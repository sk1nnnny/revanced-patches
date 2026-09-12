package app.morphe.extension.youtube.patches.components;

import static java.lang.Character.UnicodeBlock.CJK_UNIFIED_IDEOGRAPHS;
import static java.lang.Character.UnicodeBlock.HIRAGANA;
import static java.lang.Character.UnicodeBlock.KATAKANA;
import static java.lang.Character.UnicodeBlock.KHMER;
import static java.lang.Character.UnicodeBlock.LAO;
import static java.lang.Character.UnicodeBlock.MYANMAR;
import static java.lang.Character.UnicodeBlock.THAI;
import static java.lang.Character.UnicodeBlock.TIBETAN;
import static app.morphe.extension.shared.utils.StringRef.str;
import static app.morphe.extension.youtube.shared.NavigationBar.NavigationButton;

import androidx.annotation.NonNull;
import androidx.annotation.Nullable;

import java.nio.charset.StandardCharsets;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicReference;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import app.morphe.extension.shared.patches.components.Filter;
import app.morphe.extension.shared.patches.components.StringFilterGroup;
import app.morphe.extension.shared.utils.ByteTrieSearch;
import app.morphe.extension.shared.utils.Logger;
import app.morphe.extension.shared.utils.StringTrieSearch;
import app.morphe.extension.shared.utils.TrieSearch;
import app.morphe.extension.shared.utils.Utils;
import app.morphe.extension.youtube.settings.Settings;
import app.morphe.extension.youtube.shared.RootView;

/**
 * Filters feed and search results based on video title keywords and/or channel names.
 */
@SuppressWarnings({"ConstantValue", "ExtractMethodRecommender", "FieldCanBeLocal",
        "RedundantIfStatement", "StringEquality", "unchecked", "unused"})
public final class KeywordContentFilter extends Filter {

    private final Pattern COMPOSITE_RULE_PATTERN =
            Pattern.compile("^\\s*\"([^\"]+)\"\\s*(!?&|&!)\\s*\"([^\"]+)\"\\s*$");

    private final String[] STRINGS_IN_EVERY_BUFFER = {
            "googlevideo.com/initplayback?source=youtube",
            "ANDROID",
            "https://i.ytimg.com/vi/",
            "mqdefault.jpg",
            "hqdefault.jpg",
            "sddefault.jpg",
            "hq720.jpg",
            "webp",
            "_custom_",
            "OMX.ffmpeg.vp9.decoder",
            "OMX.Intel.sw_vd.vp9",
            "OMX.MTK.VIDEO.DECODER.SW.VP9",
            "OMX.google.vp9.decoder",
            "OMX.google.av1.decoder",
            "OMX.sprd.av1.decoder",
            "c2.android.av1.decoder",
            "c2.android.av1-dav1d.decoder",
            "c2.android.vp9.decoder",
            "c2.mtk.sw.vp9.decoder",
            "searchR",
            "browse-feed",
            "FEwhat_to_watch",
            "FEsubscriptions",
            "search_vwc_description_transition_key",
            "g-high-recZ",
            "expandable_metadata.",
            "thumbnail.",
            "avatar.",
            "overflow_button.",
            "shorts-lockup-image",
            "shorts-lockup.overlay-metadata.secondary-text",
            "YouTubeSans-SemiBold",
            "sans-serif"
    };

    private final StringFilterGroup startsWithFilter = new StringFilterGroup(
            null,
            "video_lockup_with_attachment.",
            "compact_video.",
            "inline_shorts",
            "shorts_video_cell",
            "shorts_pivot_item."
    );

    private final StringFilterGroup containsFilter = new StringFilterGroup(
            null,
            "modern_type_shelf_header_content.",
            "shorts_lockup_cell.",
            "video_card."
    );

    private final StringTrieSearch exceptions = new StringTrieSearch(
            "metadata.",
            "thumbnail.",
            "avatar.",
            "overflow_button."
    );

    private final int MINIMUM_KEYWORD_LENGTH = 3;
    private final float ALL_VIDEOS_FILTERED_THRESHOLD = 0.95f;
    private final float ALL_VIDEOS_FILTERED_SAMPLE_SIZE = 50;
    private final long ALL_VIDEOS_FILTERED_BACKOFF_MILLISECONDS = 60 * 1000;
    private final int UTF8_MAX_BYTE_COUNT = 4;

    private volatile float filteredVideosPercentage;
    private volatile long timeToResumeFiltering;
    private final StringFilterGroup commentsFilter;
    private final StringTrieSearch commentsFilterExceptions = new StringTrieSearch();

    private volatile String lastKeywordPhrasesParsed;
    private volatile ByteTrieSearch bufferSearch;

    private void logNavigationState(String state) {
        final boolean LOG_NAVIGATION_STATE = false;
        if (LOG_NAVIGATION_STATE) {
            Logger.printDebug(() -> "Navigation state: " + state);
        }
    }

    private String titleCaseFirstWordOnly(String sentence) {
        if (sentence.isEmpty()) return sentence;
        final int firstCodePoint = sentence.codePointAt(0);
        return new StringBuilder()
                .appendCodePoint(Character.toTitleCase(firstCodePoint))
                .append(sentence, Character.charCount(firstCodePoint), sentence.length())
                .toString();
    }

    private String capitalizeAllFirstLetters(String sentence) {
        if (sentence.isEmpty()) return sentence;
        final int delimiter = ' ';
        int[] codePoints = sentence.codePoints().toArray();
        boolean capitalizeNext = true;
        for (int i = 0, length = codePoints.length; i < length; i++) {
            final int codePoint = codePoints[i];
            if (codePoint == delimiter) {
                capitalizeNext = true;
            } else if (capitalizeNext) {
                codePoints[i] = Character.toUpperCase(codePoint);
                capitalizeNext = false;
            }
        }
        return new String(codePoints, 0, codePoints.length);
    }

    private boolean isLanguageWithNoSpaces(String text) {
        for (int i = 0, length = text.length(); i < length; ) {
            final int codePoint = text.codePointAt(i);
            Character.UnicodeBlock block = Character.UnicodeBlock.of(codePoint);
            if (block == CJK_UNIFIED_IDEOGRAPHS
                    || block == HIRAGANA
                    || block == KATAKANA
                    || block == THAI
                    || block == LAO
                    || block == MYANMAR
                    || block == KHMER
                    || block == TIBETAN) {
                return true;
            }
            i += Character.charCount(codePoint);
        }
        return false;
    }

    private boolean phrasesWillHideAllVideos(@NonNull String[] phrases, boolean matchWholeWords) {
        for (String phrase : phrases) {
            for (String commonString : STRINGS_IN_EVERY_BUFFER) {
                if (matchWholeWords) {
                    byte[] commonStringBytes = commonString.getBytes(StandardCharsets.UTF_8);
                    int matchIndex = 0;
                    while (true) {
                        matchIndex = commonString.indexOf(phrase, matchIndex);
                        if (matchIndex < 0) break;
                        if (isMatchValid(commonStringBytes, matchIndex, phrase.length(), phrase, true)) {
                            return true;
                        }
                        matchIndex++;
                    }
                } else if (Utils.containsAny(commonString, phrases)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Extracts the enclosing UTF-8 text string span from the raw Protobuf buffer.
     * Binary control characters (< 0x20) and null bytes indicate field boundaries in protobuf wire format.
     */
    @Nullable
    private String getEnclosingTextSpan(byte[] buffer, int matchStart, int matchLength) {
        int start = matchStart;
        int minStart = Math.max(0, matchStart - 1024);
        while (start > minStart) {
            byte b = buffer[start - 1];
            if (b >= 0 && b < 0x20 && b != '\t' && b != '\n' && b != '\r') {
                break;
            }
            start--;
        }

        int end = matchStart + matchLength;
        int maxLen = Math.min(buffer.length, matchStart + matchLength + 1024);
        while (end < maxLen) {
            byte b = buffer[end];
            if (b >= 0 && b < 0x20 && b != '\t' && b != '\n' && b != '\r') {
                break;
            }
            end++;
        }

        if (end <= start) return null;
        try {
            return new String(buffer, start, end - start, StandardCharsets.UTF_8);
        } catch (Exception e) {
            return null;
        }
    }

    /**
     * Checks if the enclosing text span is a technical string (URL, codec, layout ID, font, token).
     */
    private boolean isIgnoredTechnicalString(String span) {
        if (span.isEmpty()) return true;
        String s = span.toLowerCase();

        // URLs, video endpoints, domains
        if (s.startsWith("http://") || s.startsWith("https://")
                || s.contains("googlevideo.com") || s.contains(".ytimg.com")
                || s.contains("initplayback") || s.contains("youtube.com/")
                || s.contains("youtubei/v1/")) {
            return true;
        }

        // Hardware and software video codecs
        if (s.startsWith("omx.") || s.startsWith("c2.") || s.contains(".decoder")) {
            return true;
        }

        // Litho internal components, tags, UI identifiers
        if (s.startsWith("video_lockup") || s.startsWith("compact_video")
                || s.startsWith("shorts_") || s.startsWith("modern_type_shelf")
                || s.startsWith("expandable_metadata") || s.startsWith("thumbnail.")
                || s.startsWith("avatar.") || s.startsWith("overflow_button.")) {
            return true;
        }

        // Fonts
        if (s.contains("youtubesans") || s.contains("sans-serif")) {
            return true;
        }

        // URL query parameter tokens without spaces (e.g. key=val, a&b)
        if ((span.contains("=") || span.contains("&") || span.contains("?")) && !span.contains(" ")) {
            return true;
        }

        // Image files
        if (s.endsWith(".jpg") || s.endsWith(".png") || s.endsWith(".webp")) {
            return true;
        }

        return false;
    }

    /**
     * Verifies that keyword occurs as a whole word in the text span (Unicode-aware).
     */
    private boolean isValidWholeWord(String span, String keyword) {
        String spanLower = span.toLowerCase();
        String keywordLower = keyword.toLowerCase();
        int kwLen = keywordLower.length();
        int idx = 0;

        while ((idx = spanLower.indexOf(keywordLower, idx)) != -1) {
            int cpBefore = idx > 0 ? span.codePointBefore(idx) : -1;
            int nextIdx = idx + kwLen;
            int cpAfter = nextIdx < span.length() ? span.codePointAt(nextIdx) : -1;

            boolean boundaryBefore = (cpBefore == -1 || (!Character.isLetterOrDigit(cpBefore) && cpBefore != '_'));
            boolean boundaryAfter = (cpAfter == -1 || (!Character.isLetterOrDigit(cpAfter) && cpAfter != '_'));

            if (boundaryBefore && boundaryAfter) {
                return true;
            }
            idx++;
        }

        return false;
    }

    /**
     * Validates whether a match in the raw buffer is a genuine user-visible content match.
     */
    private boolean isMatchValid(byte[] buffer, int startIndex, int matchLength, String keyword, boolean isWholeWord) {
        String span = getEnclosingTextSpan(buffer, startIndex, matchLength);
        if (span == null || isIgnoredTechnicalString(span)) {
            return false;
        }

        if (!isWholeWord) {
            return span.toLowerCase().contains(keyword.toLowerCase());
        }

        return isValidWholeWord(span, keyword);
    }

    private int indexOfBytes(byte[] data, byte[] pattern, int fromIndex) {
        final int dl = data.length;
        final int pl = pattern.length;
        if (pl == 0) return -1;
        for (int i = Math.max(0, fromIndex), end = dl - pl; i <= end; i++) {
            if (data[i] != pattern[0]) continue;
            int j = 1;
            while (j < pl && data[i + j] == pattern[j]) j++;
            if (j == pl) return i;
        }
        return -1;
    }

    private boolean containsWholeWord(byte[] text, byte[] keyword) {
        int from = 0;
        final int kl = keyword.length;
        String kwStr = new String(keyword, StandardCharsets.UTF_8);
        while (true) {
            int idx = indexOfBytes(text, keyword, from);
            if (idx < 0) return false;
            if (isMatchValid(text, idx, kl, kwStr, true)) return true;
            from = idx + 1;
        }
    }

    private boolean phraseUsesAndOperator(ByteTrieSearch search, String phrase) {
        if (!Settings.HIDE_KEYWORD_CONTENT_USE_AND_OPERATOR.get()) {
            return false;
        }
        Matcher composite = COMPOSITE_RULE_PATTERN.matcher(phrase);
        if (!composite.matches()) {
            return false;
        }
        final String left = Objects.requireNonNull(composite.group(1));
        final String operator = Objects.requireNonNull(composite.group(2));
        final String right = Objects.requireNonNull(composite.group(3));

        final byte[] leftBytes = left.getBytes(StandardCharsets.UTF_8);
        final byte[] rightBytes = right.getBytes(StandardCharsets.UTF_8);
        final String compositeName = '"' + left + '"' + " " + operator + " " + '"' + right + '"';

        if (operator.indexOf('!') < 0) { // AND
            TrieSearch.TriePatternMatchedCallback<byte[]> callback =
                    (textSearched, startIndex, matchLength, callbackParameter) -> {
                        if (!isMatchValid(textSearched, startIndex, matchLength, left, true)) {
                            return false;
                        }
                        if (!containsWholeWord(textSearched, rightBytes)) {
                            return false;
                        }
                        Logger.printDebug(() -> "Matched AND keywords: " + compositeName);
                        ((MutableReference<String>) callbackParameter).value = compositeName;
                        return true;
                    };
            search.addPattern(leftBytes, callback);
            return true;
        } else { // NOT-AND
            TrieSearch.TriePatternMatchedCallback<byte[]> callback =
                    (textSearched, startIndex, matchLength, callbackParameter) -> {
                        if (!isMatchValid(textSearched, startIndex, matchLength, left, true)) {
                            return false;
                        }
                        if (containsWholeWord(textSearched, rightBytes)) {
                            return false;
                        }
                        Logger.printDebug(() -> "Matched NOT-AND keywords: " + compositeName);
                        ((MutableReference<String>) callbackParameter).value = compositeName;
                        return true;
                    };
            search.addPattern(leftBytes, callback);
            return true;
        }
    }

    private boolean phraseUsesWholeWordSyntax(String phrase) {
        return phrase.startsWith("\"") && phrase.endsWith("\"");
    }

    private String stripWholeWordSyntax(String phrase) {
        return phrase.substring(1, phrase.length() - 1);
    }

    private synchronized void parseKeywords() {
        String rawKeywords = Settings.HIDE_KEYWORD_CONTENT_PHRASES.get();

        if (rawKeywords == lastKeywordPhrasesParsed) {
            Logger.printDebug(() -> "Using previously initialized search");
            return;
        }

        ByteTrieSearch search = new ByteTrieSearch();
        String[] split = rawKeywords.split("\n");
        if (split.length != 0) {
            Map<String, Boolean> keywords = new LinkedHashMap<>(10 * split.length);

            for (String phrase : split) {
                phrase = phrase.strip();
                if (phrase.isEmpty()) continue;

                if (phraseUsesAndOperator(search, phrase)) continue;

                final boolean wholeWordMatching;
                if (phraseUsesWholeWordSyntax(phrase)) {
                    if (phrase.length() == 2) {
                        continue; // Empty ""
                    }
                    phrase = stripWholeWordSyntax(phrase);
                    wholeWordMatching = true;
                } else if (phrase.length() < MINIMUM_KEYWORD_LENGTH && !isLanguageWithNoSpaces(phrase)) {
                    Utils.showToastLong(str("revanced_hide_keyword_toast_invalid_length", phrase, MINIMUM_KEYWORD_LENGTH));
                    continue;
                } else {
                    wholeWordMatching = false;
                }

                String[] phraseVariations = {
                        phrase,
                        phrase.toLowerCase(),
                        titleCaseFirstWordOnly(phrase),
                        capitalizeAllFirstLetters(phrase),
                        phrase.toUpperCase()
                };

                if (phrasesWillHideAllVideos(phraseVariations, wholeWordMatching)) {
                    String toastMessage = (!wholeWordMatching && !phrasesWillHideAllVideos(phraseVariations, true))
                            ? "revanced_hide_keyword_toast_invalid_common_whole_word_required"
                            : "revanced_hide_keyword_toast_invalid_common";
                    Utils.showToastLong(str(toastMessage, phrase));
                    continue;
                }

                for (String variation : phraseVariations) {
                    Boolean existing = keywords.get(variation);
                    if (existing == null) {
                        keywords.put(variation, wholeWordMatching);
                    } else if (existing != wholeWordMatching) {
                        Utils.showToastLong(str("revanced_hide_keyword_toast_invalid_conflicting", phrase));
                        break;
                    }
                }
            }

            for (Map.Entry<String, Boolean> entry : keywords.entrySet()) {
                String keyword = entry.getKey();
                final boolean isWholeWord = entry.getValue();
                TrieSearch.TriePatternMatchedCallback<byte[]> callback =
                        (textSearched, startIndex, matchLength, callbackParameter) -> {
                            if (!isMatchValid(textSearched, startIndex, matchLength, keyword, isWholeWord)) {
                                return false;
                            }

                            Logger.printDebug(() -> (isWholeWord ? "Matched whole keyword: '"
                                    : "Matched keyword: '") + keyword + "'");
                            ((MutableReference<String>) callbackParameter).value = keyword;
                            return true;
                        };
                byte[] stringBytes = keyword.getBytes(StandardCharsets.UTF_8);
                search.addPattern(stringBytes, callback);
            }

            Logger.printDebug(() -> "Search using: (" + search.getEstimatedMemorySize() + " KB) keywords: " + keywords.keySet());
        }

        bufferSearch = search;
        timeToResumeFiltering = 0;
        filteredVideosPercentage = 0;
        lastKeywordPhrasesParsed = rawKeywords;
    }

    public KeywordContentFilter() {
        commentsFilterExceptions.addPatterns("engagement_toolbar");

        commentsFilter = new StringFilterGroup(
                Settings.HIDE_KEYWORD_CONTENT_COMMENTS,
                "comment_thread."
        );

        addPathCallbacks(startsWithFilter, containsFilter, commentsFilter);
    }

    private boolean hideKeywordSettingIsActive() {
        if (timeToResumeFiltering != 0) {
            if (System.currentTimeMillis() < timeToResumeFiltering) {
                return false;
            }
            timeToResumeFiltering = 0;
            filteredVideosPercentage = 0;
            Logger.printDebug(() -> "Resuming keyword filtering");
        }

        final boolean hideHome = Settings.HIDE_KEYWORD_CONTENT_HOME.get();
        final boolean hideSearch = Settings.HIDE_KEYWORD_CONTENT_SEARCH.get();
        final boolean hideSubscriptions = Settings.HIDE_KEYWORD_CONTENT_SUBSCRIPTIONS.get();

        if (!hideHome && !hideSearch && !hideSubscriptions) {
            return false;
        } else if (hideHome && hideSearch && hideSubscriptions) {
            return true;
        }

        if (RootView.isPlayerActive()) {
            return hideHome;
        }

        if (RootView.isSearchBarActive()) {
            return hideSearch;
        }

        NavigationButton selectedNavButton = NavigationButton.getSelectedNavigationButton();
        if (selectedNavButton == null) {
            return hideHome;
        }

        return switch (selectedNavButton) {
            case HOME -> hideHome;
            case SUBSCRIPTIONS -> hideSubscriptions;
            default -> false;
        };
    }

    private void updateStats(boolean videoWasHidden, @Nullable String keyword) {
        float updatedAverage = filteredVideosPercentage
                * ((ALL_VIDEOS_FILTERED_SAMPLE_SIZE - 1) / ALL_VIDEOS_FILTERED_SAMPLE_SIZE);
        if (videoWasHidden) {
            updatedAverage += 1 / ALL_VIDEOS_FILTERED_SAMPLE_SIZE;
        }

        if (updatedAverage <= ALL_VIDEOS_FILTERED_THRESHOLD) {
            filteredVideosPercentage = updatedAverage;
            return;
        }

        timeToResumeFiltering = System.currentTimeMillis() + ALL_VIDEOS_FILTERED_BACKOFF_MILLISECONDS;
        Logger.printDebug(() -> "Temporarily turning off filtering due to excessively broad filter: " + keyword);
        Utils.showToastLong(str("revanced_hide_keyword_toast_invalid_broad", keyword));
    }

    @Override
    public boolean isFiltered(String path, String identifier, String allValue, byte[] buffer,
                              StringFilterGroup matchedGroup, FilterContentType contentType, int contentIndex) {
        if (contentIndex != 0 && matchedGroup == startsWithFilter) {
            return false;
        }

        if (matchedGroup == commentsFilter && commentsFilterExceptions.matches(path)) {
            return false;
        }

        if (exceptions.matches(path)) {
            return false;
        }

        if (Settings.HIDE_KEYWORD_CONTENT_PHRASES.get() != lastKeywordPhrasesParsed) {
            parseKeywords();
        }

        if (matchedGroup != commentsFilter && !hideKeywordSettingIsActive()) {
            return false;
        }

        MutableReference<String> matchRef = new MutableReference<>();
        if (bufferSearch != null && bufferSearch.matches(buffer, matchRef)) {
            updateStats(true, matchRef.value);
            return true;
        }

        updateStats(false, null);
        return false;
    }
}

final class MutableReference<T> {
    T value;
}
