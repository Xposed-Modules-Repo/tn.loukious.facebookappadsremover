package tn.loukious.facebookappadsremover

import android.app.Activity
import android.app.Instrumentation
import android.content.Context
import android.content.ContextWrapper
import android.content.Intent
import android.os.Bundle
import android.os.Handler
import android.os.Message
import android.os.Messenger
import android.util.Log as AndroidLog
import android.view.View
import android.view.ViewGroup
import android.webkit.JavascriptInterface
import android.webkit.ValueCallback
import android.webkit.WebView
import android.widget.TextView
import de.robv.android.xposed.XC_MethodHook
import de.robv.android.xposed.XposedBridge
import org.luckypray.dexkit.DexKitBridge
import org.luckypray.dexkit.query.enums.MatchType
import org.luckypray.dexkit.query.enums.StringMatchType
import org.luckypray.dexkit.result.ClassData
import org.luckypray.dexkit.result.MethodData
import org.json.JSONArray
import org.json.JSONObject
import java.lang.reflect.Field
import java.lang.reflect.Method
import java.lang.reflect.Modifier
import java.io.File
import java.net.URLDecoder
import java.net.URLEncoder
import java.util.Collections
import java.util.Properties
import java.util.ArrayDeque
import java.util.IdentityHashMap
import java.util.LinkedHashMap
import java.util.Optional
import java.util.WeakHashMap
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong

const val TAG = "FacebookAppAdsRemover"

private const val HOST_PACKAGE = "com.facebook.katana"
private const val BEFORE_SIZE_EXTRA = "facebook_ads_before_size"
private const val BUILD_MARKER = "structural_component_guard_v2_2026_09_14"
private const val ENABLE_UPSTREAM_REELS_AD_HOOKS = true
private const val ENABLE_FEED_CSR_FILTER_HOOKS = true
private const val ENABLE_LATE_FEED_LIST_HOOKS = true
private const val ENABLE_STORY_POOL_ADD_HOOKS = true
private const val ENABLE_FEED_SPONSORED_POOL_HOOKS = true
private const val ENABLE_FEED_UI_MARKER_FALLBACKS = false
private const val ENABLE_GAME_AD_AUTOFIX = true
private const val ENABLE_GAME_AD_DIAGNOSTICS = true
private const val ENABLE_BROAD_HANDLER_GAME_AD_DIAGNOSTICS = false
private const val ENABLE_AUDIENCE_NETWORK_VIEW_DIAGNOSTICS = false
private const val ENABLE_AUDIENCE_NETWORK_REWARD_FALLBACKS = true
private const val GAME_AD_DIAG_LOG_LIMIT = 8_000
private const val GAME_AD_DIAG_TEXT_LIMIT = 1_200
private const val GAME_AD_DIAG_FLOW_WINDOW_MS = 2 * 60_000L
private const val AUDIENCE_NETWORK_STATE_DUMP_LIMIT = 120
private const val GRAPHQL_FEED_UNIT_EDGE_CLASS = "com.facebook.graphql.model.GraphQLFeedUnitEdge"
private const val GRAPHQL_MULTI_ADS_FEED_UNIT_CLASS = "com.facebook.graphql.model.GraphQLFBMultiAdsFeedUnit"
private const val GRAPHQL_QUICK_PROMO_FEED_UNIT_CLASS =
    "com.facebook.graphql.model.GraphQLQuickPromotionNativeTemplateFeedUnit"
private const val AUDIENCE_NETWORK_ACTIVITY_CLASS = "com.facebook.ads.AudienceNetworkActivity"
private const val AUDIENCE_NETWORK_REMOTE_ACTIVITY_CLASS = "com.facebook.ads.internal.ipc.AudienceNetworkRemoteActivity"
private const val NEKO_PLAYABLE_ACTIVITY_CLASS = "com.facebook.neko.playables.activity.NekoPlayableAdActivity"
private const val GAME_AD_REJECTION_MESSAGE = "Game ad request blocked"
private const val GAME_AD_REJECTION_CODE = "CLIENT_UNSUPPORTED_OPERATION"
private const val GAME_AD_UNAVAILABLE_MESSAGE = "Rewarded ad unavailable"
private const val GAME_AD_UNAVAILABLE_CODE = "ADS_UNAVAILABLE"
private const val GAME_AD_SUCCESS_INSTANCE_PREFIX = "facebook_app_ads_remover_noop_ad"
private const val GAME_AD_RECENT_WINDOW_MS = 30_000L
private const val GAME_AD_PROMISE_WINDOW_MS = 10 * 60_000L
private const val AUDIENCE_NETWORK_REWARD_CLOSE_RETRY_WINDOW_MS = 35_000L
private const val HOOK_HIT_LOG_EVERY = 25

private const val GAME_AD_WEBVIEW_HIDE_SCRIPT = """
(function(){
  if (window.__fbAppAdsRemoverBannerSweep) return;
  window.__fbAppAdsRemoverBannerSweep = true;
  function textOf(el) {
    try { return (el.innerText || el.textContent || '').toLowerCase(); } catch (e) { return ''; }
  }
  function attrsOf(el) {
    try { return ((el.id || '') + ' ' + (el.className || '') + ' ' + (el.getAttribute('aria-label') || '') + ' ' + (el.getAttribute('src') || '')).toLowerCase(); } catch (e) { return ''; }
  }
  function nearBottom(el) {
    try {
      var r = el.getBoundingClientRect();
      return r.height > 0 && r.height < Math.max(260, window.innerHeight * 0.35) && r.bottom > window.innerHeight * 0.55;
    } catch (e) { return false; }
  }
  function isAd(el) {
    var t = textOf(el);
    var a = attrsOf(el);
    if (t.indexOf('ads served by meta') >= 0 || t.indexOf('ad choices') >= 0) return true;
    if (!nearBottom(el)) return false;
    if ((el.tagName || '').toLowerCase() === 'iframe') return true;
    return /audiencenetwork|adchoices|fbinstant.*ad|instant.*ad|banner.?ad|ad.?banner|ad-container|ad_container|sponsored/.test(a);
  }
  function hide(el) {
    try {
      var target = el;
      for (var i = 0; i < 4 && target.parentElement && nearBottom(target.parentElement); i++) target = target.parentElement;
      target.style.setProperty('display', 'none', 'important');
      target.style.setProperty('visibility', 'hidden', 'important');
      target.style.setProperty('height', '0px', 'important');
      target.style.setProperty('min-height', '0px', 'important');
      target.style.setProperty('pointer-events', 'none', 'important');
    } catch (e) {}
  }
  function sweep() {
    try {
      document.querySelectorAll('iframe, div, section, aside, [id], [class], [aria-label]').forEach(function(el) {
        if (isAd(el)) hide(el);
      });
    } catch (e) {}
  }
  sweep();
  new MutationObserver(sweep).observe(document.documentElement || document.body, {childList:true, subtree:true, attributes:true});
  setInterval(sweep, 1000);
})();
"""

private val GAME_AD_MESSAGE_TYPES = setOf(
    "getinterstitialadasync",
    "getrewardedvideoasync",
    "getrewardedinterstitialasync",
    "loadadasync",
    "showadasync",
    "loadbanneradasync",
    "hidebanneradasync"
)

// Rewarded requests are resolved as success instead of "unavailable" so the
// game grants the reward without showing an ad.
private val GAME_AD_AUTOFIX_MESSAGE_TYPES = setOf(
    "getrewardedvideoasync",
    "getrewardedinterstitialasync",
    "loadbanneradasync",
    "hidebanneradasync"
)

private val GAME_AD_REWARD_MESSAGE_TYPES = setOf(
    "getrewardedvideoasync",
    "getrewardedinterstitialasync"
)

private val GAME_AD_ACTIVITY_CLASS_NAMES = setOf(
    AUDIENCE_NETWORK_ACTIVITY_CLASS,
    AUDIENCE_NETWORK_REMOTE_ACTIVITY_CLASS,
    NEKO_PLAYABLE_ACTIVITY_CLASS
)

private val HARD_BLOCKED_GAME_AD_ACTIVITY_CLASS_NAMES = setOf(
    NEKO_PLAYABLE_ACTIVITY_CLASS
)

private val AUDIENCE_NETWORK_REWARD_COMPLETION_METHOD_NAMES = setOf(
    "onRewardedVideoCompleted",
    "onRewardedAdCompleted",
    "onRewardedInterstitialCompleted",
    "onAdComplete",
    "onAdCompleted"
)

private val gameAdInstanceIds = ConcurrentHashMap<String, String>()
private val gameAdInstanceTypes = ConcurrentHashMap<String, String>()
private val gameAdPromiseSnapshots = ConcurrentHashMap<String, GameAdPromiseSnapshot>()
private val recentGameAdTargets = Collections.synchronizedMap(WeakHashMap<Any, Long>())
private val recentGameAdPayloads = Collections.synchronizedList(ArrayList<GameAdPayloadSnapshot>())
private val hookHitCounters = ConcurrentHashMap<String, AtomicInteger>()
private val gameAdSurfaceHooksInstalled = AtomicInteger(0)
private val gameAdActivityLifecycleHookInstalled = AtomicBoolean(false)
private val gameAdResultHookedClasses = ConcurrentHashMap.newKeySet<String>()
private val gameAdServiceDispatchHookedClasses = ConcurrentHashMap.newKeySet<String>()
private val gameAdSystemDiagnosticsInstalled = AtomicInteger(0)
private val gameAdDynamicDiagnosticsInstalled = AtomicInteger(0)
private val audienceNetworkViewDiagnosticsInstalled = AtomicInteger(0)
private val audienceNetworkRewardHooksInstalled = AtomicInteger(0)
private val lastGameAdActivityCloseMs = AtomicLong(0L)
private val lastUnavailableGameAdMs = AtomicLong(0L)
private val lastGameAdDiagnosticFlowMs = AtomicLong(0L)
private val gameAdDiagnosticLogCount = AtomicInteger(0)
private val scheduledGameAdActivityCloses = Collections.synchronizedMap(WeakHashMap<Activity, Long>())
private val audienceNetworkRewardClassesHooked = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val audienceNetworkRewardAdListeners = Collections.synchronizedMap(WeakHashMap<Any, Any>())
private val gameAdDiagnosticClassesHooked = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val gameAdDiagnosticClassesLogged = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val audienceNetworkViewListenerClassesHooked = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val audienceNetworkActivityStateDumps = Collections.synchronizedMap(WeakHashMap<Activity, Long>())
private val storyAdProviderClassesHooked = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val feedCsrMethodsHooked = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val lateFeedMethodsHooked = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val sponsoredPoolMethodsHooked = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val feedComponentMethodsHooked = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val feedComponentCandidates = ConcurrentHashMap<String, Class<*>>()
private val feedWrapperCandidates = ConcurrentHashMap<String, Class<*>>()
private val feedGuardResolvedComponentNames = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val feedGuardResolvedWrapperNames = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())
private val visibleAdTraceInstalled = AtomicInteger(0)
private val visibleAdViewsTraced = ConcurrentHashMap<Int, Boolean>()
private val survivingFeedAdTraceCount = AtomicInteger(0)
private val survivingFeedTypeContractsLogged = AtomicInteger(0)

private data class GameAdPayloadSnapshot(
    val target: Any,
    val payload: JSONObject,
    val messageType: String?,
    val timestampMs: Long
)

private data class GameAdPromiseSnapshot(
    val payload: JSONObject,
    val messageType: String?,
    val timestampMs: Long
)

private data class AudienceNetworkGraphNode(
    val value: Any,
    val path: String,
    val depth: Int
)

private val GAME_AD_METHOD_TAGS = listOf(
    "Invalid JSON content received by onGetInterstitialAdAsync: ",
    "Invalid JSON content received by onGetRewardedInterstitialAsync: ",
    "Invalid JSON content received by onRewardedVideoAsync: ",
    "Invalid JSON content received by onLoadAdAsync: ",
    "Invalid JSON content received by onShowAdAsync: "
)

private val FEED_AD_CATEGORY_VALUES = setOf(
    "SPONSORED",
    "PROMOTION",
    "ENGAGEMENT_QP",
    "AD",
    "ADVERTISEMENT",
    "BANNER"
)

private val FEED_COLLECTION_AD_CATEGORY_VALUES = setOf(
    "SPONSORED",
    "PROMOTION",
    "AD",
    "ADVERTISEMENT",
    "BANNER"
)

private val FEED_SAFE_CONTAINER_CATEGORY_VALUES = setOf(
    "FB_SHORTS",
    "MULTI_FB_STORIES_TRAY"
)

private val FEED_AD_SIGNAL_TOKENS = listOf(
    "sponsored",
    "promotion",
    "multiads",
    "quickpromotion",
    "reels_banner_ad",
    "reelsbannerads",
    "reels_post_loop_deferred_card",
    "deferred_card",
    "adbreakdeferredcta",
    "instreamadidlewithbannerstate",
    "instream_legacy_banner_ad",
    "unified_player_banner_ad",
    "banner_ad_",
    "floatingcta"
)

// Selectors must identify the story ad *store* itself. The telemetry labels
// "ads_insertion"/"ads_deletion" are logged by unrelated story viewer classes too
// (e.g. the viewer's onDataChanged handler), and hooking those blanks the viewer.
private val STORY_AD_PROVIDER_TAGS = listOf(
    "AdsPaginatingNetworkAdBucketFetcher",
    "FbStoryAdInDiscStoreImpl",
    "IN_DISC_METADATA_KEY",
    "AD_BUCKETS_KEY",
    "StoryAdsInDisc"
)

private data class NamedHookTarget(
    val className: String,
    val methodName: String
)

// Litho generated component classes pass a stable spec name to their base class
// constructor ("NewsFeedFeedUnitComponent" for the feed unit component,
// "LoggingComponent" for the generic wrapper Litho renders feed units through).
// Those names survive Facebook's obfuscator; the X.* class names change every
// build, so the component guard discovers its targets from these names instead.
const val FEED_UNIT_COMPONENT_NAME = "NewsFeedFeedUnitComponent"
const val FEED_WRAPPER_COMPONENT_NAME = "LoggingComponent"

// Litho layout entry points are matched by shape; the render parameter count
// has varied between builds (1 on 576), so later counts are only fallbacks.
private val FEED_RENDER_PARAMETER_COUNTS = listOf(1, 2)

private fun survivingFeedTypeClassNames(): List<String> {
    return (feedComponentCandidates.keys + feedWrapperCandidates.keys + GRAPHQL_FEED_UNIT_EDGE_CLASS).toList()
}

private val FEED_SURFACE_AD_MARKER_TOKENS = listOf(
    "hide ad",
    "ad\u2022",
    "sponsored",
    "promoted",
    "ad choices",
    "adchoices"
)

private val EXPLICIT_FEED_CARD_AD_MARKER_TOKENS = listOf(
    "hide ad",
    "ad\u2022",
    "ad choices",
    "adchoices"
)

private val EXPLICIT_FEED_AD_CTA_TOKENS = listOf(
    "apply now",
    "send message",
    "learn more",
    "shop now",
    "contact us",
    "get quote",
    "book now",
    "call now",
    "sign up",
    "download"
)

private val FEED_REEL_CTA_AD_MARKER_TOKENS = listOf(
    "shared link:",
    "send message",
    "your business",
    "your ad"
)

// Tagged-product sticker pills overlaid on organic reels compose their
// accessibility label as "<creator> - <product>, <CTA>" (e.g.
// "Zack D. Films - Hat (Denim), Shop now"). Requiring the full composite
// shape keeps plain "Shop now" buttons on other surfaces untouched.
private val REELS_SHOPPING_STICKER_CTA_TOKENS = listOf(
    "shop now",
    "buy now",
    "order now"
)

private val REELS_AD_SIGNAL_TOKENS = listOf(
    "sponsored",
    "promotion",
    "multiads",
    "quickpromotion",
    "reels_banner_ad",
    "reelsbannerads",
    "adbreakdeferredcta",
    "instreamadidlewithbannerstate",
    "instream_legacy_banner_ad",
    "unified_player_banner_ad",
    "banner_ad_"
)

private object Log {
    fun i(tag: String, msg: String): Int = if (BuildConfig.DEBUG) AndroidLog.i(tag, msg) else 0

    fun w(tag: String, msg: String): Int = if (BuildConfig.DEBUG) AndroidLog.w(tag, msg) else 0

    fun w(tag: String, msg: String, throwable: Throwable): Int =
        if (BuildConfig.DEBUG) AndroidLog.w(tag, msg, throwable) else 0

    fun e(tag: String, msg: String): Int = if (BuildConfig.DEBUG) AndroidLog.e(tag, msg) else 0

    fun e(tag: String, msg: String, throwable: Throwable): Int =
        if (BuildConfig.DEBUG) AndroidLog.e(tag, msg, throwable) else 0

    fun missing(tag: String, hookName: String): Int =
        AndroidLog.w(tag, "Hook target not found: $hookName")

    fun resolutionFailure(tag: String, msg: String, throwable: Throwable): Int {
        return if (BuildConfig.DEBUG || throwable.message?.contains("Unable to resolve") == true) {
            AndroidLog.e(tag, msg, throwable)
        } else {
            0
        }
    }
}

private data class FeedListSanitizerHook(
    val method: Method,
    val listArgIndex: Int
)

private data class FeedCsrFilterHook(
    val method: Method,
    val listArgIndex: Int
)

private data class StoryAdProviderHooks(
    val providerClass: Class<*>,
    val mergeMethod: Method?,
    val fetchMoreAdsMethod: Method?,
    val deferredUpdateMethod: Method?,
    val insertionTriggerMethod: Method?
)

private data class ResolvedHooks(
    val adKindEnumClass: Class<*>?,
    val listBuilderAppendMethod: Method?,
    val listBuilderFactoryMethod: Method?,
    val pluginPackBuildMethods: List<Method>,
    val instreamBannerEligibilityMethod: Method?,
    val indicatorPillAdEligibilityMethod: Method?,
    val reelsBannerRenderMethods: List<Method>,
    val feedCsrFilterHooks: List<FeedCsrFilterHook>,
    val lateFeedListHooks: List<FeedListSanitizerHook>,
    val storyPoolAddMethods: List<Method>,
    val sponsoredPoolClass: Class<*>?,
    val sponsoredPoolAddMethod: Method?,
    val sponsoredStoryManagerClass: Class<*>?,
    val sponsoredStoryNextMethod: Method?,
    val storyAdProviders: List<StoryAdProviderHooks>,
    val gameAdRequestMethods: List<Method>,
    val gameAdBridgePostMessageMethod: Method?,
    val playableAdActivityOnCreate: Method?,
    val gameAdUiActivityMethods: List<Method>
)

private class AdStoryInspector(
    private val adKindEnumClass: Class<*>
) {
    private val enumMethodCache = ConcurrentHashMap<Class<*>, List<Method>>()
    private val fieldCache = ConcurrentHashMap<Class<*>, List<Field>>()

    fun containsAdStory(
        value: Any?,
        depth: Int = 0,
        seen: IdentityHashMap<Any, Boolean> = IdentityHashMap()
    ): Boolean {
        return containsAdKind(value, depth, seen) &&
            containsReelsAdSignal(value, 0, IdentityHashMap())
    }

    private fun containsAdKind(
        value: Any?,
        depth: Int = 0,
        seen: IdentityHashMap<Any, Boolean> = IdentityHashMap()
    ): Boolean {
        if (value == null || depth > 4) return false
        if (isAdKind(value)) return true

        val type = value.javaClass
        if (type.isPrimitive || value is String || value is Number || value is Boolean || value is CharSequence) {
            return false
        }
        if (seen.put(value, true) != null) return false

        if (value is Iterable<*>) {
            var checked = 0
            for (item in value) {
                if (containsAdKind(item, depth + 1, seen)) return true
                checked++
                if (checked >= 8) break
            }
        }

        if (type.isArray) {
            val array = value as? Array<*>
            if (array != null) {
                var checked = 0
                for (item in array) {
                    if (containsAdKind(item, depth + 1, seen)) return true
                    checked++
                    if (checked >= 8) break
                }
            }
        }

        for (method in enumMethodsFor(type)) {
            val marker = runCatching { method.invoke(value) }.getOrNull()
            if (isAdKind(marker)) return true
        }

        for (field in fieldsFor(type)) {
            val fieldValue = runCatching { field.get(value) }.getOrNull()
            if (containsAdKind(fieldValue, depth + 1, seen)) return true
        }

        return false
    }

    private fun containsReelsAdSignal(
        value: Any?,
        depth: Int,
        seen: IdentityHashMap<Any, Boolean>
    ): Boolean {
        if (value == null || depth > 4) return false

        if (value is CharSequence) {
            return isReelsAdSignalText(value.toString())
        }

        val type = value.javaClass
        if (isReelsAdSignalText(type.name)) return true

        if (type.isEnum) {
            return isReelsAdSignalText(value.toString())
        }

        if (type.isPrimitive || value is Number || value is Boolean) {
            return false
        }

        if (seen.put(value, true) != null) return false

        if (value is Iterable<*>) {
            var checked = 0
            for (item in value) {
                if (containsReelsAdSignal(item, depth + 1, seen)) return true
                checked++
                if (checked >= 8) break
            }
        }

        if (type.isArray) {
            val array = value as? Array<*>
            if (array != null) {
                var checked = 0
                for (item in array) {
                    if (containsReelsAdSignal(item, depth + 1, seen)) return true
                    checked++
                    if (checked >= 8) break
                }
            }
        }

        if (isReelsAdSignalText(runCatching { value.toString() }.getOrNull())) return true

        for (method in stringMethodsFor(type)) {
            val marker = runCatching { method.invoke(value) as? String }.getOrNull()
            if (isReelsAdSignalText(marker)) return true
        }

        for (field in fieldsFor(type)) {
            val fieldValue = runCatching { field.get(value) }.getOrNull()
            if (containsReelsAdSignal(fieldValue, depth + 1, seen)) return true
        }

        return false
    }

    private fun isAdKind(value: Any?): Boolean {
        return value != null && value.javaClass == adKindEnumClass && value.toString() == "AD"
    }

    private fun enumMethodsFor(type: Class<*>): List<Method> {
        return enumMethodCache.getOrPut(type) {
            val methods = LinkedHashMap<String, Method>()
            var current: Class<*>? = type
            while (current != null && current != Any::class.java) {
                current.declaredMethods.forEach { method ->
                    if (!Modifier.isStatic(method.modifiers) &&
                        method.parameterCount == 0 &&
                        method.returnType == adKindEnumClass
                    ) {
                        method.isAccessible = true
                        methods.putIfAbsent("${current.name}#${method.name}", method)
                    }
                }
                current = current.superclass
            }
            methods.values.toList()
        }
    }

    private fun fieldsFor(type: Class<*>): List<Field> {
        return fieldCache.getOrPut(type) {
            val fields = ArrayList<Field>()
            var current: Class<*>? = type
            while (current != null && current != Any::class.java && fields.size < 24) {
                current.declaredFields.forEach { field ->
                    if (!Modifier.isStatic(field.modifiers) && fields.size < 24) {
                        field.isAccessible = true
                        fields.add(field)
                    }
                }
                current = current.superclass
            }
            fields
        }
    }

    private fun stringMethodsFor(type: Class<*>): List<Method> {
        return allMethodsFor(type)
            .asSequence()
            .filter { method ->
                method.parameterCount == 0 &&
                    method.returnType == String::class.java &&
                    method.name != "toString"
            }
            .take(12)
            .onEach { method -> method.isAccessible = true }
            .toList()
    }

    private fun allMethodsFor(type: Class<*>): List<Method> {
        val methods = LinkedHashMap<String, Method>()
        var current: Class<*>? = type
        while (current != null && current != Any::class.java) {
            current.declaredMethods.forEach { method ->
                if (!Modifier.isStatic(method.modifiers)) {
                    method.isAccessible = true
                    methods.putIfAbsent("${current.name}#${method.name}/${method.parameterCount}", method)
                }
            }
            current = current.superclass
        }
        return methods.values.toList()
    }

    private fun isReelsAdSignalText(value: String?): Boolean {
        if (value.isNullOrBlank()) return false
        val normalized = value.lowercase()
        return REELS_AD_SIGNAL_TOKENS.any { token -> normalized.contains(token) }
    }
}

private class FeedItemInspector(
    itemContractTypes: Collection<Class<*>>
) {
    private val itemModelAccessor =
        resolveItemModelAccessor(itemContractTypes)
    private val itemEdgeAccessor =
        resolveItemEdgeAccessor(itemContractTypes)
    private val itemNetworkAccessor =
        resolveItemNetworkAccessor(itemContractTypes)
    private val categoryMethodCache = ConcurrentHashMap<Class<*>, Method>()
    private val edgeAccessorCache = ConcurrentHashMap<Class<*>, Method>()
    private val edgeCategoryAccessorCache = ConcurrentHashMap<Class<*>, Method>()
    private val feedUnitAccessorCache = ConcurrentHashMap<Class<*>, Method>()
    private val backendDataAccessorCache = ConcurrentHashMap<Class<*>, Method>()
    private val typeNameMethodCache = ConcurrentHashMap<Class<*>, Method>()
    private val stringAccessorCache = ConcurrentHashMap<Class<*>, List<Method>>()
    private val stringFieldCache = ConcurrentHashMap<Class<*>, List<Field>>()

    private data class FeedItemFacts(
        val modelCategory: String?,
        val edgeCategory: String?,
        val network: Boolean?,
        val inflatedUnitClass: String?,
        val inflatedTypeName: String?,
        val backendUnitClass: String?,
        val backendTypeName: String?
    )

    fun isSponsoredFeedItem(value: Any?): Boolean {
        if (isDefinitelySponsoredFeedItem(value)) {
            return true
        }

        val model = invokeNoThrow(itemModelAccessor, value)
        val edge = edgeFrom(value)
        val feedUnit = feedUnitFrom(edge)
        val backendData = backendDataFrom(edge)

        if (containsKnownAdSignals(value)) return true
        if (containsKnownAdSignals(model)) return true
        if (containsKnownAdSignals(edge)) return true
        if (containsKnownAdSignals(feedUnit)) return true
        if (containsKnownAdSignals(backendData)) return true

        return false
    }

    fun isDefinitelySponsoredFeedItem(value: Any?): Boolean {
        if (value == null) return false

        val model = invokeNoThrow(itemModelAccessor, value)
        val modelCategory = readCategory(model)
        if (isSafeFeedContainerCategory(modelCategory)) {
            return false
        }
        if (isSponsoredFeedCategory(modelCategory)) {
            return true
        }

        val edge = edgeFrom(value)
        val edgeCategory = readEdgeCategory(edge) ?: readCategory(edge)
        if (isSafeFeedContainerCategory(edgeCategory)) {
            return false
        }
        if (isSponsoredFeedCategory(edgeCategory)) {
            return true
        }

        val feedUnit = feedUnitFrom(edge)
        val backendData = backendDataFrom(edge)
        val inflatedUnitClassName = feedUnit?.javaClass?.name
        val backendUnitClassName = backendData?.javaClass?.name
        if (
            inflatedUnitClassName == GRAPHQL_MULTI_ADS_FEED_UNIT_CLASS ||
            inflatedUnitClassName == GRAPHQL_QUICK_PROMO_FEED_UNIT_CLASS
        ) {
            return true
        }

        val typeName = readTypeName(feedUnit) ?: readTypeName(backendData)
        if (
            isLikelyAdTypeName(typeName) ||
            isAdSignalText(inflatedUnitClassName) ||
            isAdSignalText(backendUnitClassName)
        ) {
            return true
        }

        return false
    }

    fun isExplicitlySponsoredFeedEdge(value: Any?): Boolean {
        val edge = edgeFrom(value) ?: return false
        val edgeCategory = readEdgeCategory(edge) ?: readCategory(edge)
        return edgeCategory != null && edgeCategory in FEED_COLLECTION_AD_CATEGORY_VALUES
    }

    fun storyPoolBlockReason(value: Any?): String? {
        return if (isDefinitelySponsoredFeedItem(value)) "strict" else null
    }

    fun describe(item: Any?): String {
        if (item == null) return "null"

        val facts = factsFor(item)
        val modelCategory = facts.modelCategory ?: "unknown"
        val edgeCategory = facts.edgeCategory ?: "unknown"
        val network = facts.network?.toString() ?: "unknown"
        val inflatedUnitClass = facts.inflatedUnitClass ?: "null"
        val inflatedTypeName = facts.inflatedTypeName ?: "unknown"
        val backendUnitClass = facts.backendUnitClass ?: "null"
        val backendTypeName = facts.backendTypeName ?: "unknown"

        return "modelCat=$modelCategory edgeCat=$edgeCategory isAd=${isSponsoredFeedItem(item)} network=$network wrapper=${item.javaClass.name} inflated=$inflatedUnitClass/$inflatedTypeName backend=$backendUnitClass/$backendTypeName"
    }

    private fun factsFor(item: Any?): FeedItemFacts {
        val model = invokeNoThrow(itemModelAccessor, item)
        val edge = edgeFrom(item)
        val feedUnit = feedUnitFrom(edge)
        val backendData = backendDataFrom(edge)
        return FeedItemFacts(
            modelCategory = readCategory(model),
            edgeCategory = readEdgeCategory(edge) ?: readCategory(edge),
            network = invokeNoThrow(itemNetworkAccessor, item) as? Boolean,
            inflatedUnitClass = feedUnit?.javaClass?.name,
            inflatedTypeName = readTypeName(feedUnit),
            backendUnitClass = backendData?.javaClass?.name,
            backendTypeName = readTypeName(backendData)
        )
    }

    private fun edgeFrom(value: Any?): Any? {
        if (value == null) return null
        if (value.javaClass.name == GRAPHQL_FEED_UNIT_EDGE_CLASS) return value

        invokeNoThrow(itemEdgeAccessor, value)?.let { directEdge ->
            if (directEdge.javaClass.name == GRAPHQL_FEED_UNIT_EDGE_CLASS) {
                return directEdge
            }
        }

        val fallback = cachedMethod(edgeAccessorCache, value.javaClass) {
            resolveChildAccessor(value) { candidateValue ->
                candidateValue != null && candidateValue.javaClass.name == GRAPHQL_FEED_UNIT_EDGE_CLASS
            }
        }
        return invokeNoThrow(fallback, value)
    }

    private fun feedUnitFrom(edge: Any?): Any? {
        if (edge == null) return null

        val accessor = cachedMethod(feedUnitAccessorCache, edge.javaClass) {
            resolveChildAccessor(edge) { candidateValue ->
                    val className = candidateValue?.javaClass?.name
                    className == GRAPHQL_MULTI_ADS_FEED_UNIT_CLASS ||
                        className == GRAPHQL_QUICK_PROMO_FEED_UNIT_CLASS ||
                        readTypeName(candidateValue)?.let { it != "FeedUnitEdge" && it != "FeedBackendData" } == true
                }
        }
        return invokeNoThrow(accessor, edge)
    }

    private fun backendDataFrom(edge: Any?): Any? {
        if (edge == null) return null

        val accessor = cachedMethod(backendDataAccessorCache, edge.javaClass) {
            resolveChildAccessor(edge) { candidateValue ->
                    readTypeName(candidateValue) == "FeedBackendData"
                }
        }
        return invokeNoThrow(accessor, edge)
    }

    private fun readEdgeCategory(value: Any?): String? {
        if (value == null) return null

        val accessor = cachedMethod(edgeCategoryAccessorCache, value.javaClass) {
            allInstanceMethods(value.javaClass).firstOrNull { candidate ->
                    candidate.parameterCount == 0 &&
                        candidate.returnType.isEnum &&
                        candidate.returnType.enumConstants?.any {
                            val name = it.toString()
                            name == "SPONSORED" || name == "PROMOTION"
                        } == true
                }?.apply { isAccessible = true }
        }
        return invokeNoThrow(accessor, value)?.toString()
    }

    private fun resolveNamedNoArgAccessor(type: Class<*>, methodName: String): Method? {
        return allInstanceMethods(type).firstOrNull { candidate ->
            candidate.parameterCount == 0 && candidate.name == methodName
        }?.apply { isAccessible = true }
    }

    fun describeAccessors(): String {
        return "model=${accessorName(itemModelAccessor)} edge=${accessorName(itemEdgeAccessor)} network=${accessorName(itemNetworkAccessor)}"
    }

    private fun accessorName(method: Method?): String {
        return method?.let { "${it.declaringClass.name}.${it.name}" } ?: "unresolved"
    }

    private fun readCategory(value: Any?): String? {
        if (value == null) return null

        if (value.javaClass.isEnum) {
            return value.toString()
        }

        val accessor = cachedMethod(categoryMethodCache, value.javaClass) {
            allInstanceMethods(value.javaClass).firstOrNull { candidate ->
                candidate.parameterCount == 0 &&
                    candidate.returnType.isEnum &&
                    candidate.returnType.enumConstants?.any {
                        val name = it.toString()
                        name == "SPONSORED" || name == "PROMOTION"
                    } == true
            }?.apply { isAccessible = true }
        }
        return invokeNoThrow(accessor, value)?.toString()
    }

    private fun readTypeName(value: Any?): String? {
        if (value == null) return null

        val accessor = cachedMethod(typeNameMethodCache, value.javaClass) {
            resolveNamedNoArgAccessor(value.javaClass, "getTypeName")
                ?: allInstanceMethods(value.javaClass).firstOrNull { candidate ->
                    candidate.parameterCount == 0 &&
                        candidate.returnType == String::class.java &&
                        candidate.name == "getTypeName"
                }?.apply { isAccessible = true }
        }
        return invokeNoThrow(accessor, value) as? String
    }

    private fun cachedMethod(
        cache: ConcurrentHashMap<Class<*>, Method>,
        type: Class<*>,
        resolver: () -> Method?
    ): Method? {
        cache[type]?.let { return it }
        val resolved = resolver() ?: return null
        return cache.putIfAbsent(type, resolved) ?: resolved
    }

    private fun resolveItemModelAccessor(itemContractTypes: Collection<Class<*>>): Method? {
        return itemContractTypes
            .asSequence()
            .flatMap { type -> allInstanceMethods(type).asSequence() }
            .firstOrNull { candidate ->
                candidate.parameterCount == 0 &&
                    candidate.name != "clone" &&
                    !candidate.returnType.isPrimitive &&
                    candidate.returnType != Any::class.java &&
                    candidate.returnType != String::class.java &&
                    !candidate.returnType.isEnum
            }?.apply { isAccessible = true }
    }

    private fun resolveItemEdgeAccessor(itemContractTypes: Collection<Class<*>>): Method? {
        return itemContractTypes
            .asSequence()
            .flatMap { type -> allInstanceMethods(type).asSequence() }
            .firstOrNull { candidate ->
                candidate.parameterCount == 0 &&
                    candidate.name != "clone" &&
                    (candidate.returnType == Any::class.java || candidate.returnType.name == GRAPHQL_FEED_UNIT_EDGE_CLASS)
            }?.apply { isAccessible = true }
    }

    private fun resolveItemNetworkAccessor(itemContractTypes: Collection<Class<*>>): Method? {
        return itemContractTypes
            .asSequence()
            .flatMap { type -> allInstanceMethods(type).asSequence() }
            .firstOrNull { candidate ->
                candidate.parameterCount == 0 &&
                    candidate.returnType == Boolean::class.javaPrimitiveType
            }?.apply { isAccessible = true }
    }

    private fun resolveChildAccessor(target: Any, acceptsValue: (Any?) -> Boolean): Method? {
        return allInstanceMethods(target.javaClass)
            .asSequence()
            .filter { candidate ->
                candidate.parameterCount == 0 &&
                    !candidate.returnType.isPrimitive &&
                    candidate.returnType != Void.TYPE &&
                    candidate.returnType != String::class.java &&
                    !candidate.returnType.isEnum &&
                    candidate.declaringClass != Any::class.java
            }
            .sortedByDescending { candidate -> scoreChildAccessor(candidate.returnType) }
            .firstOrNull { candidate ->
                acceptsValue(invokeNoThrow(candidate.apply { isAccessible = true }, target))
            }
    }

    private fun scoreChildAccessor(type: Class<*>): Int {
        return when {
            type.name == GRAPHQL_FEED_UNIT_EDGE_CLASS -> 4
            type.name.startsWith("com.facebook.graphql.model.") -> 3
            type.name.startsWith("com.facebook.") -> 2
            !type.name.startsWith("java.") &&
                !type.name.startsWith("javax.") &&
                !type.name.startsWith("android.") &&
                !type.name.startsWith("kotlin.") -> 1
            else -> 0
        }
    }

    private fun isSponsoredFeedCategory(value: String?): Boolean {
        return value != null && value in FEED_AD_CATEGORY_VALUES
    }

    private fun isSafeFeedContainerCategory(value: String?): Boolean {
        return value != null && value in FEED_SAFE_CONTAINER_CATEGORY_VALUES
    }

    private fun isLikelyAdTypeName(value: String?): Boolean {
        if (value == null) return false
        if (value.contains("QuickPromotion", ignoreCase = true)) return true
        return isAdSignalText(value)
    }

    private fun containsKnownAdSignals(value: Any?): Boolean {
        if (value == null) return false

        if (value is CharSequence) {
            return isAdSignalText(value.toString())
        }

        val type = value.javaClass
        if (isAdSignalText(type.name)) return true

        if (type.isEnum) {
            return isAdSignalText(value.toString())
        }

        if (type.isPrimitive || value is Number || value is Boolean) {
            return false
        }

        if (isAdSignalText(runCatching { value.toString() }.getOrNull())) return true

        for (method in stringAccessorsFor(type)) {
            val marker = invokeNoThrow(method, value) as? String
            if (isAdSignalText(marker)) return true
        }

        for (field in stringFieldsFor(type)) {
            val marker = runCatching { field.get(value) as? String }.getOrNull()
            if (isAdSignalText(marker)) return true
        }

        return false
    }

    private fun stringAccessorsFor(type: Class<*>): List<Method> {
        return stringAccessorCache.getOrPut(type) {
            allInstanceMethods(type)
                .asSequence()
                .filter { method ->
                    method.parameterCount == 0 &&
                        method.returnType == String::class.java &&
                        method.declaringClass != Any::class.java &&
                        method.name != "toString"
                }
                .take(12)
                .onEach { method -> method.isAccessible = true }
                .toList()
        }
    }

    private fun stringFieldsFor(type: Class<*>): List<Field> {
        return stringFieldCache.getOrPut(type) {
            val fields = ArrayList<Field>()
            var current: Class<*>? = type
            while (current != null && current != Any::class.java && fields.size < 12) {
                current.declaredFields.forEach { field ->
                    if (!Modifier.isStatic(field.modifiers) && field.type == String::class.java && fields.size < 12) {
                        field.isAccessible = true
                        fields.add(field)
                    }
                }
                current = current.superclass
            }
            fields
        }
    }

    private fun isAdSignalText(value: String?): Boolean {
        if (value.isNullOrBlank()) return false
        val normalized = value.lowercase()
        return FEED_AD_SIGNAL_TOKENS.any { token -> normalized.contains(token) }
    }

    private fun allInstanceMethods(type: Class<*>): List<Method> {
        val methods = LinkedHashMap<String, Method>()
        var current: Class<*>? = type
        while (current != null && current != Any::class.java) {
            current.declaredMethods.forEach { method ->
                if (!Modifier.isStatic(method.modifiers)) {
                    method.isAccessible = true
                    methods.putIfAbsent("${current.name}#${method.name}/${method.parameterCount}", method)
                }
            }
            current.interfaces.forEach { iface ->
                iface.declaredMethods.forEach { method ->
                    if (!Modifier.isStatic(method.modifiers)) {
                        method.isAccessible = true
                        methods.putIfAbsent("${iface.name}#${method.name}/${method.parameterCount}", method)
                    }
                }
            }
            current = current.superclass
        }
        return methods.values.toList()
    }

    private fun invokeNoThrow(method: Method?, target: Any?): Any? {
        if (method == null || target == null) return null
        return runCatching { method.invoke(target) }.getOrNull()
    }
}

private fun Collection<MethodData>.firstMethodInstanceOrNull(classLoader: ClassLoader): Method? {
    return asSequence()
        .mapNotNull { methodData ->
            runCatching { methodData.getMethodInstance(classLoader) }.getOrNull()
        }
        .firstOrNull { method ->
            method.name != "<init>" && method.name != "<clinit>"
        }?.apply { isAccessible = true }
}

private fun findClassesByZeroArgStringTags(
    bridge: DexKitBridge,
    tags: Collection<String>
): List<ClassData> {
    val candidates = LinkedHashMap<String, ClassData>()
    tags.forEach { tag ->
        bridge.findClass {
            matcher {
                methods {
                    matchType = MatchType.Contains
                    add {
                        returnType = "java.lang.String"
                        paramCount = 0
                        usingStrings(tag)
                    }
                }
            }
        }.forEach { candidate ->
            candidates.putIfAbsent(candidate.name, candidate)
        }
    }
    return candidates.values.toList()
}

fun installFacebookAdRemover(classLoader: ClassLoader, bridge: DexKitBridge): Boolean {
    return try {
        Log.i(TAG, "Starting hook install: $BUILD_MARKER")
        val hooks = resolveHooks(classLoader, bridge)
        if (!hooks.hasLoadedSecondaryDexTargets()) {
            Log.w(TAG, "Facebook secondary dex targets are not loaded yet; deferring hook installation")
            return false
        }
        installFacebookVisibleAdTrace(classLoader)
        discoverFeedComponentGuardCandidates(bridge, classLoader)
        installFacebookFeedComponentGuard(classLoader)
        val feedItemInspector = FeedItemInspector(hooks.storyPoolAddMethods.map { it.parameterTypes[0] })
        Log.i(TAG, "FeedItemInspector accessors ${feedItemInspector.describeAccessors()}")

        if (
            ENABLE_UPSTREAM_REELS_AD_HOOKS &&
            hooks.adKindEnumClass != null &&
            hooks.listBuilderAppendMethod != null
        ) {
            val inspector = AdStoryInspector(hooks.adKindEnumClass)
            hookListBuilderAppend(hooks.listBuilderAppendMethod, inspector)
            hooks.listBuilderFactoryMethod?.let { hookListResultFilter(it, "list factory", inspector) }
            hooks.pluginPackBuildMethods.forEach { hookPluginPackFallback(it, inspector) }
        } else if (ENABLE_UPSTREAM_REELS_AD_HOOKS) {
            Log.w(TAG, "Upstream Reels targets unresolved; continuing with independent feed ad hooks")
        } else {
            Log.i(TAG, "Skipped upstream Reels list/plugin hooks to preserve feed Reels carousels")
        }
        hooks.instreamBannerEligibilityMethod?.let { hookInstreamBannerEligibility(it) }
        hooks.indicatorPillAdEligibilityMethod?.let { hookIndicatorPillAdEligibility(it) }
        hooks.reelsBannerRenderMethods.forEach { method ->
            runCatching { hookReelsBannerRender(method) }
                .onFailure {
                    Log.e(
                        TAG,
                        "Failed to hook Reels banner render ${method.declaringClass.name}.${method.name}",
                        it
                    )
                }
        }
        runCatching { installReelsAdDiagnostics(classLoader, bridge) }
            .onFailure { Log.w(TAG, "Failed to install Reels ad diagnostics", it) }
        runCatching { installMarketplaceAdRenderBlock(classLoader, bridge) }
            .onFailure { Log.w(TAG, "Failed to install Marketplace ad render block", it) }
        runCatching { installMarketplaceAdsQueryBlock(classLoader, bridge) }
            .onFailure { Log.w(TAG, "Failed to install Marketplace ads query block", it) }
        runCatching { installMarketplaceFeedResponseFilter(classLoader, bridge) }
            .onFailure { Log.w(TAG, "Failed to install Marketplace response probe", it) }
        if (ENABLE_FEED_CSR_FILTER_HOOKS) {
            hooks.feedCsrFilterHooks.forEach { hook ->
                runCatching { hookFeedCsrFilterInput(hook, feedItemInspector) }
                    .onFailure {
                        Log.e(
                            TAG,
                            "Failed to hook feed CSR filter ${hook.method.declaringClass.name}.${hook.method.name}",
                            it
                        )
                    }
            }
        } else {
            Log.i(TAG, "Skipped feed CSR filter hooks to isolate feed Reels carousel loading")
        }
        if (ENABLE_LATE_FEED_LIST_HOOKS) {
            hooks.lateFeedListHooks.forEach { hook ->
                runCatching { hookLateFeedListSanitizer(hook, feedItemInspector) }
                    .onFailure {
                        Log.e(
                            TAG,
                            "Failed to hook late feed list ${hook.method.declaringClass.name}.${hook.method.name}",
                            it
                        )
                    }
            }
        } else {
            Log.i(TAG, "Skipped late feed list hooks to isolate feed Reels carousel loading")
        }
        if (ENABLE_STORY_POOL_ADD_HOOKS) {
            // Diagnostic: log every item the shorts (reels) pool admits so a
            // full-page reels ad that slips through unclassified is visible.
            val shortsPoolClassNames = runCatching {
                bridge.findClass {
                    matcher {
                        usingStrings("FbShorts Pool")
                    }
                }.map { it.name }.toSet()
            }.getOrDefault(emptySet())
            Log.i(TAG, "Shorts pool classes for diagnostics: $shortsPoolClassNames")
            hooks.storyPoolAddMethods.forEach { method ->
                val logAllowed = method.declaringClass.name in shortsPoolClassNames
                runCatching { hookStoryPoolAdd(method, feedItemInspector, logAllowed) }
                    .onFailure {
                        Log.e(TAG, "Failed to hook story pool add ${method.declaringClass.name}.${method.name}", it)
                    }
            }
        } else {
            Log.i(TAG, "Skipped story pool add hooks to isolate feed Reels carousel loading")
        }
        if (ENABLE_FEED_SPONSORED_POOL_HOOKS) {
            hooks.sponsoredPoolAddMethod?.let { hookSponsoredPoolAdd(it) }
            hooks.sponsoredStoryNextMethod?.let { hookSponsoredStoryNext(it) }
        } else {
            Log.i(TAG, "Skipped feed sponsored pool hooks to isolate feed Reels carousel loading")
        }
        hooks.storyAdProviders.forEach { provider ->
            runCatching { hookStoryAdProvider(provider) }
                .onFailure {
                    Log.e(TAG, "Failed to hook story ad source ${provider.providerClass.name}", it)
                }
        }
        if (ENABLE_FEED_SPONSORED_POOL_HOOKS) {
            hooks.sponsoredPoolClass?.let {
                hookSponsoredPoolListMethods(it)
                hookSponsoredPoolResultMethods(it)
            }
            hooks.sponsoredStoryManagerClass?.let {
                hookSponsoredStoryListMethods(it)
            }
        }
        hooks.gameAdRequestMethods.forEach { method ->
            runCatching { hookGameAdRequest(method) }
                .onFailure {
                    Log.e(
                        TAG,
                        "Failed to hook game ad request ${method.declaringClass.name}.${method.name}",
                        it
                    )
                }
        }
        hooks.gameAdBridgePostMessageMethod?.let { method ->
            gameAdBridgeEntryMethodsHooked.add(methodHookKey(method))
            runCatching { hookGameAdBridge(method) }
                .onFailure {
                    Log.e(
                        TAG,
                        "Failed to hook game ad bridge ${method.declaringClass.name}.${method.name}",
                        it
                    )
                }
        }
        hooks.gameAdRequestMethods.firstOrNull()?.declaringClass?.let { bridgeClass ->
            runCatching { hookGameAdResultMethods(bridgeClass) }
                .onFailure {
                    Log.e(
                        TAG,
                        "Failed to hook game ad result helpers ${bridgeClass.name}",
                        it
                    )
                }
            runCatching { hookGameAdServiceDispatchMethods(bridgeClass) }
                .onFailure {
                    Log.e(
                        TAG,
                        "Failed to hook game ad service dispatch ${bridgeClass.name}",
                        it
                    )
                }
        }
        if (ENABLE_AUDIENCE_NETWORK_REWARD_FALLBACKS) {
            runCatching { hookAudienceNetworkRewardFallbacks(classLoader) }
                .onFailure { Log.e(TAG, "Failed to hook Audience Network reward fallbacks", it) }
        } else {
            Log.i(TAG, "Skipped Audience Network reward fallback hooks for compatibility mode")
        }
        installGameAdJavascriptInterfaceBridgeHook()
        runCatching { hookGameAdSystemDiagnostics(classLoader) }
            .onFailure { Log.e(TAG, "Failed to hook game ad diagnostics", it) }
        hooks.playableAdActivityOnCreate?.let { method ->
            runCatching { hookPlayableAdActivity(method) }
                .onFailure {
                    Log.e(
                        TAG,
                        "Failed to hook playable ad activity ${method.declaringClass.name}.${method.name}",
                        it
                    )
                }
        }
        hooks.gameAdUiActivityMethods.forEach { method ->
            runCatching { hookPlayableAdActivity(method) }
                .onFailure {
                    Log.e(
                        TAG,
                        "Failed to hook game ad activity ${method.declaringClass.name}.${method.name}",
                        it
                    )
                }
        }
        runCatching { hookGlobalGameAdActivityLifecycleFallback() }
            .onFailure { Log.e(TAG, "Failed to hook global game ad activity lifecycle fallback", it) }
        runCatching { hookGameAdActivityLaunchFallbacks() }
            .onFailure { Log.e(TAG, "Failed to hook game ad launch fallbacks", it) }
        runCatching { hookGlobalGameAdSurfaceFallbacks() }
            .onFailure { Log.e(TAG, "Failed to hook global game ad surface fallbacks", it) }
        Log.i(
            TAG,
            "Installed hooks: append=${if (ENABLE_UPSTREAM_REELS_AD_HOOKS) hooks.listBuilderAppendMethod?.let { "${it.declaringClass.name}.${it.name}" } ?: "none" else "disabled"}" +
                ", factory=${if (ENABLE_UPSTREAM_REELS_AD_HOOKS) hooks.listBuilderFactoryMethod?.let { "${it.declaringClass.name}.${it.name}" } ?: "none" else "disabled"}" +
                ", plugin=${if (ENABLE_UPSTREAM_REELS_AD_HOOKS) hooks.pluginPackBuildMethods.joinToString { "${it.declaringClass.name}.${it.name}" } else "disabled"}" +
                ", bannerState=${hooks.instreamBannerEligibilityMethod?.let { "${it.declaringClass.name}.${it.name}" } ?: "none"}" +
                ", indicatorPill=${hooks.indicatorPillAdEligibilityMethod?.let { "${it.declaringClass.name}.${it.name}" } ?: "none"}" +
                ", reelsBanner=${hooks.reelsBannerRenderMethods.joinToString { "${it.declaringClass.name}.${it.name}" }}" +
                ", feedFilters=${if (ENABLE_FEED_CSR_FILTER_HOOKS) hooks.feedCsrFilterHooks.joinToString { "${it.method.declaringClass.name}.${it.method.name}[${it.listArgIndex}]" } else "disabled"}" +
                ", lateFeed=${if (ENABLE_LATE_FEED_LIST_HOOKS) hooks.lateFeedListHooks.joinToString { "${it.method.declaringClass.name}.${it.method.name}[${it.listArgIndex}]" } else "disabled"}" +
                ", poolAdd=${if (ENABLE_STORY_POOL_ADD_HOOKS) hooks.storyPoolAddMethods.joinToString { "${it.declaringClass.name}.${it.name}" } else "disabled"}" +
                ", feedPoolAdd=${if (ENABLE_FEED_SPONSORED_POOL_HOOKS) hooks.sponsoredPoolAddMethod?.let { "${it.declaringClass.name}.${it.name}" } ?: "none" else "disabled"}" +
                ", feedHolder=${if (ENABLE_FEED_SPONSORED_POOL_HOOKS) hooks.sponsoredStoryManagerClass?.name ?: "none" else "disabled"}" +
                ", feedNext=${if (ENABLE_FEED_SPONSORED_POOL_HOOKS) hooks.sponsoredStoryNextMethod?.let { "${it.declaringClass.name}.${it.name}" } ?: "none" else "disabled"}" +
                ", storyProviders=${hooks.storyAdProviders.joinToString { it.providerClass.name }}" +
                ", gameAds=${hooks.gameAdRequestMethods.joinToString { "${it.declaringClass.name}.${it.name}" }}" +
                ", gameBridge=${hooks.gameAdBridgePostMessageMethod?.let { "${it.declaringClass.name}.${it.name}" } ?: "none"}" +
                ", playableAd=${hooks.playableAdActivityOnCreate?.let { "${it.declaringClass.name}.${it.name}" } ?: "none"}" +
                ", gameAdUi=${hooks.gameAdUiActivityMethods.joinToString { "${it.declaringClass.name}.${it.name}" }}"
        )
        true
    } catch (t: Throwable) {
        Log.resolutionFailure(TAG, "Failed to install Facebook ad remover hooks", t)
        false
    }
}

private fun ResolvedHooks.hasLoadedSecondaryDexTargets(): Boolean {
    return listBuilderAppendMethod != null ||
        pluginPackBuildMethods.isNotEmpty() ||
        feedCsrFilterHooks.isNotEmpty() ||
        lateFeedListHooks.isNotEmpty() ||
        storyPoolAddMethods.isNotEmpty() ||
        sponsoredPoolClass != null ||
        sponsoredStoryManagerClass != null ||
        storyAdProviders.isNotEmpty() ||
        gameAdRequestMethods.isNotEmpty()
}

private fun resolveHooks(classLoader: ClassLoader, bridge: DexKitBridge): ResolvedHooks {
    val classGroups = bridge.batchFindClassUsingStrings {
        groups(
            mapOf(
                "listBuilderByString" to listOf("Non ads story fall into ads rendering logic, StoryType=%s, StoryId=%s"),
                "pluginPack" to listOf("FbShortsViewerPluginPack", "MarketplaceAdsPluginPack"),
                "adKindEnum" to listOf("AD", "UGC", "PARADE", "MIDCARD"),
                "feedCsrFilters" to listOf("FeedCSRCacheFilter", "FeedCSRCacheFilter2025H1", "FeedCSRCacheFilter2026H1"),
                "sponsoredPool" to listOf("SponsoredPoolContainerAdapter", "Edge type mismatch; not added", "Sponsored Pool"),
                "sponsoredStoryManager" to listOf("FeedSponsoredStoryHolder.onPositionReset", "freshFeedStoryHolder"),
                "storyAdsInDisc" to STORY_AD_PROVIDER_TAGS
            ),
            StringMatchType.Equals
        )
    }

    Log.i(
        TAG,
        "DexKit groups: reels=${classGroups["listBuilderByString"]?.size ?: 0}, " +
            "plugin=${classGroups["pluginPack"]?.size ?: 0}, " +
            "adKind=${classGroups["adKindEnum"]?.size ?: 0}, " +
            "feedCsr=${classGroups["feedCsrFilters"]?.size ?: 0}, " +
            "feedPool=${classGroups["sponsoredPool"]?.size ?: 0}, " +
            "feedMgr=${classGroups["sponsoredStoryManager"]?.size ?: 0}, " +
            "storyAdsInDisc=${classGroups["storyAdsInDisc"]?.size ?: 0}"
    )

    val adKindEnumClass = resolveAdKindEnumClass(classLoader, classGroups["adKindEnum"].orEmpty(), bridge)
    val listBuilderClass = resolveListBuilderClass(classGroups["listBuilderByString"].orEmpty(), bridge)
    val pluginPackClasses = resolvePluginPackClasses(classGroups["pluginPack"].orEmpty(), bridge)
    val sponsoredPoolClass = resolveSponsoredPoolClass(classGroups["sponsoredPool"].orEmpty(), bridge)
    val sponsoredStoryManagerClass =
        resolveSponsoredStoryManagerClass(classGroups["sponsoredStoryManager"].orEmpty(), bridge)
    val storyAdProviderClasses =
        resolveStoryAdProviderClasses(classGroups["storyAdsInDisc"].orEmpty(), bridge)

    val appendMethod = listBuilderClass?.let { resolveAppendMethod(classLoader, it) }
    val factoryMethod = listBuilderClass?.let { resolveFactoryMethod(classLoader, it) }
    val pluginMethods = pluginPackClasses.mapNotNull { resolvePluginPackMethod(classLoader, it) }
    val instreamBannerEligibilityMethod = resolveInstreamBannerEligibilityMethod(classLoader, bridge)
    val indicatorPillAdEligibilityMethod = resolveIndicatorPillAdEligibilityMethod(classLoader, bridge)
    val reelsBannerRenderMethods = resolveReelsBannerRenderMethods(classLoader, bridge)
    val feedCsrFilterHooks =
        resolveFeedCsrFilterMethods(classLoader, classGroups["feedCsrFilters"].orEmpty(), bridge)
    val lateFeedListHooks = resolveLateFeedListHooks(classLoader, bridge)
    val storyPoolAddMethods = resolveStoryPoolAddMethods(classLoader, bridge)
    val poolClassInstance = sponsoredPoolClass?.getInstance(classLoader)
    val sponsoredStoryManagerClassInstance = sponsoredStoryManagerClass?.getInstance(classLoader)
    val poolAddMethod = sponsoredPoolClass?.let { resolveSponsoredPoolAddMethod(classLoader, it) }
    val sponsoredStoryNextMethod =
        sponsoredStoryManagerClass?.let { resolveSponsoredStoryNextMethod(classLoader, it) }
    val storyAdProviders = storyAdProviderClasses
        .mapNotNull { provider ->
            runCatching { resolveStoryAdProviderHooks(classLoader, provider) }.getOrNull()
        }
        .filter { provider ->
            provider.mergeMethod != null ||
                provider.fetchMoreAdsMethod != null ||
                provider.deferredUpdateMethod != null ||
                provider.insertionTriggerMethod != null
        }
        .distinctBy { it.providerClass.name }
    val gameAdRequestMethods = resolveGameAdRequestMethods(classLoader, bridge)
    val gameAdBridgePostMessageMethod = resolveGameAdBridgePostMessageMethod(gameAdRequestMethods)
    val playableAdActivityOnCreate = resolvePlayableAdActivityOnCreate(classLoader)
    val gameAdUiActivityMethods = resolveGameAdUiActivityMethods(classLoader)

    Log.i(TAG, "Resolved reels list builder=${listBuilderClass?.name ?: "none"}")
    Log.i(TAG, "Resolved plugin packs=${pluginPackClasses.joinToString { it.name }}")
    Log.i(TAG, "Resolved banner state eligibility=${instreamBannerEligibilityMethod?.declaringClass?.name ?: "none"}")
    Log.i(TAG, "Resolved indicator pill eligibility=${indicatorPillAdEligibilityMethod?.declaringClass?.name ?: "none"}")
    Log.i(TAG, "Resolved Reels banner render hooks=${reelsBannerRenderMethods.joinToString { it.declaringClass.name }}")
    Log.i(TAG, "Resolved feed CSR filters=${feedCsrFilterHooks.joinToString { "${it.method.declaringClass.name}[list=${it.listArgIndex}]" }}")
    Log.i(TAG, "Resolved late feed list hooks=${lateFeedListHooks.joinToString { it.method.declaringClass.name }}")
    Log.i(TAG, "Resolved story pool add hooks=${storyPoolAddMethods.joinToString { it.declaringClass.name }}")
    Log.i(TAG, "Resolved feed sponsored pool=${sponsoredPoolClass?.name ?: "none"}")
    Log.i(TAG, "Resolved feed sponsored manager=${sponsoredStoryManagerClass?.name ?: "none"}")
    Log.i(TAG, "Resolved feed add method=${poolAddMethod?.name ?: "none"}")
    Log.i(TAG, "Resolved feed next method=${sponsoredStoryNextMethod?.name ?: "none"}")
    Log.i(TAG, "Resolved story ad source classes=${storyAdProviderClasses.joinToString { it.name }}")
    Log.i(TAG, "Resolved story ad providers=${storyAdProviders.joinToString { it.providerClass.name }}")
    Log.i(TAG, "Resolved game ad requests=${gameAdRequestMethods.joinToString { it.declaringClass.name }}")
    Log.i(TAG, "Resolved game ad bridge=${gameAdBridgePostMessageMethod?.declaringClass?.name ?: "none"}")
    Log.i(TAG, "Resolved playable ad activity=${playableAdActivityOnCreate?.declaringClass?.name ?: "none"}")
    Log.i(TAG, "Resolved game ad UI activities=${gameAdUiActivityMethods.joinToString { it.declaringClass.name }}")
    logMissingHooks(
        pluginPackClasses = pluginPackClasses,
        factoryMethod = factoryMethod,
        pluginMethods = pluginMethods,
        instreamBannerEligibilityMethod = instreamBannerEligibilityMethod,
        indicatorPillAdEligibilityMethod = indicatorPillAdEligibilityMethod,
        reelsBannerRenderMethods = reelsBannerRenderMethods,
        feedCsrFilterHooks = feedCsrFilterHooks,
        lateFeedListHooks = lateFeedListHooks,
        storyPoolAddMethods = storyPoolAddMethods,
        sponsoredPoolClass = sponsoredPoolClass,
        poolAddMethod = poolAddMethod,
        sponsoredStoryManagerClass = sponsoredStoryManagerClass,
        sponsoredStoryNextMethod = sponsoredStoryNextMethod,
        storyAdProviderClasses = storyAdProviderClasses,
        storyAdProviders = storyAdProviders,
        gameAdRequestMethods = gameAdRequestMethods,
        gameAdBridgePostMessageMethod = gameAdBridgePostMessageMethod,
        playableAdActivityOnCreate = playableAdActivityOnCreate,
        gameAdUiActivityMethods = gameAdUiActivityMethods
    )

    return ResolvedHooks(
        adKindEnumClass = adKindEnumClass,
        listBuilderAppendMethod = appendMethod,
        listBuilderFactoryMethod = factoryMethod,
        pluginPackBuildMethods = pluginMethods,
        instreamBannerEligibilityMethod = instreamBannerEligibilityMethod,
        indicatorPillAdEligibilityMethod = indicatorPillAdEligibilityMethod,
        reelsBannerRenderMethods = reelsBannerRenderMethods,
        feedCsrFilterHooks = feedCsrFilterHooks,
        lateFeedListHooks = lateFeedListHooks,
        storyPoolAddMethods = storyPoolAddMethods,
        sponsoredPoolClass = poolClassInstance,
        sponsoredPoolAddMethod = poolAddMethod,
        sponsoredStoryManagerClass = sponsoredStoryManagerClassInstance,
        sponsoredStoryNextMethod = sponsoredStoryNextMethod,
        storyAdProviders = storyAdProviders,
        gameAdRequestMethods = gameAdRequestMethods,
        gameAdBridgePostMessageMethod = gameAdBridgePostMessageMethod,
        playableAdActivityOnCreate = playableAdActivityOnCreate,
        gameAdUiActivityMethods = gameAdUiActivityMethods
    )
}

private fun logMissingHooks(
    pluginPackClasses: List<ClassData>,
    factoryMethod: Method?,
    pluginMethods: List<Method>,
    instreamBannerEligibilityMethod: Method?,
    indicatorPillAdEligibilityMethod: Method?,
    reelsBannerRenderMethods: List<Method>,
    feedCsrFilterHooks: List<FeedCsrFilterHook>,
    lateFeedListHooks: List<FeedListSanitizerHook>,
    storyPoolAddMethods: List<Method>,
    sponsoredPoolClass: ClassData?,
    poolAddMethod: Method?,
    sponsoredStoryManagerClass: ClassData?,
    sponsoredStoryNextMethod: Method?,
    storyAdProviderClasses: List<ClassData>,
    storyAdProviders: List<StoryAdProviderHooks>,
    gameAdRequestMethods: List<Method>,
    gameAdBridgePostMessageMethod: Method?,
    playableAdActivityOnCreate: Method?,
    gameAdUiActivityMethods: List<Method>
) {
    if (factoryMethod == null) Log.missing(TAG, "Reels list factory method")
    if (pluginPackClasses.isEmpty()) {
        Log.missing(TAG, "PluginPack classes")
    } else if (pluginMethods.isEmpty()) {
        Log.missing(TAG, "PluginPack build methods")
    }
    if (instreamBannerEligibilityMethod == null) Log.missing(TAG, "Instream banner eligibility method")
    if (indicatorPillAdEligibilityMethod == null) Log.missing(TAG, "Reels indicator pill eligibility method")
    if (reelsBannerRenderMethods.isEmpty()) Log.missing(TAG, "Reels banner render methods")
    if (feedCsrFilterHooks.isEmpty()) Log.missing(TAG, "Feed CSR filter methods")
    if (lateFeedListHooks.isEmpty()) Log.missing(TAG, "Late feed list sanitizer methods")
    if (storyPoolAddMethods.isEmpty()) Log.missing(TAG, "Story pool add methods")
    if (sponsoredPoolClass == null) {
        Log.missing(TAG, "Sponsored pool class")
    } else if (poolAddMethod == null) {
        Log.missing(TAG, "Sponsored pool add method")
    }
    if (sponsoredStoryManagerClass == null) {
        Log.missing(TAG, "Sponsored story manager class")
    } else if (sponsoredStoryNextMethod == null) {
        Log.missing(TAG, "Sponsored story next method")
    }
    if (storyAdProviderClasses.isEmpty()) Log.missing(TAG, "Story ad source classes")
    if (storyAdProviders.isEmpty()) Log.missing(TAG, "Story ad provider methods")
    if (gameAdRequestMethods.isEmpty()) Log.missing(TAG, "Game ad request methods")
    if (gameAdBridgePostMessageMethod == null) Log.missing(TAG, "Game ad bridge postMessage method")
    if (playableAdActivityOnCreate == null) Log.missing(TAG, "Playable ad activity lifecycle method")
    if (gameAdUiActivityMethods.isEmpty()) Log.missing(TAG, "Game ad UI activity lifecycle methods")
}

private fun resolveAdKindEnumClass(
    classLoader: ClassLoader,
    batchCandidates: Collection<ClassData>,
    bridge: DexKitBridge
): Class<*>? {
    val directCandidates = if (batchCandidates.isNotEmpty()) {
        batchCandidates
    } else {
        bridge.findClass {
            matcher {
                usingEqStrings("AD", "UGC", "PARADE", "MIDCARD")
            }
        }
    }

    directCandidates.forEach { candidate ->
        val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
        val constants = clazz.enumConstants?.map { it.toString() }.orEmpty()
        if (clazz.isEnum && "AD" in constants && "UGC" in constants) {
            return clazz
        }
    }

    return null
}

private fun resolveListBuilderClass(
    batchCandidates: Collection<ClassData>,
    bridge: DexKitBridge
): ClassData? {
    val structuralCandidates = bridge.findClass {
        matcher {
            methods {
                matchType = MatchType.Contains
                add {
                    modifiers = Modifier.STATIC
                    returnType = "void"
                    paramTypes = listOf(null, null, null, null, null, "java.util.List")
                }
                add {
                    returnType = "void"
                    paramTypes = listOf(null, null, null, null, null, "java.util.List")
                }
                add {
                    modifiers = Modifier.STATIC
                    returnType = "java.util.ArrayList"
                    paramTypes = listOf(null, null, null, null, "boolean")
                }
                add {
                    modifiers = Modifier.STATIC
                    returnType = "java.util.ArrayList"
                    paramTypes = listOf(null, null, null, null, null, "boolean")
                }
                add {
                    returnType = "java.util.ArrayList"
                    paramTypes = listOf(null, null, null, "java.lang.Iterable")
                }
                add {
                    returnType = "java.util.List"
                    paramTypes = listOf(null, null, null, "boolean")
                }
            }
        }
    }

    return structuralCandidates.singleOrNull()
        ?: batchCandidates.firstOrNull()
}

private fun resolvePluginPackClasses(
    batchCandidates: Collection<ClassData>,
    bridge: DexKitBridge
): List<ClassData> {
    if (batchCandidates.isNotEmpty()) {
        return batchCandidates.toList()
    }

    val result = bridge.findClass {
        matcher {
            methods {
                matchType = MatchType.Contains
                add {
                    returnType = "java.lang.String"
                    paramCount = 0
                    usingStrings("FbShortsViewerPluginPack")
                }
                add {
                    returnType = "java.util.List"
                    paramCount = 0
                }
            }
        }
    }.toMutableList()
    
    result.addAll(bridge.findClass {
        matcher {
            methods {
                matchType = MatchType.Contains
                add {
                    returnType = "java.lang.String"
                    paramCount = 0
                    usingStrings("MarketplaceAdsPluginPack")
                }
                add {
                    returnType = "java.util.List"
                    paramCount = 0
                }
            }
        }
    })
    
    return result
}

private fun resolveSponsoredPoolClass(
    batchCandidates: Collection<ClassData>,
    bridge: DexKitBridge
): ClassData? {
    val candidates = if (batchCandidates.isNotEmpty()) {
        batchCandidates
    } else {
        bridge.findClass {
            matcher {
                usingEqStrings("SponsoredPoolContainerAdapter", "Edge type mismatch; not added")
            }
        }
    }

    return candidates.firstOrNull { candidate ->
        candidate.findMethod {
            findFirst = true
            matcher {
                returnType = "boolean"
                paramTypes = listOf("com.facebook.graphql.model.GraphQLFeedUnitEdge")
            }
        }.isNotEmpty()
    }
}

private fun resolveSponsoredStoryManagerClass(
    batchCandidates: Collection<ClassData>,
    bridge: DexKitBridge
): ClassData? {
    val candidates = if (batchCandidates.isNotEmpty()) {
        batchCandidates
    } else {
        bridge.findClass {
            matcher {
                usingEqStrings("FeedSponsoredStoryHolder.onPositionReset", "freshFeedStoryHolder")
            }
        }
    }

    return candidates.firstOrNull { candidate ->
        candidate.findMethod {
            findFirst = true
            matcher {
                returnType = "com.facebook.graphql.model.GraphQLFeedUnitEdge"
                paramCount = 0
            }
        }.isNotEmpty()
    }
}


private fun resolveStoryAdProviderClasses(
    batchCandidates: Collection<ClassData>,
    bridge: DexKitBridge
): List<ClassData> {
    val candidates = LinkedHashMap<String, ClassData>()
    batchCandidates.forEach { candidate ->
        candidates.putIfAbsent(candidate.name, candidate)
    }
    STORY_AD_PROVIDER_TAGS.forEach { tag ->
        bridge.findClass {
            matcher {
                usingStrings(tag)
            }
        }.forEach { candidate ->
            candidates.putIfAbsent(candidate.name, candidate)
        }
    }

    return candidates.values.toList()
}

private fun resolveStoryAdProviderHooks(
    classLoader: ClassLoader,
    providerClassData: ClassData
): StoryAdProviderHooks {
    val providerClass = providerClassData.getInstance(classLoader)
    val insertionTriggerMethod = providerClassData.findMethod {
        findFirst = true
        matcher {
            returnType = "void"
            usingStrings("ads_insertion")
        }
    }.firstMethodInstanceOrNull(classLoader)
    return resolveStoryAdProviderHooks(providerClass, insertionTriggerMethod)
}

private fun resolveStoryAdProviderHooks(
    providerClass: Class<*>,
    insertionTriggerMethod: Method? = null
): StoryAdProviderHooks {
    val methods = (providerClass.declaredMethods + providerClass.methods)
        .distinctBy { method ->
            "${method.name}:${method.parameterTypes.joinToString { it.name }}:${method.returnType.name}"
        }

    val mergeMethod = methods.firstOrNull { method ->
        method.parameterCount == 3 &&
            method.parameterTypes[0].name == "com.facebook.auth.usersession.FbUserSession" &&
            isFeedListType(method.parameterTypes[2]) &&
            isFeedListType(method.returnType)
    }?.apply { isAccessible = true }
    val fetchMoreAdsMethod = methods.firstOrNull { method ->
        method.returnType == Void.TYPE &&
            method.parameterCount == 2 &&
            isFeedListType(method.parameterTypes[0]) &&
            method.parameterTypes[1] == Int::class.javaPrimitiveType
    }?.apply { isAccessible = true }
    val deferredUpdateMethod = methods.firstOrNull { method ->
        method.returnType == Void.TYPE &&
            method.parameterCount == 2 &&
            !method.parameterTypes[0].isPrimitive &&
            isConcreteFeedListType(method.parameterTypes[1])
    }?.apply { isAccessible = true }

    return StoryAdProviderHooks(
        providerClass = providerClass,
        mergeMethod = mergeMethod,
        fetchMoreAdsMethod = fetchMoreAdsMethod,
        deferredUpdateMethod = deferredUpdateMethod,
        insertionTriggerMethod = insertionTriggerMethod
    )
}

// Debug-only: records which Litho component classes the wrapper renders besides
// the feed unit component, to spot ads rendering through other components.
private val feedWrapperChildClassesLogged = Collections.newSetFromMap(ConcurrentHashMap<String, Boolean>())

private fun logWrapperChildClass(owner: Any, wrapperChildField: Field) {
    val child = runCatching { wrapperChildField.get(owner) }.getOrNull() ?: return
    val key = "${owner.javaClass.name} -> ${child.javaClass.name}"
    if (feedWrapperChildClassesLogged.add(key)) {
        Log.i(TAG, "Feed wrapper child=$key")
    }
}

fun installFacebookFeedComponentGuard(classLoader: ClassLoader): Boolean {
    // The cached names may fail Class.forName at attach time (secondary dex not
    // yet configured) but resolve on a later attempt; retry on every call.
    registerCachedGuardClasses(classLoader, feedGuardCachedComponentNames, feedComponentCandidates)
    registerCachedGuardClasses(classLoader, feedGuardCachedWrapperNames, feedWrapperCandidates)
    val inspector = FeedItemInspector(emptyList())
    var resolvedTargets = 0
    var installed = 0
    val resolvedMethods = ArrayList<Method>()

    feedComponentCandidates.values.forEach { componentClass ->
        val edgeField = resolveFeedEdgeField(componentClass) ?: return@forEach
        feedWrapperCandidates.values.forEach { wrapperClass ->
            if (wrapperClass == componentClass) return@forEach
            val wrapperChildField = resolveWrapperChildField(wrapperClass, componentClass) ?: return@forEach
            val renderMethods = FEED_RENDER_PARAMETER_COUNTS.firstNotNullOfOrNull { parameterCount ->
                val layoutContextType =
                    resolveLithoLayoutContextType(componentClass, wrapperClass, parameterCount)
                        ?: return@firstNotNullOfOrNull null
                val methods = listOf(componentClass, wrapperClass).flatMap { type ->
                    lithoLayoutMethods(type, layoutContextType, parameterCount)
                }
                methods.ifEmpty { null }
            } ?: return@forEach

            resolvedTargets++
            resolvedMethods.addAll(renderMethods)
            feedGuardResolvedComponentNames.add(componentClass.name)
            feedGuardResolvedWrapperNames.add(wrapperClass.name)
            renderMethods.forEach { method ->
                val key = methodHookKey(method)
                if (!feedComponentMethodsHooked.add(key)) return@forEach

                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        val owner = param.thisObject ?: return
                        val component = when {
                            componentClass.isInstance(owner) -> owner
                            wrapperClass.isInstance(owner) -> runCatching {
                                wrapperChildField.get(owner)
                            }.getOrNull()?.takeIf(componentClass::isInstance)
                            else -> null
                        }
                        if (component == null) {
                            if (wrapperClass.isInstance(owner) && BuildConfig.DEBUG) {
                                logWrapperChildClass(owner, wrapperChildField)
                            }
                            return
                        }
                        val edge = runCatching { edgeField.get(component) }.getOrNull()
                        if (edge == null) {
                            logHookHitThrottled(
                                "sponsoredFeedComponentNoEdge",
                                method,
                                "component=${componentClass.name}"
                            )
                            return
                        }
                        if (!inspector.isDefinitelySponsoredFeedItem(edge)) {
                            logHookHitThrottled(
                                "sponsoredFeedComponentPass",
                                method,
                                inspector.describe(edge)
                            )
                            return
                        }

                        param.result = null
                        logHookHitThrottled(
                            "sponsoredFeedComponentBlock",
                            method,
                            inspector.describe(edge)
                        )
                    }
                })
                installed++
            }
        }
    }
    if (installed > 0) {
        Log.i(
            TAG,
            "Installed sponsored feed component guards=" +
                resolvedMethods.joinToString { "${it.declaringClass.name}.${it.name}" }
        )
    }
    return installed > 0
}

// Litho components carry their spec name ("NewsFeedFeedUnitComponent",
// "LoggingComponent") in a final String field of their generated base class,
// filled by a String constructor. Reflection cannot read the constant without
// running the constructor, so this instantiates the class through its no-arg
// constructor and reads the name. The generated component constructors are
// trivial (super(name) plus field defaults), and any class whose construction
// fails is simply skipped.
private val lithoComponentNameFields = ConcurrentHashMap<String, Optional<Field>>()

fun lithoComponentNameOf(type: Class<*>): String? {
    return runCatching {
        if (type.isInterface || type.isPrimitive || type.isArray || type.isAnnotation) return null
        var base = type.superclass
        var hops = 0
        while (base != null && base != Any::class.java && hops < 4) {
            val nameField = lithoComponentNameFields.computeIfAbsent(base.name) {
                Optional.ofNullable(
                    base.declaredFields.firstOrNull { declared ->
                        !Modifier.isStatic(declared.modifiers) &&
                            Modifier.isFinal(declared.modifiers) &&
                            declared.type == String::class.java
                    }?.takeIf {
                        base.declaredConstructors.any { constructor ->
                            constructor.parameterCount == 1 &&
                                constructor.parameterTypes[0] == String::class.java
                        }
                    }?.apply { isAccessible = true }
                )
            }.orElse(null)
            if (nameField != null) {
                val constructor = type.declaredConstructors.firstOrNull { it.parameterCount == 0 }
                    ?: return null
                constructor.isAccessible = true
                return nameField.get(constructor.newInstance()) as? String
            }
            base = base.superclass
            hops++
        }
        null
    }.getOrNull()
}

fun registerFeedGuardCandidate(type: Class<*>, componentName: String): Boolean {
    return when (componentName) {
        FEED_UNIT_COMPONENT_NAME -> {
            feedComponentCandidates.putIfAbsent(type.name, type) == null
            true
        }
        FEED_WRAPPER_COMPONENT_NAME -> {
            feedWrapperCandidates.putIfAbsent(type.name, type) == null
            true
        }
        else -> false
    }
}

// Backstop for the class-load notifier: once the secondary dex is scanned,
// DexKit finds the component classes by their stable name strings directly.
private fun registerLithoComponentClasses(
    bridge: DexKitBridge,
    classLoader: ClassLoader,
    componentName: String,
    registry: ConcurrentHashMap<String, Class<*>>
) {
    val classes = runCatching {
        bridge.findClass {
            matcher {
                usingStrings(listOf(componentName), StringMatchType.Equals)
            }
        }.mapNotNull { classData ->
            runCatching { classData.getInstance(classLoader) }.getOrNull()
        }
    }.getOrDefault(emptyList())
    classes.forEach { discovered -> registry.putIfAbsent(discovered.name, discovered) }
    Log.i(
        TAG,
        "Discovered Litho component name=$componentName classes=" +
            classes.joinToString { it.name }
    )
}

fun discoverFeedComponentGuardCandidates(bridge: DexKitBridge, classLoader: ClassLoader) {
    registerLithoComponentClasses(bridge, classLoader, FEED_UNIT_COMPONENT_NAME, feedComponentCandidates)
    registerLithoComponentClasses(bridge, classLoader, FEED_WRAPPER_COMPONENT_NAME, feedWrapperCandidates)
}

// The full DexKit scan takes seconds, but the cached initial News Feed renders
// within the first seconds after a cold start — before the scan finishes. The
// discovered guard pair is therefore persisted (keyed by the host app version
// AND the module version) so later launches can register and hook the same
// classes within ~100ms of Application.attach. A Facebook update changes the
// obfuscated names, and a module update may change discovery semantics; either
// invalidates the cache via the version keys.
private const val FEED_GUARD_CACHE_FILE = "fbar_feed_guard_cache.properties"

private fun feedGuardCacheModuleKey(): String {
    return "${BuildConfig.VERSION_NAME} (${BuildConfig.VERSION_CODE})"
}

private fun registerCachedGuardClasses(
    classLoader: ClassLoader,
    classNames: List<String>,
    registry: ConcurrentHashMap<String, Class<*>>
): Int {
    var registered = 0
    classNames.forEach { className ->
        runCatching { Class.forName(className, false, classLoader) }.getOrNull()?.let { loaded ->
            registry.putIfAbsent(loaded.name, loaded)
            registered++
        }
    }
    return registered
}

// Parsed once from the cache file; every guard install attempt retries these
// names because the secondary dex is often not configurable yet at
// Application.attach, when the cache is first read.
@Volatile
private var feedGuardCachedComponentNames: List<String> = emptyList()

@Volatile
private var feedGuardCachedWrapperNames: List<String> = emptyList()

fun loadCachedFeedGuardCandidates(
    context: Context,
    classLoader: ClassLoader,
    hostVersionName: String
): Int {
    if (hostVersionName.isBlank()) return 0
    return runCatching {
        val file = File(context.cacheDir, FEED_GUARD_CACHE_FILE)
        if (!file.exists()) {
            Log.i(TAG, "Feed guard cache missing; re-discovering")
            return 0
        }
        val properties = Properties()
        file.inputStream().use { properties.load(it) }
        if (hostVersionName != properties.getProperty("version")) {
            Log.i(TAG, "Feed guard cache stale for version=$hostVersionName; re-discovering")
            return 0
        }
        if (feedGuardCacheModuleKey() != properties.getProperty("moduleVersion")) {
            Log.i(TAG, "Feed guard cache stale for moduleVersion=${feedGuardCacheModuleKey()}; re-discovering")
            return 0
        }
        feedGuardCachedComponentNames = properties.getProperty("components").orEmpty()
            .split(',').filter { it.isNotBlank() }
        feedGuardCachedWrapperNames = properties.getProperty("wrappers").orEmpty()
            .split(',').filter { it.isNotBlank() }
        val registered = registerCachedGuardClasses(classLoader, feedGuardCachedComponentNames, feedComponentCandidates) +
            registerCachedGuardClasses(classLoader, feedGuardCachedWrapperNames, feedWrapperCandidates)
        Log.i(
            TAG,
            "Loaded feed guard cache components=$feedGuardCachedComponentNames " +
                "wrappers=$feedGuardCachedWrapperNames registeredNow=$registered"
        )
        registered
    }.onFailure {
        Log.w(TAG, "Failed to load feed guard cache", it)
    }.getOrDefault(0)
}

fun saveFeedGuardCandidateCache(context: Context, hostVersionName: String) {
    if (hostVersionName.isBlank()) return
    val components = feedGuardResolvedComponentNames.toList()
    val wrappers = feedGuardResolvedWrapperNames.toList()
    if (components.isEmpty() || wrappers.isEmpty()) return
    runCatching {
        val file = File(context.cacheDir, FEED_GUARD_CACHE_FILE)
        val properties = Properties()
        properties.setProperty("version", hostVersionName)
        properties.setProperty("moduleVersion", feedGuardCacheModuleKey())
        properties.setProperty("components", components.joinToString(","))
        properties.setProperty("wrappers", wrappers.joinToString(","))
        file.outputStream().use { properties.store(it, null) }
        Log.i(TAG, "Saved feed guard cache components=$components wrappers=$wrappers")
    }.onFailure {
        Log.w(TAG, "Failed to save feed guard cache", it)
    }
}

// Litho layout entry points are obfuscated differently in every build (A1H on 571,
// both A1F and A1H on 576), so they are matched by shape instead of by name.
// Static builder factories share the same shape and must stay unhooked.
private fun lithoLayoutMethods(
    type: Class<*>,
    contextType: Class<*>,
    parameterCount: Int
): List<Method> {
    return type.declaredMethods.filter { method ->
        !Modifier.isStatic(method.modifiers) &&
            method.parameterCount == parameterCount &&
            !method.returnType.isPrimitive &&
            method.parameterTypes[0] == contextType
    }.onEach { it.isAccessible = true }
}

private fun resolveLithoLayoutContextType(
    componentClass: Class<*>,
    wrapperClass: Class<*>,
    parameterCount: Int
): Class<*>? {
    fun contextCandidates(type: Class<*>): List<Class<*>> {
        return type.declaredMethods
            .filter { method ->
                !Modifier.isStatic(method.modifiers) &&
                    method.parameterCount == parameterCount &&
                    !method.returnType.isPrimitive &&
                    !method.parameterTypes[0].isPrimitive
            }
            .map { it.parameterTypes[0] }
    }

    val componentCandidates = contextCandidates(componentClass)
    val wrapperCandidates = contextCandidates(wrapperClass).toSet()
    return componentCandidates.firstOrNull { it in wrapperCandidates }
        ?: componentCandidates.groupingBy { it }.eachCount().maxByOrNull { it.value }?.key
}

private fun resolveFeedEdgeField(componentClass: Class<*>): Field? {
    val declared = componentClass.declaredFields.filter { field ->
        !Modifier.isStatic(field.modifiers) && !field.type.isPrimitive
    }
    val resolved = declared.firstOrNull { it.type.name == GRAPHQL_FEED_UNIT_EDGE_CLASS }
        ?: declared.firstOrNull { declaresFeedStoryCategoryAccessor(it.type) }
    return resolved?.apply { isAccessible = true }
}

private fun resolveWrapperChildField(
    wrapperClass: Class<*>,
    componentClass: Class<*>
): Field? {
    val resolved = wrapperClass.declaredFields.firstOrNull { field ->
        !Modifier.isStatic(field.modifiers) &&
            field.type != Any::class.java &&
            field.type.isAssignableFrom(componentClass)
    }
    return resolved?.apply { isAccessible = true }
}

// The story-category enum moved package between builds, so match it by its
// constants rather than by class name.
private fun declaresFeedStoryCategoryAccessor(type: Class<*>): Boolean {
    return runCatching {
        type.declaredMethods.any { method ->
            method.parameterCount == 0 &&
                method.returnType.isEnum &&
                method.returnType.enumConstants?.any { constant ->
                    val name = constant.toString()
                    name == "SPONSORED" || name == "PROMOTION"
                } == true
        }
    }.getOrDefault(false)
}


private fun logFacebookSurvivingFeedTypeContracts(classLoader: ClassLoader) {
    if (!BuildConfig.DEBUG || survivingFeedTypeContractsLogged.getAndIncrement() != 0) return

    survivingFeedTypeClassNames().forEach { className ->
        logSurvivingFeedTypeContract(classLoader, className)
    }
}

private fun logSurvivingFeedTypeContract(classLoader: ClassLoader, className: String) {
    val type = runCatching {
        Class.forName(className, false, classLoader)
    }.getOrElse {
        Log.w(TAG, "SurvivingFeedType class unavailable=$className")
        return
    }
    Log.i(
        TAG,
        "SurvivingFeedType class=${type.name} super=${type.superclass?.name} " +
            "interfaces=${type.interfaces.joinToString { it.name }}"
    )
    type.declaredFields.forEach { field ->
        Log.i(
            TAG,
            "SurvivingFeedType field=${type.name}.${field.name}:${field.type.name} " +
                "static=${Modifier.isStatic(field.modifiers)}"
        )
    }
    type.declaredConstructors.forEach { constructor ->
        Log.i(
            TAG,
            "SurvivingFeedType ctor=${type.name}(" +
                constructor.parameterTypes.joinToString { it.name } + ")"
        )
    }
    type.declaredMethods.forEach { method ->
        Log.i(
            TAG,
            "SurvivingFeedType method=${type.name}.${method.name}(" +
                method.parameterTypes.joinToString { it.name } + "):${method.returnType.name} " +
                "static=${Modifier.isStatic(method.modifiers)}"
        )
    }
}

fun installFacebookVisibleAdTrace(classLoader: ClassLoader) {
    if (!BuildConfig.DEBUG || visibleAdTraceInstalled.getAndIncrement() != 0) return

    val method = View::class.java.getDeclaredMethod(
        "setContentDescription",
        CharSequence::class.java
    ).apply { isAccessible = true }
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun afterHookedMethod(param: MethodHookParam) {
            val marker = param.args.getOrNull(0)?.toString().orEmpty()
            if (
                !marker.equals("Hide ad", ignoreCase = true) &&
                !marker.contains("Ad\u2022Shared with", ignoreCase = true)
            ) {
                return
            }
            val view = param.thisObject as? View ?: return
            view.postDelayed(
                { traceVisibleFacebookFeedAd(view, marker, classLoader, 0) },
                150L
            )
        }
    })
    Log.i(TAG, "Installed visible-ad holder tracer")
}

private data class VisibleAdGraphNode(
    val value: Any,
    val path: String,
    val depth: Int
)

private fun traceVisibleFacebookFeedAd(
    markerView: View,
    marker: String,
    classLoader: ClassLoader,
    attempt: Int
) {
    val recycler = findRecyclerViewAncestor(markerView)
    val lithoView = findViewAncestor(markerView, "com.facebook.litho.LithoView")
    if (recycler == null && lithoView == null) {
        if (attempt < 5) {
            markerView.postDelayed(
                {
                    traceVisibleFacebookFeedAd(
                        markerView,
                        marker,
                        classLoader,
                        attempt + 1
                    )
                },
                250L
            )
        }
        return
    }

    val traceKey = System.identityHashCode(markerView)
    if (visibleAdViewsTraced.putIfAbsent(traceKey, true) != null) return

    val holder = invokeMethodByName(recycler, "findContainingViewHolder", markerView)
    val adapter = invokeMethodByName(recycler, "getAdapter")
    val bindingPosition = invokeMethodByName(holder, "getBindingAdapterPosition")
    val absolutePosition = invokeMethodByName(holder, "getAbsoluteAdapterPosition")
    Log.i(
        TAG,
        "VisibleAdTrace marker=$marker recycler=${recycler?.javaClass?.name ?: "null"} " +
            "lithoView=${lithoView?.javaClass?.name ?: "null"} " +
            "holder=${holder?.javaClass?.name ?: "null"} adapter=${adapter?.javaClass?.name ?: "null"} " +
            "bindingPosition=$bindingPosition absolutePosition=$absolutePosition"
    )

    val inspector = FeedItemInspector(emptyList())
    lithoView?.let { traceVisibleAdObjectGraph(it, "lithoView", inspector) }
    holder?.let { traceVisibleAdObjectGraph(it, "holder", inspector) }
    adapter?.let { traceVisibleAdObjectGraph(it, "adapter", inspector) }
}

private fun findViewAncestor(view: View, className: String): View? {
    var current: View? = view
    repeat(80) {
        val value = current ?: return null
        if (value.javaClass.name == className) return value
        current = value.parent as? View
    }
    return null
}

private fun findRecyclerViewAncestor(view: View): Any? {
    var current: Any? = view
    repeat(80) {
        val value = current ?: return null
        if (
            allMethodsInHierarchy(value.javaClass).any { method ->
                method.name == "findContainingViewHolder" && method.parameterCount == 1
            }
        ) {
            return value
        }
        current = runCatching {
            (value as? View)?.parent
        }.getOrNull()
    }
    return null
}

private fun invokeMethodByName(target: Any?, methodName: String, vararg args: Any?): Any? {
    if (target == null) return null
    val method = allMethodsInHierarchy(target.javaClass).firstOrNull { candidate ->
        candidate.name == methodName &&
            candidate.parameterCount == args.size &&
            candidate.parameterTypes.zip(args).all { (parameterType, argument) ->
                argument == null || parameterType.isAssignableFrom(argument.javaClass)
            }
    } ?: return null
    method.isAccessible = true
    return runCatching { method.invoke(target, *args) }.getOrNull()
}

private fun traceVisibleAdObjectGraph(
    root: Any,
    rootPath: String,
    inspector: FeedItemInspector
) {
    val queue = ArrayDeque<VisibleAdGraphNode>()
    val seen = IdentityHashMap<Any, Boolean>()
    queue.add(VisibleAdGraphNode(root, rootPath, 0))
    var visited = 0
    var matches = 0

    while (queue.isNotEmpty() && visited < 2_000 && matches < 80) {
        val node = queue.removeFirst()
        val value = node.value
        if (seen.put(value, true) != null) continue
        visited++

        val type = value.javaClass
        val typeName = type.name
        if (isTraceableFeedObject(type)) {
            matches++
            Log.i(
                TAG,
                "VisibleAdTrace feedObject path=${node.path} class=$typeName " +
                    inspector.describe(value)
            )
        }

        if (value is CharSequence) {
            val text = value.toString()
            if (isVisibleAdTraceString(text)) {
                matches++
                Log.i(TAG, "VisibleAdTrace string path=${node.path} value=${text.take(300)}")
            }
            continue
        }
        if (node.depth >= 7 || shouldSkipVisibleAdTraceType(type)) continue

        if (value is Iterable<*>) {
            var index = 0
            for (item in value) {
                if (item != null && index < 300) {
                    queue.add(VisibleAdGraphNode(item, "${node.path}[$index]", node.depth + 1))
                }
                index++
                if (index >= 300) break
            }
        } else if (type.isArray && !type.componentType.isPrimitive) {
            val length = java.lang.reflect.Array.getLength(value).coerceAtMost(300)
            for (index in 0 until length) {
                java.lang.reflect.Array.get(value, index)?.let { item ->
                    queue.add(VisibleAdGraphNode(item, "${node.path}[$index]", node.depth + 1))
                }
            }
        }

        allFieldsInHierarchy(type).forEach { field ->
            if (Modifier.isStatic(field.modifiers) || field.type.isPrimitive) return@forEach
            field.isAccessible = true
            val child = runCatching { field.get(value) }.getOrNull() ?: return@forEach
            queue.add(
                VisibleAdGraphNode(
                    child,
                    "${node.path}.${type.simpleName}.${field.name}",
                    node.depth + 1
                )
            )
        }
    }
    Log.i(TAG, "VisibleAdTrace graph root=$rootPath visited=$visited matches=$matches")
}

private fun isTraceableFeedObject(type: Class<*>): Boolean {
    return type.name == GRAPHQL_FEED_UNIT_EDGE_CLASS ||
        (type.name.contains("GraphQL") && type.name.contains("Feed"))
}

private fun shouldSkipVisibleAdTraceType(type: Class<*>): Boolean {
    val name = type.name
    return type.isEnum ||
        Number::class.java.isAssignableFrom(type) ||
        type == java.lang.Boolean::class.java ||
        name.startsWith("java.lang.Class") ||
        name.startsWith("java.lang.reflect.") ||
        name.startsWith("android.graphics.") ||
        name.startsWith("android.content.res.")
}

private fun isVisibleAdTraceString(value: String): Boolean {
    val normalized = value.lowercase()
    return normalized.contains("xtreme-pc") ||
        normalized.contains("book now") ||
        normalized.contains("hide ad") ||
        normalized.contains("samurai") ||
        normalized.contains("sponsored") ||
        normalized.contains("ad choices") ||
        normalized.contains("adchoices") ||
        normalized.contains("apply now") ||
        normalized.contains("send message") ||
        normalized.contains("learn more") ||
        normalized.contains("shop now") ||
        normalized.contains("contact us") ||
        normalized.contains("get quote") ||
        normalized.contains("call now") ||
        normalized.contains("sign up")
}

private fun allFieldsInHierarchy(type: Class<*>): List<Field> {
    val fields = ArrayList<Field>()
    var current: Class<*>? = type
    while (current != null && current != Any::class.java && fields.size < 200) {
        fields.addAll(current.declaredFields)
        current = current.superclass
    }
    return fields
}

private fun allMethodsInHierarchy(type: Class<*>): List<Method> {
    val methods = LinkedHashMap<String, Method>()
    var current: Class<*>? = type
    while (current != null && current != Any::class.java) {
        current.declaredMethods.forEach { method ->
            methods.putIfAbsent(
                "${method.name}:${method.parameterTypes.joinToString { it.name }}",
                method
            )
        }
        current = current.superclass
    }
    return methods.values.toList()
}


private fun isFeedListType(type: Class<*>): Boolean {
    return Iterable::class.java.isAssignableFrom(type) ||
        type.name == "com.google.common.collect.ImmutableList"
}

// Narrower than isFeedListType: only concrete collection types, never arbitrary
// interfaces that happen to extend Iterable. Used where the shape rule alone is
// too generic to safely identify a method (see deferredUpdateMethod).
private fun isConcreteFeedListType(type: Class<*>): Boolean {
    return Collection::class.java.isAssignableFrom(type)
}

private fun resolveAppendMethod(classLoader: ClassLoader, listBuilderClass: ClassData): Method? {
    val clazz = listBuilderClass.getInstance(classLoader)
    return resolveListBuilderMethods(clazz)
        .filter { method ->
            method.returnType == Void.TYPE &&
                method.listParameterIndexes().size == 1 &&
                method.listParameterIndexes().first() == method.parameterCount - 1
        }
        .maxByOrNull { method -> scoreAppendMethod(method, clazz) }
        ?.apply { isAccessible = true }
}

private fun resolveFactoryMethod(classLoader: ClassLoader, listBuilderClass: ClassData): Method? {
    val clazz = listBuilderClass.getInstance(classLoader)
    return resolveListBuilderMethods(clazz)
        .filter { method ->
            Modifier.isStatic(method.modifiers) &&
                method.returnType == ArrayList::class.java &&
                method.parameterTypes.lastOrNull() == Boolean::class.javaPrimitiveType &&
                (
                    method.parameterTypes.firstOrNull() == clazz ||
                        method.parameterTypes.getOrNull(1) == clazz
                    )
        }
        .maxByOrNull { method -> scoreFactoryMethod(method, clazz) }
        ?.apply { isAccessible = true }
}

private fun resolveListBuilderMethods(clazz: Class<*>): List<Method> {
    val methods = LinkedHashMap<String, Method>()
    (clazz.declaredMethods + clazz.methods).forEach { method ->
        if (method.name != "<init>" && method.name != "<clinit>") {
            methods.putIfAbsent("${method.name}/${method.parameterCount}/${Modifier.isStatic(method.modifiers)}", method)
        }
    }
    return methods.values.toList()
}

private fun Method.listParameterIndexes(): List<Int> {
    return parameterTypes.mapIndexedNotNull { index, type ->
        index.takeIf { List::class.java.isAssignableFrom(type) }
    }
}

private fun scoreAppendMethod(method: Method, owner: Class<*>): Int {
    val listIndex = method.listParameterIndexes().firstOrNull() ?: return Int.MIN_VALUE
    var score = 0
    if (listIndex == method.parameterCount - 1) score += 10_000
    if (method.parameterCount == 6) score += 5_000
    if (!Modifier.isStatic(method.modifiers)) score += 2_000
    if (Modifier.isStatic(method.modifiers) && method.parameterTypes.getOrNull(1) == owner) score += 1_500
    if (Modifier.isStatic(method.modifiers) && method.parameterTypes.firstOrNull() == owner) score += 750
    score -= method.parameterCount * 10
    return score
}

private fun scoreFactoryMethod(method: Method, owner: Class<*>): Int {
    var score = 0
    if (method.parameterCount == 6) score += 4_000
    if (method.parameterCount == 5) score += 3_000
    if (method.parameterTypes.getOrNull(1) == owner) score += 2_000
    if (method.parameterTypes.firstOrNull() == owner) score += 1_000
    if (method.parameterTypes.firstOrNull()?.name == "com.facebook.auth.usersession.FbUserSession") score += 500
    score -= method.parameterCount * 10
    return score
}

private fun resolvePluginPackMethod(classLoader: ClassLoader, pluginPackClass: ClassData): Method? {
    val method = pluginPackClass.findMethod {
        findFirst = true
        matcher {
            returnType = "java.util.List"
            paramCount = 0
        }
    }.firstOrNull() ?: return null

    return listOf(method).firstMethodInstanceOrNull(classLoader)
}

private fun resolveFeedCsrFilterMethods(
    classLoader: ClassLoader,
    batchCandidates: Collection<ClassData>,
    bridge: DexKitBridge
): List<FeedCsrFilterHook> {
    val namedCandidates = if (batchCandidates.isNotEmpty()) {
        batchCandidates.toList()
    } else {
        findClassesByZeroArgStringTags(
            bridge,
            listOf(
                "FeedCSRCacheFilter",
                "FeedCSRCacheFilter2025H1",
                "FeedCSRCacheFilter2026H1",
                "FeedCSRCacheFilter2026H2"
            )
        )
    }

    val candidates = LinkedHashMap<String, ClassData>()
    namedCandidates.forEach { candidates.putIfAbsent(it.name, it) }

    return candidates.values.mapNotNull { candidate ->
        val fourArgMethod = candidate.findMethod {
            findFirst = true
            matcher {
                paramTypes = listOf(
                    "com.facebook.auth.usersession.FbUserSession",
                    null,
                    "com.google.common.collect.ImmutableList",
                    "int"
                )
            }
        }.firstMethodInstanceOrNull(classLoader)
        when {
            fourArgMethod != null -> FeedCsrFilterHook(fourArgMethod, 2)
            else -> candidate.findMethod {
                findFirst = true
                matcher {
                    paramTypes = listOf(
                        "com.facebook.auth.usersession.FbUserSession",
                        "com.google.common.collect.ImmutableList",
                        "int"
                    )
                }
            }.firstMethodInstanceOrNull(classLoader)?.let { method ->
                FeedCsrFilterHook(method, 1)
            }
        }
    }.filter { hook ->
        !Modifier.isAbstract(hook.method.modifiers) &&
            !hook.method.declaringClass.isInterface &&
            !Modifier.isAbstract(hook.method.declaringClass.modifiers)
    }.distinctBy { "${it.method.declaringClass.name}.${it.method.name}:${it.listArgIndex}" }
}

private fun resolveLateFeedListHooks(
    classLoader: ClassLoader,
    bridge: DexKitBridge
): List<FeedListSanitizerHook> {
    val hooks = LinkedHashMap<String, FeedListSanitizerHook>()

    bridge.findClass {
        matcher {
            usingStrings("handleStorageStories", "Empty Storage List")
        }
    }.forEach { candidate ->
        candidate.findMethod {
            findFirst = true
            matcher {
                returnType = "void"
                paramTypes = listOf(null, "com.google.common.collect.ImmutableList", "int")
            }
        }.firstMethodInstanceOrNull(classLoader)?.let { method ->
            hooks.putIfAbsent(
                "${method.declaringClass.name}.${method.name}:1",
                FeedListSanitizerHook(method, 1)
            )
        }
    }

    bridge.findClass {
        matcher {
            usingStrings("cancelVendingTimerAndAddToPool_")
        }
    }.forEach { candidate ->
        candidate.findMethod {
            findFirst = true
            matcher {
                returnType = "void"
                paramTypes = listOf("com.google.common.collect.ImmutableList", "java.lang.String")
            }
        }.firstMethodInstanceOrNull(classLoader)?.let { method ->
            hooks.putIfAbsent(
                "${method.declaringClass.name}.${method.name}:0",
                FeedListSanitizerHook(method, 0)
            )
        }
    }

    findClassesByZeroArgStringTags(
        bridge,
        listOf(
            "CSRNoOpStorageLifecycleImpl",
            "FeedCSRStorageLifecycle",
            "FriendlyFeedCSRStorageLifecycle",
            "FbShortsCSRStorageLifecycle"
        )
    ).forEach { candidate ->
        candidate.findMethod {
            findFirst = true
            matcher {
                returnType = "void"
                paramTypes = listOf(
                    "com.facebook.auth.usersession.FbUserSession",
                    null,
                    "com.google.common.collect.ImmutableList"
                )
            }
        }.firstMethodInstanceOrNull(classLoader)?.let { method ->
            hooks.putIfAbsent(
                "${method.declaringClass.name}.${method.name}:2",
                FeedListSanitizerHook(method, 2)
            )
        }
    }

    return hooks.values.filter { hook ->
        !Modifier.isAbstract(hook.method.modifiers) &&
            !hook.method.declaringClass.isInterface &&
            !Modifier.isAbstract(hook.method.declaringClass.modifiers)
    }.toList()
}

private fun resolveStoryPoolAddMethods(
    classLoader: ClassLoader,
    bridge: DexKitBridge
): List<Method> {
    val methods = LinkedHashMap<String, Method>()

    findClassesByZeroArgStringTags(
        bridge,
        listOf("CSRStoryPoolCoordinator", "FeedStoryPoolCoordinator")
    ).forEach { candidate ->
        // Hook every instance boolean single-arg method on the coordinator, not
        // just the first match: 576's shorts pool (X.1mn) exposes both a static
        // eligibility helper and the real pool-add ABd, and findFirst picked the
        // helper, leaving the FbShorts pool's add path unhooked.
        candidate.findMethod {
            matcher {
                returnType = "boolean"
                paramTypes = listOf(null)
            }
        }.mapNotNull { methodData ->
            runCatching { methodData.getMethodInstance(classLoader) }.getOrNull()
        }.forEach { method ->
            methods.putIfAbsent("${method.declaringClass.name}.${method.name}", method)
        }
    }

    return methods.values.filter { method ->
        !Modifier.isStatic(method.modifiers) &&
            !Modifier.isAbstract(method.modifiers) &&
            !method.declaringClass.isInterface &&
            !Modifier.isAbstract(method.declaringClass.modifiers)
    }.toList()
}

private fun resolveInstreamBannerEligibilityMethod(
    classLoader: ClassLoader,
    bridge: DexKitBridge
): Method? {
    val candidates = findClassesByZeroArgStringTags(
        bridge,
        listOf("InstreamAdIdleWithBannerState")
    )

    candidates.asSequence().mapNotNull { candidate ->
        candidate.findMethod {
            findFirst = true
            matcher {
                returnType = "boolean"
                paramCount = 0
            }
        }.firstMethodInstanceOrNull(classLoader)
    }.firstOrNull { method ->
        !Modifier.isStatic(method.modifiers)
    }?.apply { isAccessible = true }?.let { return it }

    candidates.asSequence().mapNotNull { candidate ->
        val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@mapNotNull null
        var current: Class<*>? = clazz.superclass
        while (current != null && current != Any::class.java) {
            current.declaredMethods.firstOrNull { method ->
                !Modifier.isStatic(method.modifiers) &&
                    method.returnType == Boolean::class.javaPrimitiveType &&
                    method.parameterCount == 0
            }?.let { method ->
                method.isAccessible = true
                return@mapNotNull method
            }
            current = current.superclass
        }
        null
    }.firstOrNull()?.let { return it }

    return null
}

private fun resolveIndicatorPillAdEligibilityMethod(
    classLoader: ClassLoader,
    bridge: DexKitBridge
): Method? {
    val classCandidates = bridge.findClass {
        matcher {
            usingStrings(
                "IndicatorPillComponent.render",
                "com.facebook.feedback.comments.plugins.indicatorpill.reelsadsfloatingcta.ReelsAdsFloatingCtaPlugin"
            )
        }
    }

    return classCandidates.asSequence().mapNotNull { candidate ->
        candidate.findMethod {
            findFirst = true
            matcher {
                modifiers = Modifier.STATIC
                returnType = "boolean"
                paramCount = 3
            }
        }.firstMethodInstanceOrNull(classLoader)
    }.firstOrNull()?.apply { isAccessible = true }
}

private fun resolveReelsBannerRenderMethods(
    classLoader: ClassLoader,
    bridge: DexKitBridge
): List<Method> {
    val componentClasses = LinkedHashMap<String, Class<*>>()

    listOf("ReelsBannerAdsComponent", "ReelsBannerAdsNativeComponent").forEach { componentName ->
        bridge.findClass {
            matcher {
                usingStrings(componentName)
            }
        }.forEach { candidate ->
            val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
            if (resolveLithoRenderMethod(clazz) != null) {
                componentClasses.putIfAbsent(clazz.name, clazz)
            }
        }
    }

    return componentClasses.values.mapNotNull { clazz ->
        resolveLithoRenderMethod(clazz)
    }
}

private fun resolveLithoRenderMethod(componentClass: Class<*>): Method? {
    return componentClass.declaredMethods.firstOrNull { method ->
        !Modifier.isStatic(method.modifiers) &&
            !method.isBridge &&
            !method.isSynthetic &&
            method.parameterCount == 1 &&
            !method.returnType.isPrimitive &&
            method.returnType != Void.TYPE &&
            method.returnType != Any::class.java &&
            method.returnType.isAssignableFrom(componentClass)
    }?.apply { isAccessible = true }
}

// ---------------------------------------------------------------------------
// Full-page sponsored Reels ads (576).
//
// The sponsored reel is an organic-shaped story (comments, reactions,
// follower social context) injected into the Reels feed, gated server-side
// ("reels_ads_ap_plus_newsfeed_qp"), so only some accounts see it. Its
// comment flyout is rendered by the ReelsAdsCaptionCommentComponent (found
// via the stable CallerContext string), whose construction site reveals the
// reels item model: field A04 (type C8Wm) is the ad model and is non-null
// only for ads — the structural "is this reel an ad" marker.
// ---------------------------------------------------------------------------

private val reelsAdDiagnosticsInstalled = AtomicInteger(0)
private val reelsAdDiagnosticsLogged = AtomicInteger(0)

private fun installReelsAdDiagnostics(classLoader: ClassLoader, bridge: DexKitBridge) {
    if (!reelsAdDiagnosticsInstalled.compareAndSet(0, 1)) return

    val componentClasses = LinkedHashMap<String, Class<*>>()
    bridge.findClass {
        matcher {
            usingStrings("ReelsAdsCaptionCommentComponent")
        }
    }.forEach { candidate ->
        val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
        componentClasses.putIfAbsent(clazz.name, clazz)
    }
    if (componentClasses.isEmpty()) {
        Log.w(TAG, "Reels ad caption component not found via string")
        return
    }

    componentClasses.values.forEach { clazz ->
        // Constructor: (FbUserSession, C8YW ad-model, C3PA) per C28D case 13.
        clazz.declaredConstructors.forEach { constructor ->
            if (constructor.parameterCount in 1..4) {
                constructor.isAccessible = true
                XposedBridge.hookMethod(constructor, object : XC_MethodHook() {
                    override fun afterHookedMethod(param: MethodHookParam) {
                        val count = reelsAdDiagnosticsLogged.incrementAndGet()
                        if (count > 60) return
                        val args = param.args.orEmpty().joinToString(" | ") { arg ->
                            "${arg?.javaClass?.name}:${formatDiagValue(arg)}"
                        }
                        Log.i(TAG, "ReelsAdDiag captionCtor ${clazz.name} args=[$args]")
                        param.thisObject?.let { describeReelsAdModelChain(it) }
                    }
                })
                Log.i(TAG, "Hooked Reels ad caption ctor ${clazz.name}")
            }
        }

        resolveLithoRenderMethod(clazz)?.let { render ->
            XposedBridge.hookMethod(render, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    val count = reelsAdDiagnosticsLogged.incrementAndGet()
                    if (count > 60) return
                    Log.i(
                        TAG,
                        "ReelsAdDiag captionRender ${clazz.name}.${render.name} " +
                            "this=${formatDiagValue(param.thisObject)} args=${formatDiagArgs(param.args)}"
                    )
                }
            })
            Log.i(TAG, "Hooked Reels ad caption render ${clazz.name}.${render.name}")
        }
    }

    installReelsAdPipelineProbes(classLoader, bridge)
    installReelsInstreamAdBlock(classLoader, bridge)
    installReelsAdListFilters(classLoader, bridge)
    Log.i(TAG, "Reels ad diagnostics installed components=${componentClasses.keys}")
}

// Block full-page Reels ads by forcing the instream eligibility gate to report
// "suppress ads". On 576 the gate (X.QNM.A00) is consulted at every decision
// point of the instream state machine (entry check, fetch trigger, fetch-result
// insertion) and a true result means "do not serve an ad" — early return,
// disabled state, or skipped insertion. The gate class is referenced only by
// the reels instream pipeline, so forcing it cannot affect other surfaces.
// Resolution is structural: an instance method returning boolean with exactly
// 5 parameters whose first is FbUserSession and last is int-Integer, on a tiny
// class that carries an ImmutableList cache field.
private fun installReelsInstreamAdBlock(classLoader: ClassLoader, bridge: DexKitBridge) {
    val userSessionClass = runCatching {
        Class.forName("com.facebook.auth.usersession.FbUserSession", false, classLoader)
    }.getOrNull() ?: run {
        Log.w(TAG, "Reels instream gate: FbUserSession class not found; skipping")
        return
    }
    val immutableListClass = runCatching {
        Class.forName("com.google.common.collect.ImmutableList", false, classLoader)
    }.getOrNull()

    val candidates = runCatching {
        bridge.findMethod {
            matcher {
                returnType = "boolean"
                paramTypes = listOf(
                    "com.facebook.auth.usersession.FbUserSession",
                    null,
                    null,
                    null,
                    "java.lang.Integer"
                )
            }
        }
    }.getOrNull().orEmpty()

    var blocked = 0
    candidates.forEach { methodData ->
        val method = runCatching { methodData.getMethodInstance(classLoader) }.getOrNull()
            ?: return@forEach
        if (Modifier.isStatic(method.modifiers)) return@forEach
        val clazz = method.declaringClass

        // The gate class declares exactly one such method on 576; anything with
        // more than one matching method is a different (shared) helper.
        val gateMethods = clazz.declaredMethods.filter { candidate ->
            !Modifier.isStatic(candidate.modifiers) &&
                candidate.returnType == java.lang.Boolean.TYPE &&
                candidate.parameterTypes.size == 5 &&
                candidate.parameterTypes.first() == userSessionClass &&
                candidate.parameterTypes.last() == java.lang.Integer::class.java
        }
        if (gateMethods.size != 1 || gateMethods[0] != method) return@forEach
        if (immutableListClass != null &&
            clazz.declaredFields.none { it.type == immutableListClass }
        ) return@forEach

        method.isAccessible = true
        XposedBridge.hookMethod(method, object : XC_MethodHook() {
            override fun beforeHookedMethod(param: MethodHookParam) {
                param.result = true
            }
        })
        blocked++
        Log.i(TAG, "Reels instream ad gate forced to suppress: ${clazz.name}.${method.name}")
    }
    if (blocked == 0) {
        Log.w(TAG, "Reels instream ad gate not resolved (candidates=${candidates.size})")
    }
}

// Server classification values that mark a reel item as an ad.
private val AD_CLASSIFICATION_VALUES = setOf("AD", "ADS_MIDCARD")

// Debug-only: renderables whose model carries a classification outside the
// blocklist (e.g. MIDCARD/PARADE/UGC) pass straight through the render block.
// Logging each (renderable, classification) pair once per session maps which
// classification the still-visible banner ads ride on.
private val reelsNonAdClassificationSeen: MutableSet<String> =
    Collections.synchronizedSet(HashSet())

// Server-injected full-page Reels ads: the ad item arrives inline in the reels
// feed response (and, for the client-vended variant, via the FbShorts
// sponsored pool) and renders straight from the item list without any ad fetch
// or story-pool insertion, so removal happens at the video-home data
// controller: the single A0K(List) choke point both feed paths push through,
// plus disabling the client-side insertion trigger and the sponsored pool fill.
private fun installReelsAdListFilters(classLoader: ClassLoader, bridge: DexKitBridge) {
    val classifier = resolveReelsAdClassifier(classLoader, bridge) ?: return
    Log.i(TAG, "Reels ad classifier resolved: ${classifier.describe()}")

    // 1. Data controller choke point: A0K(List<C76D>) — each wrapper's list
    //    field holds the InterfaceC190979h4 items pushed into the pager's UI
    //    collection. Filter ad items out of the nested lists.
    runCatching {
        bridge.findClass {
            matcher {
                usingStrings("VideoHomeDataControllerImpl.maybeInsertAds")
            }
        }.forEach { candidate ->
            val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
            clazz.declaredMethods.filter { method ->
                !Modifier.isStatic(method.modifiers) &&
                    method.returnType == java.lang.Boolean.TYPE &&
                    method.parameterTypes.size == 1 &&
                    List::class.java.isAssignableFrom(method.parameterTypes[0])
            }.forEach { method ->
                runCatching { hookReelsPagerListPush(method, classifier) }
                    .onFailure { Log.w(TAG, "Failed to hook reels pager push ${clazz.name}.${method.name}", it) }
            }
        }
    }.onFailure { Log.w(TAG, "Reels pager push resolution failed", it) }

    // 2. Client-side ad insertion trigger ("maybeInsertAds"): only no-op a
    //    controller insertion method. The same diagnostic string can be
    //    copied into unrelated telemetry helpers in later builds; a string
    //    match alone is unsafe.
    hookReelsMaybeInsertAds(classLoader, bridge)

    // 3. FbShorts sponsored pool fill ("after_model_added_to_pool"): only
    //    hook the three-argument pool add method with a boolean item classifier.
    hookReelsSponsoredPoolAdd(classLoader, bridge)

    // 4. Async RTI ad fetches: block at the fetch builders.
    installReelsRtiAdBlock(classLoader, bridge)

    // 5. The video-home item collection snapshot read: filter ads out of the
    //    collection itself, so every reader sees a sanitized list regardless
    //    of how or when an ad entered it (defeats the cold-start race where
    //    the reels CSR load lands before hook installation finishes).
    installReelsCollectionFilter(classLoader, bridge, classifier)

    // 6. The shorts viewer's own ad components: RTI ad data (whose fetch can
    //    fire before hook installation and whose response lands later) is
    //    rendered directly by dedicated components, bypassing the video-home
    //    collection. Block them at render time.
    installReelsViewerAdRenderBlock(classLoader, bridge, classifier)

    // 7. Diagnostics: capture stack traces when an ad is classified or the
    //    sponsored label renders, to expose any remaining delivery path.
    installReelsAdClassificationProbe(classLoader, bridge, classifier)
    installReelsSponsoredLabelProbe(classLoader, bridge, classifier)

    reelsFullPassInstalled.set(true)
}

// The shorts viewer renders server-injected full-page ads through dedicated
// ad components — the ad root component ("FbShortsAdsRootKComponent"), the
// real-time-intent section ("FbShortsAdsRealTimeIntentComponent"), and a
// sibling of the RTI section with no surviving string anchor (576: X.PWg) —
// fed directly by the RTI ad data, not by the video-home collection. Worse,
// some of these components carry no anchor strings at all, and every reels
// page (organic or ad) is ultimately built by the shared page component
// (576: X.Ad2), whose only ad marker is its ad-model-typed field. So besides
// the string anchors, every renderable class declaring a render method AND
// holding a field typed as the ad model interface is hooked: when such a
// component instance carries an ad-classified model (or an item list made
// only of ad items), its render is short-circuited to null, which Litho
// treats as "render nothing".
// The reels render block races the cold-start ad render (the full DexKit pass
// needs seconds; the reels UI renders within the first second). The resolved
// hook targets are therefore persisted (keyed by host and module version, like
// the feed guard cache) and re-installed within ~100ms of Application.attach
// on later launches. The hook registries are shared between the early cached
// install and the full DexKit pass so nothing is hooked twice.
private const val REELS_GUARD_CACHE_FILE = "fbar_reels_guard_cache.properties"

// Value-based on purpose: reflection hands out fresh Method copies on every
// lookup, so an identity-based set would let the early install re-hook the
// same methods on every retry (Method.equals compares declaring class, name
// and signature).
private val reelsRenderHookedMethods: MutableSet<Method> =
    Collections.synchronizedSet(HashSet())

// Snapshots are cached by the host until invalidated, so memoize filtered
// results by snapshot identity to keep the hot read path cheap. Shared across
// the cached and DexKit installs.
private val reelsSnapshotMemo = Collections.synchronizedMap(IdentityHashMap<Any, Any>())

// Hook targets recorded while the full DexKit pass installs, persisted for the
// next launch's early install. Renderables are plain class names (the hooked
// method is always "render"); the pager push and snapshot hooks are
// "class#method" specs.
private val reelsGuardRenderableNames = Collections.synchronizedList(ArrayList<String>())

// Shoppable-card components blocked unconditionally by string anchor; tracked
// separately from the ad renderables so the cached early install can hook them
// without needing the ad classifier.
private val reelsShoppingRenderableNames = Collections.synchronizedList(ArrayList<String>())
private val reelsGuardPagerPushSpecs = Collections.synchronizedList(ArrayList<String>())
private val reelsGuardSnapshotSpecs = Collections.synchronizedList(ArrayList<String>())

@Volatile
private var reelsGuardModelInterfaceSpecs: List<String> = emptyList()

@Volatile
private var reelsGuardEnumClassName: String = ""

private fun installReelsViewerAdRenderBlock(
    classLoader: ClassLoader,
    bridge: DexKitBridge,
    classifier: ReelsAdClassifier
) {
    val anchors = listOf(
        "FbShortsAdsRootKComponent" to "Reels viewer ad component blocked",
        "FbShortsAdsRealTimeIntentComponent" to "Reels RTI ad component blocked"
    )
    for ((anchor, label) in anchors) {
        runCatching {
            bridge.findClass {
                matcher {
                    usingStrings(anchor)
                }
            }.forEach { candidate ->
                val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
                hookReelsAdRenderable(clazz, classifier, reelsRenderHookedMethods, label)
            }
        }.onFailure { Log.w(TAG, "$label failed", it) }
    }

    // Shoppable product cards (the small "Shop now" banner overlaying a reel):
    // unlike the ad renderables above, these hold a shopping product payload,
    // not an ad-classified model, so they are blocked unconditionally — the
    // components exist solely to render the shopping card. The string anchors
    // only bootstrap the discovery: their shared non-framework field type is
    // the shopping payload class, and a structural pass then catches every
    // renderable holding it (banner card, marketplace card, hscroll items...).
    val shoppingAnchors = listOf(
        "FbShortsShoppableProductItemComponent",
        "FbShortsShoppableAdsItemComponent",
        "FbShortsShoppableMarketplaceCardComponent"
    )
    val shoppingAnchorClasses = ArrayList<Class<*>>()
    for (anchor in shoppingAnchors) {
        runCatching {
            bridge.findClass {
                matcher {
                    usingStrings(anchor)
                }
            }.forEach { candidate ->
                val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
                shoppingAnchorClasses.add(clazz)
            }
        }.onFailure { Log.w(TAG, "Reels shopping card block failed for $anchor", it) }
    }
    val shoppingPayloadType = resolveShoppingPayloadType(shoppingAnchorClasses)
    // Anchor strings identify the feature, but a class containing the string
    // can be a factory or a parent component. Resolve the payload first and
    // only block a render when that instance actually carries a product model.
    shoppingAnchorClasses.distinctBy { it.name }.forEach { clazz ->
        hookReelsShoppingRenderable(
            clazz,
            reelsRenderHookedMethods,
            "Reels shopping card blocked",
            shoppingPayloadType
        )
    }
    if (shoppingPayloadType != null) {
        runCatching {
            val matches = bridge.findClass {
                matcher {
                    addFieldForType(shoppingPayloadType)
                    addMethod { name("render") }
                }
            }
            for (candidate in matches) {
                val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: continue
                hookReelsShoppingRenderable(
                    clazz,
                    reelsRenderHookedMethods,
                    "Reels shopping card blocked (structural)",
                    shoppingPayloadType
                )
            }
            Log.i(TAG, "Reels shopping renderables for ${shoppingPayloadType.name}: ${matches.size}")
        }.onFailure { Log.w(TAG, "Reels shopping structural pass failed", it) }
    } else {
        Log.w(TAG, "Reels shopping payload type not resolved from ${shoppingAnchorClasses.size} anchors")
    }

    // Structural pass: renderables with an ad-model-typed field. This covers
    // the ad components without string anchors and the shared page component.
    for (modelInterface in classifier.modelInterfaceClasses) {
        runCatching {
            val matches = bridge.findClass {
                matcher {
                    addFieldForType(modelInterface)
                    addMethod { name("render") }
                }
            }
            for (candidate in matches) {
                val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: continue
                hookReelsAdRenderable(clazz, classifier, reelsRenderHookedMethods, "Reels ad renderable (structural)")
            }
            Log.i(TAG, "Reels structural renderables for ${modelInterface.name}: ${matches.size}")
        }.onFailure { Log.w(TAG, "Reels structural renderable resolution failed for ${modelInterface.name}", it) }
    }
}

private fun hookReelsAdRenderable(
    clazz: Class<*>,
    classifier: ReelsAdClassifier,
    hookedRenderMethods: MutableSet<Method>,
    label: String
) {
    val render = clazz.declaredMethods.firstOrNull {
        it.name == "render" && !Modifier.isStatic(it.modifiers)
    } ?: return
    if (!hookedRenderMethods.add(render)) return
    reelsGuardRenderableNames.add(clazz.name)
    val modelFields = clazz.declaredFields.filter { field ->
        !Modifier.isStatic(field.modifiers) && classifier.isModelType(field.type)
    }.onEach { it.isAccessible = true }
    val listFields = clazz.declaredFields.filter { field ->
        !Modifier.isStatic(field.modifiers) &&
            Iterable::class.java.isAssignableFrom(field.type)
    }.onEach { it.isAccessible = true }
    render.isAccessible = true
    XposedBridge.hookMethod(render, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val target = param.thisObject ?: return
            for (field in modelFields) {
                val model = runCatching { field.get(target) }.getOrNull() ?: continue
                val classification = classifier.modelClassification(model)
                if (classification in AD_CLASSIFICATION_VALUES) {
                    param.result = null
                    logHookHitThrottled(
                        "reelsViewerAdRenderBlock",
                        render,
                        "model=${model.javaClass.simpleName}"
                    )
                    return
                }
                if (classification != null && BuildConfig.DEBUG) {
                    val seenKey = "${clazz.name}=$classification"
                    if (reelsNonAdClassificationSeen.add(seenKey)) {
                        Log.i(
                            TAG,
                            "Reels renderable passthrough ${clazz.name} " +
                                "model=${model.javaClass.simpleName} classification=$classification"
                        )
                    }
                }
            }
            // Only block on an item list when every classifiable item in it is
            // an ad — a mixed list belongs to a component that also renders
            // organic reels and must not be blanked.
            for (field in listFields) {
                val items = runCatching { field.get(target) }.getOrNull() as? Iterable<*> ?: continue
                var anyAd = false
                var anyNonAd = false
                for (item in items) {
                    when (classifier.classificationOf(item)) {
                        in AD_CLASSIFICATION_VALUES -> anyAd = true
                        null -> {}
                        else -> anyNonAd = true
                    }
                }
                if (anyAd && !anyNonAd) {
                    param.result = null
                    logHookHitThrottled(
                        "reelsViewerAdRenderBlock",
                        render,
                        "adList=${field.name}"
                    )
                    return
                }
            }
        }
    })
    Log.i(
        TAG,
        "$label: ${clazz.name}.render modelFields=${modelFields.size} listFields=${listFields.size}"
    )
}

// Derives the shoppable product payload class from the anchor components: the
// non-framework field type shared by every anchored renderable (their product
// payload holder). Anchors may individually lack the field, so any class that
// shares the majority type wins.
private fun resolveShoppingPayloadType(anchorClasses: List<Class<*>>): Class<*>? {
    // Count distinct anchor classes, not fields. A generated component can
    // carry the same value twice; that must not make an unrelated type win.
    val ownersByType = LinkedHashMap<Class<*>, MutableSet<Class<*>>>()
    anchorClasses.distinctBy { it.name }.forEach { clazz ->
        clazz.declaredFields
            .filter { !Modifier.isStatic(it.modifiers) }
            .forEach { field ->
                if (isLikelyShoppingPayloadType(field.type)) {
                    ownersByType.getOrPut(field.type) { LinkedHashSet() }.add(clazz)
                }
            }
    }
    return ownersByType.entries
        .filter { (_, owners) -> owners.size >= 2 }
        .maxWithOrNull(
            compareBy<Map.Entry<Class<*>, MutableSet<Class<*>>>> { it.value.size }
                .thenBy { it.key.declaredFields.size }
        )?.key
}

private fun isLikelyShoppingPayloadType(type: Class<*>): Boolean {
    if (type.isPrimitive || type.isEnum || type.isInterface || type.isArray) return false
    if (type.name.startsWith("java.") || type.name.startsWith("android.")) return false
    val fields = type.declaredFields.filter { !Modifier.isStatic(it.modifiers) }
    if (fields.size < 8) return false
    val stringFields = fields.count { it.type == String::class.java }
    val scalarFields = fields.count {
        it.type.isPrimitive ||
            Number::class.java.isAssignableFrom(it.type) ||
            it.type == Boolean::class.java
    }
    return stringFields >= 2 && scalarFields >= 2
}

// Render block for shoppable product cards. The payload check keeps shared
// generated components safe when their optional product field is null. Shares
// the hooked-methods set so cached and full installs never double-hook.
private fun hookReelsShoppingRenderable(
    clazz: Class<*>,
    hookedRenderMethods: MutableSet<Method>,
    label: String,
    payloadType: Class<*>? = null
) {
    val render = resolveLithoRenderMethod(clazz) ?: clazz.declaredMethods.firstOrNull {
        it.name == "render" &&
            !Modifier.isStatic(it.modifiers) &&
            !it.isBridge &&
            !it.isSynthetic &&
            it.parameterCount == 1 &&
            !it.returnType.isPrimitive &&
            it.returnType != Void.TYPE
    } ?: return
    val payloadFields = clazz.declaredFields.filter { field ->
        !Modifier.isStatic(field.modifiers) &&
            (payloadType?.let { field.type == it } ?: isLikelyShoppingPayloadType(field.type))
    }.onEach { it.isAccessible = true }
    if (payloadFields.isEmpty()) return
    if (!hookedRenderMethods.add(render)) return
    reelsShoppingRenderableNames.add(clazz.name)
    render.isAccessible = true
    XposedBridge.hookMethod(render, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val target = param.thisObject ?: return
            // Product fields are optional on several shared generated
            // components. Returning null while the field is empty blanks an
            // organic Reels page, which was the intermittent black-screen
            // failure. Suppress only a real product-card instance.
            if (payloadFields.none { runCatching { it.get(target) }.getOrNull() != null }) return
            param.result = null
            logHookHitThrottled("reelsShoppingCardBlock", render, "")
        }
    })
    Log.i(TAG, "$label: ${clazz.name}.${render.name} payloadFields=${payloadFields.size}")
}

// Marketplace sponsored units (seller row + "Sponsored" label + video card) in
// the home feed are rendered by Litho components that carry stable "Marketplace
// …Ads…" strings: the query-fetched fallback card ("MarketplaceVideoAdQuery"),
// the Litho wrapper that mounts the ad card content
// ("MarketplaceVideoAdsComponent"), and the ad video layout
// ("MarketplaceVideoAdsGrootLayoutSpec"). Blocking their render/layout methods
// to null makes Litho skip the whole unit. The ads themselves are fetched by a
// Relay query whose name only exists in the JS bundle, so render time is the
// earliest reliable native interception point.
private val marketplaceAdRenderHookedMethods: MutableSet<Method> =
    Collections.synchronizedSet(HashSet())

private fun installMarketplaceAdRenderBlock(classLoader: ClassLoader, bridge: DexKitBridge) {
    val anchors = listOf(
        "MarketplaceVideoAdQuery",
        "MarketplaceVideoAdsComponent",
        "MarketplaceVideoAdsGrootLayoutSpec"
    )
    for (anchor in anchors) {
        runCatching {
            val matches = bridge.findClass {
                matcher {
                    usingStrings(anchor)
                }
            }
            for (candidate in matches) {
                val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: continue
                hookMarketplaceAdRenderable(clazz, marketplaceAdRenderHookedMethods, "Marketplace ad component blocked")
            }
            Log.i(TAG, "Marketplace ad renderables for $anchor: ${matches.size}")
        }.onFailure { Log.w(TAG, "Marketplace ad render block failed for $anchor", it) }
    }
}

private fun hookMarketplaceAdRenderable(
    clazz: Class<*>,
    hookedMethods: MutableSet<Method>,
    label: String
) {
    // The query-fetched card is a plain renderable (render(SectionContext));
    // the other two are Litho layout components whose method names are
    // obfuscated but whose shape is stable: exactly one non-primitive
    // parameter (the Litho component context) and a non-primitive return
    // (the component tree). Hooking that shape only matches the layout entry
    // point — lifecycle hooks (onCreateLayout's 2-param variants, void
    // attach/detach) are excluded.
    val targets = clazz.declaredMethods.filter { method ->
        !Modifier.isStatic(method.modifiers) && !method.isSynthetic && (
            method.name == "render" ||
                (
                    method.parameterCount == 1 &&
                        !method.parameterTypes[0].isPrimitive &&
                        method.returnType != Void.TYPE &&
                        !method.returnType.isPrimitive
                    )
            )
    }
    var hooked = 0
    for (method in targets) {
        if (!hookedMethods.add(method)) continue
        method.isAccessible = true
        XposedBridge.hookMethod(method, object : XC_MethodHook() {
            override fun beforeHookedMethod(param: MethodHookParam) {
                param.result = null
                logHookHitThrottled("marketplaceAdRenderBlock", method, "")
            }
        })
        hooked++
    }
    if (hooked > 0) {
        Log.i(TAG, "$label: ${clazz.name} methods=$hooked")
    }
}

// Marketplace home-feed sponsored tiles are fetched by dedicated Relay queries
// ("RelayFBNetwork_MarketplaceHomeFeedAdsQueryRendererQuery",
// "...MarketplaceHomeFeedAdsPaginationQuery",
// "...MarketplaceHomeFeedBoostedListingAds[...Pagination]Query") issued
// through the React Native Networking module. The query name is embedded in
// the POST body, so requests carrying it are dropped entirely: the RN
// QueryRenderer never receives data and keeps rendering its loading fallback
// (nothing), which removes the whole sponsored tile. The Networking module is
// found by its stable request-context string; its sendRequest method keeps the
// RN-native name because JS invokes it reflectively by name.
private fun installMarketplaceAdsQueryBlock(classLoader: ClassLoader, bridge: DexKitBridge) {
    runCatching {
        val matches = bridge.findClass {
            matcher {
                usingStrings("FBNetworkingModule_React_Native")
            }
        }
        var installed = 0
        for (candidate in matches) {
            val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: continue
            val sendRequest = clazz.declaredMethods.firstOrNull { method ->
                method.name == "sendRequest" && method.parameterCount == 9
            } ?: continue
            if (hookMarketplaceSendRequest(sendRequest)) {
                installed++
                marketplaceNetResolvedClassName = clazz.name
            }
        }
        Log.i(TAG, "Marketplace ads query block installed on $installed Networking module(s)")
    }.onFailure { Log.w(TAG, "Marketplace ads query block failed", it) }
}

// Hooks already installed on these methods (the early cached install and the
// full DexKit pass resolve the same method object; hooking twice would run the
// rewrite/block logic twice per request).
private val marketplaceSendRequestHookedMethods: MutableSet<Method> =
    Collections.synchronizedSet(HashSet())

// The Networking module class resolved by the last successful install; cached
// so later launches can re-install the hook before the marketplace renderer
// query fires (the cold-start race: the feed query goes out ~3s after launch,
// before the DexKit scan finishes).
@Volatile
private var marketplaceNetResolvedClassName: String? = null

private fun hookMarketplaceSendRequest(sendRequest: Method): Boolean {
    if (!marketplaceSendRequestHookedMethods.add(sendRequest)) return false
    sendRequest.isAccessible = true
    XposedBridge.hookMethod(sendRequest, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    val body = requestBodyOf(param.args.getOrNull(4)) ?: return
                    val name = marketplaceQueryNameRegex.find(body)?.groupValues?.get(1)
                        ?: marketplaceFormQueryIdRegex.find(body)?.groupValues?.get(1)
                        ?: "persisted"
                    if (BuildConfig.DEBUG) {
                        val url = param.args.getOrNull(1) as? String ?: ""
                        if (marketplaceDiagnosedQueries.add("req:$url|$name")) {
                            Log.i(TAG, "RN request url=$url query=$name len=${body.length}")
                        }
                    }
                    // The marketplace home feed queries (initial renderer and
                    // scroll pagination) mix sponsored tiles into the organic
                    // grid. The persisted-query config exposes server-honoured
                    // skip flags, so rewriting the request variables makes the
                    // server omit the ads entirely instead of trying to strip
                    // them from a chunked incremental response.
                    if (name == "MarketplaceHomeFeedQueryRendererQuery" ||
                        name == "MarketplaceHomeFeedPaginationQuery"
                    ) {
                        val rewritten = rewriteMarketplaceFeedRequestVariables(body)
                        if (rewritten != null) {
                            val replacement = readableMapWithString(param.args.getOrNull(4), rewritten)
                            if (replacement != null) {
                                param.args[4] = replacement
                                logHookHitThrottled("marketplaceFeedAdSkip", sendRequest, "")
                            } else if (BuildConfig.DEBUG) {
                                Log.w(TAG, "Could not build replacement ReadableMap for feed request")
                            }
                        }
                        return
                    }
                    if (!body.contains("MarketplaceHomeFeedAds") &&
                        !body.contains("MarketplaceHomeFeedBoostedListingAds") &&
                        !body.contains("MarketplaceHomeFeedThemedAds")
                    ) {
                        return
                    }
                    param.result = null
                    logHookHitThrottled("marketplaceAdsQueryBlock", sendRequest, "")
                }
    })
    return true
}

// The marketplace feed query fires within seconds of launch — before the
// DexKit scan installs the main hooks (the same cold-start race as the cached
// News Feed) — so the resolved Networking module class name is persisted and
// re-hooked right after Application.attach on later launches. The class name
// is obfuscated per build, but it is discovered at runtime and cached keyed by
// the Facebook version, never hardcoded.
private const val MARKETPLACE_NET_CACHE_FILE = "fbar_marketplace_net_cache.properties"

fun saveMarketplaceNetGuardCache(context: Context, hostVersionName: String) {
    val className = marketplaceNetResolvedClassName ?: return
    if (hostVersionName.isBlank()) return
    runCatching {
        val file = File(context.cacheDir, MARKETPLACE_NET_CACHE_FILE)
        val properties = Properties()
        properties.setProperty("version", hostVersionName)
        properties.setProperty("moduleVersion", feedGuardCacheModuleKey())
        properties.setProperty("networkingModule", className)
        file.outputStream().use { properties.store(it, null) }
        Log.i(TAG, "Saved marketplace net guard cache networkingModule=$className")
    }.onFailure {
        Log.w(TAG, "Failed to save marketplace net guard cache", it)
    }
}

// Returns true when the cached Networking module was loaded and hooked. Fails
// softly (false) while the secondary dex is not yet configured, so callers can
// retry on a timer.
fun installMarketplaceNetGuardFromCache(
    context: Context,
    classLoader: ClassLoader,
    hostVersionName: String
): Boolean {
    if (hostVersionName.isBlank()) return false
    return runCatching {
        val file = File(context.cacheDir, MARKETPLACE_NET_CACHE_FILE)
        if (!file.exists()) return false
        val properties = Properties()
        file.inputStream().use { properties.load(it) }
        if (hostVersionName != properties.getProperty("version")) return false
        if (feedGuardCacheModuleKey() != properties.getProperty("moduleVersion")) return false
        val className = properties.getProperty("networkingModule").orEmpty()
        if (className.isBlank()) return false
        val clazz = Class.forName(className, false, classLoader)
        val sendRequest = clazz.declaredMethods.firstOrNull { method ->
            method.name == "sendRequest" && method.parameterCount == 9
        } ?: return false
        val hooked = hookMarketplaceSendRequest(sendRequest)
        if (hooked) {
            Log.i(TAG, "Marketplace net guard installed from cache on $className")
        }
        hooked
    }.onFailure {
        false
    }.getOrDefault(false)
}

// The RN Networking module receives its POST body as a ReadableMap with a
// "string" key. ReadableMap is a host interface, so read it reflectively.
private fun requestBodyOf(data: Any?): String? {
    if (data == null) return null
    val hasKey = data.javaClass.methods.firstOrNull {
        it.name == "hasKey" && it.parameterCount == 1
    } ?: return null
    val getString = data.javaClass.methods.firstOrNull {
        it.name == "getString" && it.parameterCount == 1
    } ?: return null
    return runCatching {
        if (hasKey.invoke(data, "string") != true) {
            return@runCatching null
        }
        getString.invoke(data, "string") as? String
    }.getOrNull()
}

// The marketplace home feed request body is form-encoded. Its "variables"
// parameter is URL-encoded JSON whose schema (from the persisted query config
// asset) includes server-honoured ad-skip flags. Flipping them to true makes
// the server omit sponsored tiles from the response instead of the module
// having to strip them out of a chunked incremental payload. Returns null when
// the body has no variables to rewrite.
private fun rewriteMarketplaceFeedRequestVariables(body: String): String? {
    val marker = "variables="
    val markerIndex = body.indexOf(marker)
    if (markerIndex < 0) return null
    val valueStart = markerIndex + marker.length
    val valueEnd = body.indexOf('&', valueStart).let { if (it < 0) body.length else it }
    val encoded = body.substring(valueStart, valueEnd)
    val decoded = runCatching { URLDecoder.decode(encoded, "UTF-8") }.getOrNull() ?: return null
    var changed = false
    var variables: JSONObject? = null
    try {
        variables = JSONObject(decoded)
        for (flag in MARKETPLACE_FEED_AD_SKIP_FLAGS) {
            if (variables.optBoolean(flag, false)) continue
            variables.put(flag, true)
            changed = true
        }
    } catch (throwable: Throwable) {
        if (BuildConfig.DEBUG) {
            Log.w(TAG, "Failed to parse marketplace feed variables", throwable)
        }
        return null
    }
    if (!changed) return null
    val rewritten = URLEncoder.encode(variables.toString(), "UTF-8")
    return body.substring(0, valueStart) + rewritten + body.substring(valueEnd)
}

private val MARKETPLACE_FEED_AD_SKIP_FLAGS = listOf(
    "shouldSkipAdRequest",
    "shouldSkipBoostedListingAdRequest",
)

// Builds a replacement ReadableMap body for the RN Networking module. The
// module and its same-origin delegate read the body only through
// hasKey/getString/getType, so any ReadableMap implementation works; the RN
// bridge's WritableNativeMap is public API with a no-arg constructor and
// putString(String, String).
private fun readableMapWithString(original: Any?, body: String): Any? {
    if (original == null) return null
    return runCatching {
        // Resolve through the host classloader (the original body map's), not
        // the module's own.
        val mapClass = original.javaClass.classLoader
            .loadClass("com.facebook.react.bridge.WritableNativeMap")
        val instance = mapClass.getDeclaredConstructor().newInstance()
        val putString = mapClass.methods.firstOrNull {
            it.name == "putString" &&
                it.parameterCount == 2 &&
                it.parameterTypes[0] == String::class.java &&
                it.parameterTypes[1] == String::class.java
        } ?: return@runCatching null
        putString.invoke(instance, "string", body)
        instance
    }.getOrNull()
}

// Correlates marketplace diagnostics across a session while diagnosing where
// the marketplace feed payload actually flows.
private val marketplaceDiagnosedQueries: MutableSet<String> =
    Collections.synchronizedSet(HashSet())
private val marketplaceQueryNameRegex = Regex("query[\\s]+([A-Za-z0-9_]+)")
// Persisted Relay requests are form-encoded and carry the readable query
// name in fb_api_req_friendly_name plus a numeric doc_id.
private val marketplaceFormQueryIdRegex = Regex("fb_api_req_friendly_name=([A-Za-z0-9_]+)")

// The RN Networking module hands every response body to JavaScript through the
// static emitters of one class (found via its stable "didReceiveNetworkData"
// event string): the text path, the base64/byte[] path, and the incremental
// path. Feed responses are chunked through the incremental path, so reliably
// rewriting the payload there requires reassembling chunks across calls.
private fun installMarketplaceFeedResponseFilter(classLoader: ClassLoader, bridge: DexKitBridge) {
    runCatching {
        val matches = bridge.findClass {
            matcher {
                usingStrings("didReceiveNetworkData")
            }
        }
        var installed = 0
        for (candidate in matches) {
            val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: continue
            for (method in clazz.declaredMethods) {
                if (!java.lang.reflect.Modifier.isStatic(method.modifiers)) continue
                if (method.returnType != Void.TYPE) continue
                val params = method.parameterTypes
                val incrementalEmitter = params.size == 6 &&
                    params[1] == String::class.java &&
                    params[2] == String::class.java &&
                    params[3] == Int::class.javaPrimitiveType &&
                    params[4] == Long::class.javaPrimitiveType &&
                    params[5] == Long::class.javaPrimitiveType
                if (!incrementalEmitter) continue
                method.isAccessible = true
                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        if (!BuildConfig.DEBUG) return
                        val body = param.args.getOrNull(2) as? String ?: return
                        if (!body.contains("ponsored")) return
                        // Diagnostic capture: write sponsored-bearing chunks to
                        // the host cache dir (logcat's ring buffer is too small
                        // for ~120KB bodies).
                        runCatching {
                            val context = param.args.getOrNull(0) as? Context ?: return
                            val dir = File(context.cacheDir, "mp_probe")
                            dir.mkdirs()
                            val file = File(dir, "chunk_${System.currentTimeMillis()}.json")
                            file.writeText(body)
                            Log.i(TAG, "MP-CHUNK captured len=${body.length} file=${file.name}")
                        }
                    }
                })
                installed++
                Log.i(TAG, "Marketplace response probe installed on ${clazz.name}.$method")
            }
        }
        Log.i(TAG, "Marketplace response probe installed on $installed emitter(s)")
    }.onFailure { Log.w(TAG, "Marketplace response probe failed", it) }
}

// The video-home item collection (576: X.4zE) is read exclusively through a
// static snapshot method that returns an ImmutableList copy of the current
// items (with copy-on-write caching). Every consumer — the reels pager, the
// adapter, the Litho sections — sees the collection through that snapshot, so
// filtering it removes ad items from all views at once. This catches ads that
// entered the collection through ANY path, including CSR loads that completed
// before the module's hooks were installed (the cold-start race).
private fun installReelsCollectionFilter(
    classLoader: ClassLoader,
    bridge: DexKitBridge,
    classifier: ReelsAdClassifier
) {
    runCatching {
        bridge.findClass {
            matcher {
                usingStrings("videohome_insert_index_out_of_bounds")
            }
        }.forEach { candidate ->
            val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
            val snapshotMethods = clazz.declaredMethods.filter { method ->
                Modifier.isStatic(method.modifiers) &&
                    List::class.java.isAssignableFrom(method.returnType) &&
                    method.parameterTypes.size == 1 &&
                    method.parameterTypes[0] == clazz
            }
            if (snapshotMethods.isEmpty()) {
                Log.w(TAG, "Reels collection snapshot method not found on ${clazz.name}")
                return@forEach
            }
            snapshotMethods.forEach { method ->
                hookReelsCollectionSnapshot(method, classifier)
            }
        }
    }.onFailure { Log.w(TAG, "Reels collection filter failed", it) }
}

private fun hookReelsCollectionSnapshot(method: Method, classifier: ReelsAdClassifier) {
    method.isAccessible = true
    reelsGuardSnapshotSpecs.add("${method.declaringClass.name}#${method.name}")
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun afterHookedMethod(param: MethodHookParam) {
            if (param.throwable != null) return
            val snapshot = param.result as? List<*> ?: return
            val cached = reelsSnapshotMemo[snapshot]
            if (cached != null) {
                param.result = cached
                return
            }
            val kept = ArrayList<Any?>(snapshot.size)
            var removed = 0
            for (item in snapshot) {
                val classification = classifier.classificationOf(item)
                if (classification != null && classification in AD_CLASSIFICATION_VALUES) {
                    removed++
                } else {
                    kept.add(item)
                }
            }
            if (removed == 0) {
                reelsSnapshotMemo[snapshot] = snapshot
                return
            }
            val rebuilt = buildImmutableListLike(
                snapshot,
                kept,
                method.declaringClass.classLoader
            )
            if (rebuilt != null) {
                reelsSnapshotMemo[snapshot] = rebuilt
                param.result = rebuilt
                logHookHitThrottled(
                    "reelsCollectionFilter",
                    method,
                    "size=${snapshot.size} filtered=$removed kept=${kept.size}"
                )
            }
        }
    })
    Log.i(TAG, "Hooked Reels collection ad filter at ${method.declaringClass.name}.${method.name}")
}

private val reelsClassificationProbeHits = AtomicInteger(0)
private val reelsSponsoredLabelHits = AtomicInteger(0)

// Diagnostic probe: whenever a reel media model is classified as an ad, log
// the classification plus the call stack. Ads that bypass every known
// pipeline reveal themselves here — whoever renders or processes the ad item
// has to read its classification.
private fun installReelsAdClassificationProbe(
    classLoader: ClassLoader,
    bridge: DexKitBridge,
    classifier: ReelsAdClassifier
) {
    runCatching {
        bridge.findMethod {
            matcher {
                returnType = classifier.enumClassName
                paramCount = 0
            }
        }.forEach { methodData ->
            val method = runCatching { methodData.getMethodInstance(classLoader) }.getOrNull()
                ?: return@forEach
            if (Modifier.isStatic(method.modifiers) || method.declaringClass.isInterface) return@forEach
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun afterHookedMethod(param: MethodHookParam) {
                    if (param.throwable != null) return
                    val value = param.result?.toString() ?: return
                    if (value !in AD_CLASSIFICATION_VALUES) return
                    val hits = reelsClassificationProbeHits.incrementAndGet()
                    if (hits > 12) return
                    val stack = Throwable().stackTrace.take(20)
                        .joinToString(" <- ") { "${it.className}.${it.methodName}" }
                    Log.i(
                        TAG,
                        "ReelsAdDiag classified=$value hits=$hits at " +
                            "${method.declaringClass.name}.${method.name} stack=$stack"
                    )
                }
            })
        }
    }.onFailure { Log.w(TAG, "Reels ad classification probe failed", it) }
}

// Diagnostic probe: the sponsored label component ("FbShortsAdsSponsoredLabel
// Component") is constructed only for ad items, so its constructor is a
// reliable render-time signal. Logs its ad model and the call stack.
private fun installReelsSponsoredLabelProbe(
    classLoader: ClassLoader,
    bridge: DexKitBridge,
    classifier: ReelsAdClassifier
) {
    runCatching {
        bridge.findClass {
            matcher {
                usingStrings("FbShortsAdsSponsoredLabelComponent")
            }
        }.forEach { candidate ->
            val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
            clazz.declaredConstructors.forEach { ctor ->
                runCatching {
                    ctor.isAccessible = true
                    XposedBridge.hookMethod(ctor, object : XC_MethodHook() {
                        override fun afterHookedMethod(param: MethodHookParam) {
                            val hits = reelsSponsoredLabelHits.incrementAndGet()
                            if (hits > 6) return
                            val argInfo = param.args.joinToString(",") { arg ->
                                classifier.modelClassification(arg)?.let { cls ->
                                    "${arg?.javaClass?.simpleName}=$cls"
                                } ?: arg?.javaClass?.simpleName ?: "null"
                            }
                            val stack = Throwable().stackTrace.take(20)
                                .joinToString(" <- ") { "${it.className}.${it.methodName}" }
                            Log.i(TAG, "ReelsAdDiag sponsoredLabel hits=$hits args=[$argInfo] stack=$stack")
                        }
                    })
                    Log.i(TAG, "Hooked Reels sponsored label ctor ${clazz.name}")
                }
            }
        }
    }.onFailure { Log.w(TAG, "Reels sponsored label probe failed", it) }
}

// Async RTI (real-time intent) Reels ads: while watching organic reels, the
// viewer's FbShortsRealTimeIntentAdsDataController (576: X.50U) proactively
// requests a fresh ad from the server ("async_ads_request_type" =
// "IMMERSIVE_REAL_TIME_INTENT", plus the POE/post-roll interstitial variant)
// and injects the response's AD-classified items into the pager as full-page
// ads. These fetches run outside the gated instream pipeline entirely, so they
// are blocked at their builders: the Function0.invoke() methods that assemble
// the GraphQL request are no-op'd (their return value is discarded — they run
// through a Runnable SAM), so the ad response never arrives. This also covers
// the impRecord "INTERSTITIAL_N" ads, which come from the POE variant.
private fun installReelsRtiAdBlock(classLoader: ClassLoader, bridge: DexKitBridge) {
    val targets = listOf(
        "IMMERSIVE_REAL_TIME_INTENT" to "Reels RTI ad fetch blocked",
        "POE_TRIGGERED_INTERSTITIAL" to "Reels POE interstitial fetch blocked"
    )
    for ((needle, label) in targets) {
        runCatching {
            bridge.findMethod {
                matcher {
                    usingStrings(needle)
                }
            }.forEach { methodData ->
                val method = runCatching { methodData.getMethodInstance(classLoader) }.getOrNull()
                    ?: return@forEach
                if (!isReelsRtiFunctionMethod(method)) return@forEach
                method.isAccessible = true
                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        param.result = null
                    }
                })
                Log.i(TAG, "$label: ${method.declaringClass.name}.${method.name}")
            }
        }.onFailure { Log.w(TAG, "$label resolution failed", it) }
    }
}

private fun isReelsRtiFunctionMethod(method: Method): Boolean {
    if (Modifier.isStatic(method.modifiers) || method.parameterCount != 0) return false
    if (method.name != "invoke" || method.returnType == Void.TYPE) return false
    // The RTI request builders are Kotlin Function0 lambdas. Restricting the
    // hook to that immutable contract prevents a zero-argument helper that
    // happens to carry the request marker from being replaced with null.
    return implementsInterface(method.declaringClass, "kotlin.jvm.functions.Function0")
}

private fun implementsInterface(type: Class<*>, interfaceName: String): Boolean {
    val pending = ArrayDeque<Class<*>>()
    val seen = HashSet<Class<*>>()
    pending.add(type)
    while (pending.isNotEmpty()) {
        val current = pending.removeFirst()
        if (!seen.add(current)) continue
        if (current.name == interfaceName) return true
        current.interfaces.forEach { pending.addLast(it) }
        current.superclass?.let { pending.addLast(it) }
    }
    return false
}

private fun hookReelsMaybeInsertAds(
    classLoader: ClassLoader,
    bridge: DexKitBridge
) {
    runCatching {
        bridge.findMethod {
            matcher { usingStrings("VideoHomeDataControllerImpl.maybeInsertAds") }
        }.forEach { methodData ->
            val method = runCatching { methodData.getMethodInstance(classLoader) }.getOrNull()
                ?: return@forEach
            if (!isReelsMaybeInsertAdsMethod(method)) return@forEach
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    param.result = null
                }
            })
            Log.i(TAG, "Reels client-side ad insertion disabled: ${methodSignature(method)}")
        }
    }.onFailure { Log.w(TAG, "Reels client-side ad insertion resolution failed", it) }
}

private fun isReelsMaybeInsertAdsMethod(method: Method): Boolean {
    if (Modifier.isStatic(method.modifiers) || method.returnType != Void.TYPE) return false
    val params = method.parameterTypes
    if (params.size !in 1..3) return false
    val hasPosition = params.any { type ->
        type == Int::class.javaPrimitiveType ||
            type == Long::class.javaPrimitiveType ||
            type == Integer::class.java ||
            type == Long::class.java
    }
    val hasCandidate = params.any { type ->
        !type.isPrimitive &&
            type != String::class.java &&
            !List::class.java.isAssignableFrom(type) &&
            !Map::class.java.isAssignableFrom(type)
    }
    if (!hasPosition || !hasCandidate) return false
    // The controller also exposes a numeric eligibility gate. Requiring this
    // sibling shape keeps diagnostic helpers with the same marker untouched.
    return method.declaringClass.declaredMethods.any { sibling ->
        !Modifier.isStatic(sibling.modifiers) &&
            sibling.returnType == Boolean::class.javaPrimitiveType &&
            sibling.parameterCount == 1 &&
            (sibling.parameterTypes[0] == Int::class.javaPrimitiveType ||
                sibling.parameterTypes[0] == Integer::class.java)
    }
}

private fun hookReelsSponsoredPoolAdd(
    classLoader: ClassLoader,
    bridge: DexKitBridge
) {
    runCatching {
        bridge.findMethod {
            matcher { usingStrings("after_model_added_to_pool") }
        }.forEach { methodData ->
            val method = runCatching { methodData.getMethodInstance(classLoader) }.getOrNull()
                ?: return@forEach
            if (!isReelsSponsoredPoolAddMethod(method)) return@forEach
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    param.result = null
                }
            })
            Log.i(TAG, "Reels sponsored pool fill disabled: ${methodSignature(method)}")
        }
    }.onFailure { Log.w(TAG, "Reels sponsored pool resolution failed", it) }
}

private fun isReelsSponsoredPoolAddMethod(method: Method): Boolean {
    if (Modifier.isStatic(method.modifiers) || method.returnType != Void.TYPE) return false
    val params = method.parameterTypes
    if (params.size != 3) return false
    val session = params[0]
    if (session.name != "com.facebook.auth.usersession.FbUserSession" &&
        session.simpleName != "FbUserSession") return false
    val itemType = params[1]
    if (!itemType.isInterface) return false
    // WatchAdStoryPool and VideoHomeSponsoredPool both expose a one-argument
    // boolean item classifier beside their add method. This is the stable pool
    // role; the telemetry label is only a discovery seed.
    return method.declaringClass.declaredMethods.any { sibling ->
        !Modifier.isStatic(sibling.modifiers) &&
            sibling.returnType == Boolean::class.javaPrimitiveType &&
            sibling.parameterCount == 1 &&
            (sibling.parameterTypes[0] == itemType ||
                (sibling.parameterTypes[0].isInterface &&
                    (sibling.parameterTypes[0].isAssignableFrom(itemType) ||
                        itemType.isAssignableFrom(sibling.parameterTypes[0]))))
    }
}

// Filters ad items out of the nested lists pushed into the reels pager. The
// pager push takes a list of wrapper objects (576: C76D), each holding its own
// item list in its only Iterable-typed field. Every invocation logs a
// throttled summary (item/model/ad counts plus a classification sample) so a
// path change or an unrecognized ad classification is visible in debug logs.
private fun hookReelsPagerListPush(method: Method, classifier: ReelsAdClassifier) {
    method.isAccessible = true
    reelsGuardPagerPushSpecs.add("${method.declaringClass.name}#${method.name}")
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val wrappers = param.args.getOrNull(0) as? Iterable<*> ?: return
            var total = 0
            var withModel = 0
            var removed = 0
            var writeFailures = 0
            val sample = ArrayList<String>(8)
            val keptWrappers = ArrayList<Any?>()
            for (wrapper in wrappers) {
                val listField = resolveWrapperListField(wrapper?.javaClass)
                val items = if (listField != null) {
                    runCatching { listField.get(wrapper) }.getOrNull() as? Iterable<*>
                } else null
                if (items == null) {
                    keptWrappers.add(wrapper)
                    continue
                }
                val keptItems = ArrayList<Any?>()
                var ads = 0
                for (item in items) {
                    total++
                    val classification = classifier.classificationOf(item)
                    if (classification != null) {
                        withModel++
                        if (sample.size < 8) sample.add("${item?.javaClass?.simpleName}=${classification}")
                    }
                    if (classification != null && classification in AD_CLASSIFICATION_VALUES) {
                        ads++
                    } else {
                        keptItems.add(item)
                    }
                }
                when {
                    ads == 0 -> keptWrappers.add(wrapper)
                    // Ad-only wrapper: drop it from the outer list outright —
                    // rewriting param.args is guaranteed to take effect, even
                    // when the reflective write to the wrapper's final list
                    // field is rejected by the runtime.
                    keptItems.isEmpty() -> removed += ads
                    else -> {
                        val rebuilt = buildImmutableListLike(
                            items,
                            keptItems,
                            method.declaringClass.classLoader
                        )
                        val applied = rebuilt != null && runCatching {
                            listField?.set(wrapper, rebuilt)
                            true
                        }.getOrDefault(false)
                        if (applied) {
                            removed += ads
                        } else {
                            writeFailures++
                        }
                        keptWrappers.add(wrapper)
                    }
                }
            }
            if (keptWrappers.size != wrappers.count()) {
                // Never null out the argument: the hooked method declares its
                // parameter as a Kotlin non-null List, so a null (or a failed
                // rebuild) must leave the original list untouched — the
                // downstream render block still suppresses the ad page.
                val rebuilt = buildImmutableListLike(
                    param.args[0],
                    keptWrappers,
                    method.declaringClass.classLoader
                )
                if (rebuilt != null) {
                    param.args[0] = rebuilt
                }
            }
            logHookHitThrottled(
                "reelsPagerPush",
                method,
                "items=$total withModel=$withModel adsRemoved=$removed writeFailures=$writeFailures " +
                    "droppedWrappers=${wrappers.count() - keptWrappers.size} sample=[${sample.joinToString(", ")}]"
            )
        }
    })
    Log.i(TAG, "Hooked Reels pager ad filter at ${method.declaringClass.name}.${method.name}")
}

private val wrapperListFieldCache = ConcurrentHashMap<Class<*>, Field?>()

private fun resolveWrapperListField(clazz: Class<*>?): Field? {
    if (clazz == null) return null
    wrapperListFieldCache.get(clazz)?.let { return it }
    val field = runCatching {
        var current: Class<*>? = clazz
        var found: Field? = null
        while (current != null && current != Any::class.java && found == null) {
            found = current.declaredFields.firstOrNull { candidate ->
                !Modifier.isStatic(candidate.modifiers) &&
                    Iterable::class.java.isAssignableFrom(candidate.type)
            }
            current = current.superclass
        }
        found?.isAccessible = true
        found
    }.getOrNull()
    wrapperListFieldCache[clazz] = field
    return field
}

// Classifier for server-injected full-page Reels ads. Reel items expose their
// media model through a zero-arg accessor; the model implements an interface
// (576: X.9AE) whose zero-arg classifier method (BQB) returns a classification
// enum (576: X.7T7) with stable server values ("AD", "ADS_MIDCARD", "MIDCARD",
// "PARADE", "UGC"). The enum is found via the stable "ADS_MIDCARD" string; the
// item interfaces are interfaces declaring exactly one zero-arg method
// returning that enum.
private class ReelsAdClassifier(
    private val modelInterfaces: List<Pair<Class<*>, Method>>,
    private val adValues: Set<Any>
) {
    lateinit var enumClassName: String

    val modelInterfaceClasses: List<Class<*>> get() = modelInterfaces.map { it.first }

    // Item class -> candidate accessor chains (each chain is a sequence of
    // zero-arg getters from item to model). Null entries are cached misses.
    private val accessorChainsCache = ConcurrentHashMap<Class<*>, List<List<Method>>?>()

    fun isAdReelItem(item: Any?): Boolean {
        val classification = classificationOf(item) ?: return false
        return classification in AD_CLASSIFICATION_VALUES
    }

    // Classification of a direct model object (e.g. a constructor arg), or
    // null when the value is not a model instance.
    fun modelClassification(model: Any?): String? {
        if (model == null) return null
        for ((iface, method) in modelInterfaces) {
            if (iface.isInstance(model)) {
                return runCatching { method.invoke(model)?.toString() }.getOrNull()
            }
        }
        return null
    }

    // Returns the item's classification name (e.g. "AD", "UGC"), or null when
    // no model accessor chain resolves for the item's class.
    fun classificationOf(item: Any?): String? {
        if (item == null) return null
        val chains = resolveAccessorChains(item.javaClass) ?: return null
        for (chain in chains) {
            var current: Any? = item
            for (accessor in chain) {
                current = runCatching { accessor.invoke(current) }.getOrNull() ?: break
            }
            val model = current ?: continue
            for ((iface, method) in modelInterfaces) {
                if (!iface.isInstance(model)) continue
                return runCatching { method.invoke(model)?.toString() }.getOrNull()
            }
        }
        return null
    }

    private fun resolveAccessorChains(clazz: Class<*>): List<List<Method>>? {
        accessorChainsCache.get(clazz)?.let { return it }
        val chains = runCatching { findAccessorChains(clazz) }.getOrNull()
        accessorChainsCache[clazz] = chains
        return chains
    }

    // Direct accessors first (item method returning a model interface), then
    // two-hop chains through a holder object (576 reels items expose the media
    // model via item.A04().A00()-style getter pairs). Only one hop through
    // non-trivial types; deeper nesting has not been seen.
    private fun findAccessorChains(clazz: Class<*>): List<List<Method>>? {
        val chains = ArrayList<List<Method>>()
        zeroArgMethods(clazz).forEach { candidate ->
            if (modelInterfaces.any { (iface, _) -> candidate.returnType == iface }) {
                chains.add(listOf(candidate))
            }
        }
        zeroArgMethods(clazz).forEach { candidate ->
            val holder = candidate.returnType
            if (holder == clazz || holder.isPrimitive || holder == Void.TYPE ||
                holder == String::class.java ||
                Collection::class.java.isAssignableFrom(holder) ||
                holder.name.startsWith("java.")
            ) return@forEach
            zeroArgMethods(holder).forEach { nested ->
                if (modelInterfaces.any { (iface, _) -> nested.returnType == iface }) {
                    chains.add(listOf(candidate, nested))
                }
            }
        }
        return chains.ifEmpty { null }
    }

    private fun zeroArgMethods(clazz: Class<*>): List<Method> =
        clazz.methods.filter { method ->
            !Modifier.isStatic(method.modifiers) &&
                method.parameterCount == 0 &&
                method.returnType != Void.TYPE
        }

    fun isModelType(type: Class<*>): Boolean = modelInterfaces.any { it.first == type }

    fun describe(): String {
        return "models=${modelInterfaces.joinToString { "${it.first.name}.${it.second.name}" }} " +
            "adValues=${adValues.joinToString { it.toString() }}"
    }
}

private fun resolveReelsAdClassifier(classLoader: ClassLoader, bridge: DexKitBridge): ReelsAdClassifier? {
    // 1. The classification enum via its stable server-value strings.
    val enumClass = bridge.findClass {
        matcher {
            usingStrings("ADS_MIDCARD")
        }
    }.asSequence()
        .mapNotNull { runCatching { it.getInstance(classLoader) }.getOrNull() }
        .firstOrNull { it.isEnum } ?: run {
        Log.w(TAG, "Reels ad classifier: classification enum not found")
        return null
    }
    val adValues = enumClass.enumConstants
        .filter { runCatching { it.toString() }.getOrNull() in AD_CLASSIFICATION_VALUES }
        .toSet()
    if (adValues.isEmpty()) {
        Log.w(TAG, "Reels ad classifier: enum ${enumClass.name} has no ad constants")
        return null
    }

    // 2. Model interfaces: interfaces declaring exactly one zero-arg method
    //    returning the classification enum.
    val modelInterfaces = bridge.findMethod {
        matcher {
            returnType = enumClass.name
            paramCount = 0
        }
    }.asSequence()
        .mapNotNull { methodData ->
            runCatching { methodData.getMethodInstance(classLoader) }.getOrNull()
        }
        .map { it.declaringClass }
        .filter { it.isInterface }
        .distinct()
        .mapNotNull { candidate ->
            runCatching {
                val methods = candidate.declaredMethods.filter { method ->
                    method.parameterCount == 0 && method.returnType == enumClass
                }
                if (methods.size != 1) return@mapNotNull null
                methods[0].isAccessible = true
                candidate to methods[0]
            }.getOrNull()
        }
        .toList()
    if (modelInterfaces.isEmpty()) {
        Log.w(TAG, "Reels ad classifier: model interfaces not found")
        return null
    }
    return ReelsAdClassifier(modelInterfaces, adValues).also {
        it.enumClassName = enumClass.name
        reelsGuardModelInterfaceSpecs = modelInterfaces.map { (iface, method) ->
            "${iface.name}#${method.name}"
        }
        reelsGuardEnumClassName = enumClass.name
    }
}

// Persists the reels hook targets discovered by the full DexKit pass so the
// next launch of the same Facebook build can install them right after
// Application.attach — before the cold-start reels render that flashes an ad
// and only disappears once the render block arms seconds later.
fun saveReelsGuardCache(context: Context, hostVersionName: String) {
    if (hostVersionName.isBlank()) return
    val renderables = reelsGuardRenderableNames.toList().distinct()
    val shoppingRenderables = reelsShoppingRenderableNames.toList().distinct()
    val interfaces = reelsGuardModelInterfaceSpecs
    if (renderables.isEmpty() || interfaces.isEmpty()) return
    runCatching {
        val properties = Properties()
        properties.setProperty("version", hostVersionName)
        properties.setProperty("moduleVersion", feedGuardCacheModuleKey())
        properties.setProperty("modelInterfaces", interfaces.joinToString(","))
        properties.setProperty("enumClass", reelsGuardEnumClassName)
        properties.setProperty("renderables", renderables.joinToString(","))
        properties.setProperty("shoppingRenderables", shoppingRenderables.joinToString(","))
        properties.setProperty("pagerPush", reelsGuardPagerPushSpecs.toList().distinct().joinToString(","))
        properties.setProperty("snapshots", reelsGuardSnapshotSpecs.toList().distinct().joinToString(","))
        File(context.cacheDir, REELS_GUARD_CACHE_FILE).outputStream().use { properties.store(it, null) }
        Log.i(TAG, "Saved reels guard cache renderables=${renderables.size} shopping=${shoppingRenderables.size} pagerPush=${reelsGuardPagerPushSpecs.size} snapshots=${reelsGuardSnapshotSpecs.size}")
    }.onFailure { Log.w(TAG, "Failed to save reels guard cache", it) }
}

@Volatile
private var reelsGuardCachedInterfaces: List<String> = emptyList()

@Volatile
private var reelsGuardCachedRenderables: List<String> = emptyList()

@Volatile
private var reelsGuardCachedShoppingRenderables: List<String> = emptyList()

@Volatile
private var reelsGuardCachedPagerPush: List<String> = emptyList()

@Volatile
private var reelsGuardCachedSnapshots: List<String> = emptyList()

@Volatile
private var reelsGuardCacheParsed = false

// Cached specs already resolved by the early-install thread; each is retried
// until its class becomes loadable, then never again.
private val reelsGuardResolvedSpecs: MutableSet<String> = Collections.synchronizedSet(HashSet())

// Set once the full DexKit pass installs the reels hooks; the early-install
// thread stops retrying because every target is then hooked anyway.
private val reelsFullPassInstalled = java.util.concurrent.atomic.AtomicBoolean(false)

// Loads the persisted reels guard targets and installs them on a background
// thread, retrying while the secondary dex finishes configuring (the cached
// class names fail Class.forName at attach time, exactly like the feed guard).
fun installReelsGuardFromCache(
    context: Context,
    classLoader: ClassLoader,
    hostVersionName: String
) {
    if (hostVersionName.isBlank()) return
    if (!reelsGuardCacheParsed) {
        val parsed = runCatching {
            val file = File(context.cacheDir, REELS_GUARD_CACHE_FILE)
            if (!file.exists()) return
            val properties = Properties()
            file.inputStream().use { properties.load(it) }
            if (hostVersionName != properties.getProperty("version")) {
                Log.i(TAG, "Reels guard cache stale for version=$hostVersionName; re-discovering")
                return
            }
            if (feedGuardCacheModuleKey() != properties.getProperty("moduleVersion")) {
                Log.i(TAG, "Reels guard cache stale for moduleVersion; re-discovering")
                return
            }
            reelsGuardCachedInterfaces = properties.getProperty("modelInterfaces").orEmpty()
                .split(',').filter { it.isNotBlank() }
            reelsGuardCachedRenderables = properties.getProperty("renderables").orEmpty()
                .split(',').filter { it.isNotBlank() }
            reelsGuardCachedShoppingRenderables = properties.getProperty("shoppingRenderables").orEmpty()
                .split(',').filter { it.isNotBlank() }
            reelsGuardCachedPagerPush = properties.getProperty("pagerPush").orEmpty()
                .split(',').filter { it.isNotBlank() }
            reelsGuardCachedSnapshots = properties.getProperty("snapshots").orEmpty()
                .split(',').filter { it.isNotBlank() }
            true
        }.getOrDefault(false)
        if (!parsed || reelsGuardCachedInterfaces.isEmpty() || reelsGuardCachedRenderables.isEmpty()) {
            reelsGuardCacheParsed = true
            return
        }
        Log.i(
            TAG,
            "Loaded reels guard cache renderables=${reelsGuardCachedRenderables.size} " +
                "pagerPush=${reelsGuardCachedPagerPush.size} snapshots=${reelsGuardCachedSnapshots.size}"
        )
        reelsGuardCacheParsed = true
    }
    if (reelsGuardCachedInterfaces.isEmpty()) return
    Thread(
        {
            // Some cached classes (e.g. the pager controller) only become
            // loadable when the secondary dexes finish configuring, seconds
            // after attach — hence the long retry window. Each spec is
            // resolved at most once; the full DexKit pass makes the whole
            // thread redundant once it installs.
            val allSpecs = reelsGuardCachedRenderables +
                reelsGuardCachedShoppingRenderables +
                reelsGuardCachedPagerPush +
                reelsGuardCachedSnapshots
            for (attempt in 1..80) {
                if (reelsFullPassInstalled.get()) return@Thread
                // Shopping cards need no classifier, so they install first —
                // even before the model interfaces become loadable.
                for (name in reelsGuardCachedShoppingRenderables) {
                    if (!reelsGuardResolvedSpecs.add(name)) continue
                    val clazz = runCatching { Class.forName(name, false, classLoader) }.getOrNull()
                    if (clazz == null) {
                        reelsGuardResolvedSpecs.remove(name)
                        continue
                    }
                    runCatching {
                        hookReelsShoppingRenderable(clazz, reelsRenderHookedMethods, "Reels shopping card (cached)")
                    }
                }
                val classifier = buildCachedReelsClassifier(classLoader)
                if (classifier != null) {
                    for (name in reelsGuardCachedRenderables) {
                        if (!reelsGuardResolvedSpecs.add(name)) continue
                        val clazz = runCatching { Class.forName(name, false, classLoader) }.getOrNull()
                        if (clazz == null) {
                            reelsGuardResolvedSpecs.remove(name)
                            continue
                        }
                        runCatching {
                            hookReelsAdRenderable(clazz, classifier, reelsRenderHookedMethods, "Reels ad renderable (cached)")
                        }
                    }
                    for (spec in reelsGuardCachedPagerPush) {
                        if (!reelsGuardResolvedSpecs.add(spec)) continue
                        val method = resolveReelsGuardMethodSpec(classLoader, spec)
                        if (method == null) {
                            reelsGuardResolvedSpecs.remove(spec)
                            continue
                        }
                        runCatching { hookReelsPagerListPush(method, classifier) }
                    }
                    for (spec in reelsGuardCachedSnapshots) {
                        if (!reelsGuardResolvedSpecs.add(spec)) continue
                        val method = resolveReelsGuardMethodSpec(classLoader, spec)
                        if (method == null) {
                            reelsGuardResolvedSpecs.remove(spec)
                            continue
                        }
                        runCatching { hookReelsCollectionSnapshot(method, classifier) }
                    }
                }
                if (reelsGuardResolvedSpecs.containsAll(allSpecs)) {
                    Log.i(TAG, "Reels guard cache installed early: ${allSpecs.size} targets")
                    return@Thread
                }
                Thread.sleep(250)
            }
            Log.w(TAG, "Reels guard cache install incomplete; full DexKit pass will finish it")
        },
        "FbarrReelsGuardInit"
    ).start()
}

private fun buildCachedReelsClassifier(classLoader: ClassLoader): ReelsAdClassifier? {
    val pairs = reelsGuardCachedInterfaces.mapNotNull { spec ->
        val idx = spec.indexOf('#')
        if (idx <= 0) return@mapNotNull null
        runCatching {
            val iface = Class.forName(spec.substring(0, idx), false, classLoader)
            val method = iface.getDeclaredMethod(spec.substring(idx + 1))
            method.isAccessible = true
            iface to method
        }.getOrNull()
    }
    if (pairs.size != reelsGuardCachedInterfaces.size) return null
    return ReelsAdClassifier(pairs, emptySet()).also { it.enumClassName = reelsGuardEnumClassName }
}

private fun resolveReelsGuardMethodSpec(classLoader: ClassLoader, spec: String): Method? {
    val idx = spec.indexOf('#')
    if (idx <= 0) return null
    return runCatching {
        val clazz = Class.forName(spec.substring(0, idx), false, classLoader)
        val method = clazz.getDeclaredMethod(spec.substring(idx + 1))
        method.isAccessible = true
        method
    }.getOrNull()
}

// Pure log probes over the two candidate pipelines for full-page Reels ads:
// the instream/postloop fetch state machine ("FBFetchReelsVideoAdsQuery") and
// the reels ad impression recorder ("ReelsAdImpRecord"). Whichever fires while
// a full-page ad is visible identifies the real insertion pipeline.
private fun installReelsAdPipelineProbes(classLoader: ClassLoader, bridge: DexKitBridge) {
    val userSessionClass = runCatching {
        Class.forName("com.facebook.auth.usersession.FbUserSession", false, classLoader)
    }.getOrNull()
    val futureClass = runCatching {
        Class.forName("com.google.common.util.concurrent.ListenableFuture", false, classLoader)
    }.getOrNull()

    // Impression recorder: constructed exactly when a reels ad is displayed.
    runCatching {
        bridge.findClass {
            matcher {
                usingStrings("ReelsAdImpRecord(sessionId=")
            }
        }.forEach { candidate ->
            val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
            clazz.declaredConstructors.forEach { constructor ->
                constructor.isAccessible = true
                XposedBridge.hookMethod(constructor, object : XC_MethodHook() {
                    override fun afterHookedMethod(param: MethodHookParam) {
                        val count = reelsAdDiagnosticsLogged.incrementAndGet()
                        if (count > 80) return
                        Log.i(
                            TAG,
                            "ReelsAdDiag impRecord ${clazz.name} args=${formatDiagArgs(param.args)}"
                        )
                    }
                })
            }
            Log.i(TAG, "Hooked Reels ad impression recorder ${clazz.name}")
        }
    }.onFailure { Log.w(TAG, "Reels ad impression recorder not found", it) }

    // Instream/postloop fetch pipeline classes.
    runCatching {
        bridge.findClass {
            matcher {
                usingStrings("FBFetchReelsVideoAdsQuery")
            }
        }.forEach { candidate ->
            val clazz = runCatching { candidate.getInstance(classLoader) }.getOrNull() ?: return@forEach
            var hooked = 0
            (clazz.declaredMethods + clazz.methods).filter { method ->
                !Modifier.isStatic(method.modifiers) && !method.isSynthetic && !method.isBridge
            }.forEach { method ->
                val isFetch = futureClass != null && method.returnType == futureClass
                val isTrigger = userSessionClass != null &&
                    method.returnType == Void.TYPE &&
                    method.parameterTypes.firstOrNull() == userSessionClass
                if (!isFetch && !isTrigger) return@forEach
                method.isAccessible = true
                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        val count = reelsAdDiagnosticsLogged.incrementAndGet()
                        if (count > 80) return
                        Log.i(
                            TAG,
                            "ReelsAdDiag ${if (isFetch) "fetch" else "trigger"} " +
                                "${clazz.name}.${method.name} args=${formatDiagArgs(param.args)}"
                        )
                    }
                })
                hooked++
            }
            Log.i(TAG, "Hooked $hooked Reels instream pipeline method(s) in ${clazz.name}")
        }
    }.onFailure { Log.w(TAG, "Reels instream pipeline classes not found", it) }
}

// Walks the component's fields to capture the reels item model (C8YG → A04
// ad model C8Wm) and every reachable string field, so one reproduction shows
// the full ad payload chain.
private fun describeReelsAdModelChain(root: Any) {
    runCatching {
        val rootClass = root.javaClass
        val fields = rootClass.declaredFields.filter { !Modifier.isStatic(it.modifiers) }
        fields.forEach { field ->
            field.isAccessible = true
            val value = runCatching { field.get(root) }.getOrNull() ?: return@forEach
            val typeName = value.javaClass.name
            val description = when {
                value is String -> "\"${value.take(160)}\""
                value.javaClass.name.contains("FbUserSession") -> "userSession"
                else -> {
                    val inner = value.javaClass.declaredFields
                        .filter { !Modifier.isStatic(it.modifiers) }
                        .mapNotNull { innerField ->
                            innerField.isAccessible = true
                            val innerValue = runCatching { innerField.get(value) }.getOrNull()
                            innerValue?.let { "  ${innerField.name}(${innerField.type.simpleName})=${formatDiagValue(it).take(120)}" }
                        }
                        .joinToString("\n")
                    "$typeName {\n$inner\n}"
                }
            }
            Log.i(TAG, "ReelsAdDiag field ${field.name}($typeName)=${description.take(600)}")
        }
    }.onFailure { Log.w(TAG, "ReelsAdDiag chain walk failed", it) }
}

private fun resolveSponsoredPoolAddMethod(classLoader: ClassLoader, sponsoredPoolClass: ClassData): Method? {
    val method = sponsoredPoolClass.findMethod {
        findFirst = true
        matcher {
            returnType = "boolean"
            paramTypes = listOf("com.facebook.graphql.model.GraphQLFeedUnitEdge")
        }
    }.firstOrNull() ?: return null

    return listOf(method).firstMethodInstanceOrNull(classLoader)
}

private fun resolveSponsoredStoryNextMethod(
    classLoader: ClassLoader,
    sponsoredStoryManagerClass: ClassData
): Method? {
    val method = sponsoredStoryManagerClass.findMethod {
        findFirst = true
        matcher {
            returnType = "com.facebook.graphql.model.GraphQLFeedUnitEdge"
            paramCount = 0
        }
    }.firstOrNull() ?: return null

    return listOf(method).firstMethodInstanceOrNull(classLoader)
}

private fun resolveGameAdRequestMethods(
    classLoader: ClassLoader,
    bridge: DexKitBridge
): List<Method> {
    val methods = LinkedHashMap<String, Method>()
    GAME_AD_METHOD_TAGS.forEach { tag ->
        bridge.findMethod {
            matcher {
                returnType = "void"
                paramTypes = listOf("org.json.JSONObject")
                usingStrings(tag)
            }
        }.mapNotNull { methodData ->
            runCatching { methodData.getMethodInstance(classLoader) }.getOrNull()
        }.filter { method ->
            !Modifier.isStatic(method.modifiers) &&
                method.name != "<init>" &&
                method.name != "<clinit>"
        }.forEach { method ->
            method.isAccessible = true
            methods.putIfAbsent("${method.declaringClass.name}.${method.name}", method)
        }
    }
    return methods.values.toList()
}

private fun resolveGameAdBridgePostMessageMethod(gameAdRequestMethods: Collection<Method>): Method? {
    val bridgeClass = gameAdRequestMethods.firstOrNull()?.declaringClass ?: return null
    return bridgeClass.declaredMethods.firstOrNull { method ->
        method.name == "postMessage" &&
            method.parameterCount == 2 &&
            method.parameterTypes.all { it == String::class.java }
    }?.apply { isAccessible = true }
}

private fun resolvePlayableAdActivityOnCreate(classLoader: ClassLoader): Method? {
    val activityClass = runCatching { classLoader.loadClass(NEKO_PLAYABLE_ACTIVITY_CLASS) }.getOrNull() ?: return null
    return activityClass.declaredMethods
        .firstOrNull { method ->
            method.name == "onResume" &&
                method.parameterCount == 0
        }?.apply { isAccessible = true }
}

private fun resolveGameAdUiActivityMethods(classLoader: ClassLoader): List<Method> {
    val methods = LinkedHashMap<String, Method>()
    val classNames = listOf(
        AUDIENCE_NETWORK_ACTIVITY_CLASS,
        AUDIENCE_NETWORK_REMOTE_ACTIVITY_CLASS
    )
    classNames.forEach { className ->
        val activityClass = runCatching { classLoader.loadClass(className) }.getOrNull()
        if (activityClass == null) {
            Log.w(TAG, "Game ad UI class not loadable: $className")
            return@forEach
        }
        (activityClass.declaredMethods + activityClass.methods)
            .firstOrNull { method ->
                (method.name == "onResume" && method.parameterCount == 0) ||
                    (method.name == "onStart" && method.parameterCount == 0) ||
                    (method.name == "onCreate" && method.parameterCount == 1 && method.parameterTypes[0] == Bundle::class.java)
            }?.apply {
                isAccessible = true
                methods.putIfAbsent("${declaringClass.name}.${name}", this)
            }
    }
    if (methods.isEmpty()) {
        resolveGameAdUiActivityMethodsFallback(classLoader, methods)
    }
    return methods.values.toList()
}

private fun resolveGameAdUiActivityMethodsFallback(
    classLoader: ClassLoader,
    methods: LinkedHashMap<String, Method>
) {
    val activityClass = runCatching {
        classLoader.loadClass("android.app.Activity")
    }.getOrNull() ?: return
    GAME_AD_ACTIVITY_CLASS_NAMES.forEach { className ->
        val clazz = runCatching { classLoader.loadClass(className) }.getOrNull()
        if (clazz != null && activityClass.isAssignableFrom(clazz)) {
            (clazz.declaredMethods + clazz.methods)
                .firstOrNull { method ->
                    (method.name == "onResume" && method.parameterCount == 0) ||
                        (method.name == "onStart" && method.parameterCount == 0) ||
                        (method.name == "onCreate" && method.parameterCount == 1 && method.parameterTypes[0] == Bundle::class.java)
                }?.apply {
                    isAccessible = true
                    methods.putIfAbsent("${declaringClass.name}.${name}", this)
                }
        }
    }
}

private fun hookListBuilderAppend(method: Method, inspector: AdStoryInspector) {
    val listArgIndex = method.listParameterIndexes().singleOrNull()
    if (listArgIndex == null) {
        Log.w(
            TAG,
            "Skipping list append hook because ${method.declaringClass.name}.${method.name} does not expose exactly one List parameter"
        )
        return
    }

    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val list = param.args.getOrNull(listArgIndex) as? List<*>
            param.setObjectExtra(BEFORE_SIZE_EXTRA, list?.size ?: -1)
        }

        override fun afterHookedMethod(param: MethodHookParam) {
            val beforeSize = param.getObjectExtra(BEFORE_SIZE_EXTRA) as? Int ?: return
            val list = param.args.getOrNull(listArgIndex) as? MutableList<Any?> ?: return
            if (beforeSize < 0 || beforeSize > list.size) return

            var removed = 0
            for (index in list.lastIndex downTo beforeSize) {
                if (inspector.containsAdStory(list[index])) {
                    list.removeAt(index)
                    removed++
                }
            }

            if (removed > 0) {
                Log.i(TAG, "Removed $removed ad item(s) from upstream list append")
            }
        }
    })
}

private fun hookListResultFilter(method: Method, source: String, inspector: AdStoryInspector) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun afterHookedMethod(param: MethodHookParam) {
            val result = param.result as? MutableList<Any?> ?: return
            val removed = filterAdItems(result, inspector)
            if (removed > 0) {
                Log.i(TAG, "Removed $removed ad item(s) from $source")
            }
        }
    })
}

private fun hookPluginPackFallback(method: Method, inspector: AdStoryInspector) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            if (isMarketplaceAdsPluginPack(param.thisObject)) {
                Log.i(TAG, "Returning an empty plugin pack for marketplace ads (${method.declaringClass.name})")
                param.result = arrayListOf<Any?>()
                return
            }
            if (inspector.containsAdStory(param.thisObject)) {
                Log.i(TAG, "Returning an empty plugin pack for an ad-backed story")
                param.result = arrayListOf<Any?>()
            }
        }

        override fun afterHookedMethod(param: MethodHookParam) {
            if (isMarketplaceAdsPluginPack(param.thisObject)) return
            val result = param.result as? MutableList<Any?> ?: return
            val removed = filterAdItems(result, inspector)
            if (removed > 0) {
                Log.i(TAG, "Removed $removed ad plugin item(s)")
            }
        }
    })
}

private val marketplaceAdsPackCache = ConcurrentHashMap<String, Boolean>()

private fun isMarketplaceAdsPluginPack(instance: Any): Boolean {
    val className = instance.javaClass.name
    return marketplaceAdsPackCache.getOrPut(className) {
        runCatching {
            instance.javaClass.declaredMethods
                .filter { m ->
                    m.parameterCount == 0 &&
                        m.returnType == String::class.java &&
                        !java.lang.reflect.Modifier.isStatic(m.modifiers)
                }
                .any { m ->
                    m.isAccessible = true
                    val name = m.invoke(instance) as? String
                    name != null && name.contains("Ads", ignoreCase = true)
                }
        }.getOrDefault(false)
    }
}

private fun hookFeedCsrFilterInput(
    hook: FeedCsrFilterHook,
    feedItemInspector: FeedItemInspector
): Boolean {
    if (!feedCsrMethodsHooked.add(methodHookKey(hook.method))) {
        return false
    }
    XposedBridge.hookMethod(hook.method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val filterName = hook.method.declaringClass.name
            val originalList = param.args.getOrNull(hook.listArgIndex) as? Iterable<*>
            if (originalList == null) return
            logFeedItems("$filterName IN", originalList, feedItemInspector)
            val keptItems = ArrayList<Any?>()
            var removed = 0

            for (item in originalList) {
                if (feedItemInspector.isDefinitelySponsoredFeedItem(item)) {
                    removed++
                } else {
                    keptItems.add(item)
                }
            }

            if (removed <= 0) return

            val rebuilt = buildImmutableListLike(param.args.getOrNull(hook.listArgIndex), keptItems) ?: return
            param.args[hook.listArgIndex] = rebuilt
            Log.i(TAG, "Removed $removed sponsored feed item(s) before ${hook.method.declaringClass.name}.${hook.method.name}")
        }

        override fun afterHookedMethod(param: MethodHookParam) {
            val filterName = hook.method.declaringClass.name
            val resultItems = extractFeedItemsFromResult(param.result)
            if (resultItems != null) {
                logFeedItems("$filterName OUT", resultItems, feedItemInspector)
                val keptItems = ArrayList<Any?>()
                var removed = 0
                for (item in resultItems) {
                    if (feedItemInspector.isDefinitelySponsoredFeedItem(item)) {
                        removed++
                    } else {
                        keptItems.add(item)
                    }
                }
                if (removed > 0 && replaceFeedItemsInResult(param, keptItems)) {
                    Log.i(TAG, "Removed $removed sponsored feed item(s) from result of ${hook.method.declaringClass.name}.${hook.method.name}")
                }
            }
        }
    })
    return true
}

private fun methodHookKey(method: Method): String {
    return "${method.declaringClass.name}#${method.name}(" +
        method.parameterTypes.joinToString(",") { it.name } +
        "):${method.returnType.name}"
}

private fun hookLateFeedListSanitizer(
    hook: FeedListSanitizerHook,
    feedItemInspector: FeedItemInspector
): Boolean {
    if (!lateFeedMethodsHooked.add(methodHookKey(hook.method))) {
        return false
    }
    XposedBridge.hookMethod(hook.method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val originalList = param.args.getOrNull(hook.listArgIndex) as? Iterable<*> ?: return
            val keptItems = ArrayList<Any?>()
            var removed = 0

            for (item in originalList) {
                if (feedItemInspector.isDefinitelySponsoredFeedItem(item)) {
                    removed++
                } else {
                    keptItems.add(item)
                }
            }

            if (removed <= 0) return

            val rebuilt = buildImmutableListLike(param.args.getOrNull(hook.listArgIndex), keptItems) ?: return
            param.args[hook.listArgIndex] = rebuilt
            Log.i(
                TAG,
                "Late-stage removed $removed sponsored feed item(s) before ${hook.method.declaringClass.name}.${hook.method.name}"
            )
        }
    })
    return true
}

private fun hookStoryPoolAdd(
    method: Method,
    feedItemInspector: FeedItemInspector,
    logAllowedItems: Boolean = false
) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val item = param.args.getOrNull(0)
            val blockReason = feedItemInspector.storyPoolBlockReason(item)
            if (blockReason == null) {
                if (logAllowedItems && item != null) {
                    logHookHitThrottled(
                        "shortsPoolAddAllowed",
                        method,
                        feedItemInspector.describe(item)
                    )
                } else if (feedItemInspector.isSponsoredFeedItem(item)) {
                    logHookHitThrottled("storyPoolBroadAllowed", method, feedItemInspector.describe(item))
                }
                return
            }

            param.result = false
            logHookHitThrottled(
                if (blockReason == "strict") "storyPoolStrictBlock" else "storyPoolBroadNetworkBlock",
                method,
                feedItemInspector.describe(item)
            )
        }
    })
}

private fun logHookHitThrottled(hookName: String, method: Method, detail: String? = null) {
    val hits = hookHitCounters.computeIfAbsent(hookName) { AtomicInteger(0) }.incrementAndGet()
    if (hits <= 3 || hits % HOOK_HIT_LOG_EVERY == 0) {
        val extra = detail?.let { " $it" } ?: ""
        Log.i(TAG, "Hook hit $hookName count=$hits at ${method.declaringClass.name}.${method.name}$extra")
    }
}

private fun hookInstreamBannerEligibility(method: Method) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            logHookHitThrottled("bannerState", method)
            param.result = false
        }
    })
}

private fun hookIndicatorPillAdEligibility(method: Method) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val pluginSlot = param.args.getOrNull(2)?.toString() ?: "unknown"
            logHookHitThrottled("indicatorPill", method, "slot=$pluginSlot")
            param.result = false
        }
    })
}

private fun hookReelsBannerRender(method: Method) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            logHookHitThrottled("reelsBannerRender", method)
            param.result = null
        }
    })
}

private fun hookGameAdRequest(method: Method) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val payload = param.args.getOrNull(0) ?: return
            val messageType = inferGameAdMessageType(method, payload)
            markGameAdDiagnosticFlow("request ${method.declaringClass.name}.${method.name}")
            logGameAdDiagnostic(
                "request.before",
                "${methodSignature(method)} type=$messageType this=${formatDiagValue(param.thisObject)} args=${formatDiagArgs(param.args)}"
            )
            rememberGameAdPayload(param.thisObject, payload, messageType)
            if (!ENABLE_GAME_AD_AUTOFIX) return
            if (!shouldForceGameAdSuccess(payload, messageType)) return

            if (resolveGameAdPayload(param.thisObject, payload, messageType)) {
                dispatchPostResolveGameAdSignals(param.thisObject, payload, messageType)
                param.result = null
                Log.i(
                    TAG,
                    "Resolved game ad request as success in ${method.declaringClass.name}.${method.name}"
                )
            } else if (rejectGameAdPayload(param.thisObject, payload)) {
                param.result = null
                Log.i(
                    TAG,
                    "Rejected game ad request in ${method.declaringClass.name}.${method.name}"
                )
            } else {
                Log.w(
                    TAG,
                    "Unable to resolve or reject game ad request ${method.declaringClass.name}.${method.name}"
                )
            }
        }

        override fun afterHookedMethod(param: MethodHookParam) {
            val payload = param.args.getOrNull(0) ?: return
            val messageType = inferGameAdMessageType(method, payload)
            logGameAdDiagnostic(
                "request.after",
                "${methodSignature(method)} type=$messageType result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
            )
        }
    })
}

private fun hookGameAdBridge(method: Method) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val rawMessage = param.args.getOrNull(0) as? String ?: return
            val payload = runCatching { JSONObject(rawMessage) }.getOrNull() ?: return
            val messageType = payload.optString("type")
            if (messageType !in GAME_AD_MESSAGE_TYPES) return

            markGameAdDiagnosticFlow("bridge ${method.declaringClass.name}.${method.name}")
            logGameAdDiagnostic(
                "bridge.before",
                "${methodSignature(method)} type=$messageType args=${formatDiagArgs(param.args)}"
            )
            rememberGameAdPayload(param.thisObject, payload, messageType)
            if (!ENABLE_GAME_AD_AUTOFIX) return
            if (!shouldForceGameAdSuccess(payload, messageType)) return

            if (resolveGameAdPayload(param.thisObject, payload, messageType)) {
                dispatchPostResolveGameAdSignals(param.thisObject, payload, messageType)
                param.result = null
                Log.i(
                    TAG,
                    "Resolved game ad bridge message type=$messageType in ${method.declaringClass.name}.${method.name}"
                )
            } else if (rejectGameAdPayload(param.thisObject, payload)) {
                param.result = null
                Log.i(
                    TAG,
                    "Rejected game ad bridge message type=$messageType in ${method.declaringClass.name}.${method.name}"
                )
            } else {
                Log.w(
                    TAG,
                    "Unable to resolve or reject game ad bridge message type=$messageType in ${method.declaringClass.name}.${method.name}"
                )
            }
        }

        override fun afterHookedMethod(param: MethodHookParam) {
            val rawMessage = param.args.getOrNull(0) as? String ?: return
            val payload = runCatching { JSONObject(rawMessage) }.getOrNull() ?: return
            val messageType = payload.optString("type")
            if (messageType !in GAME_AD_MESSAGE_TYPES) return

            logGameAdDiagnostic(
                "bridge.after",
                "${methodSignature(method)} type=$messageType result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
            )
        }
    })
}

// The instant-games delegate that receives ad messages is not the DexKit
// bridge (X.gJA) on all builds — the game webview can register a delegate
// from a lazily loaded plugin dex whose obfuscated name is unknowable in
// advance. WebView.addJavascriptInterface is a stable framework seam that
// observes every delegate object at registration time, whatever dex it
// comes from; its JS entry methods are then hooked with the same
// game-ad bridge logic used for the statically discovered bridge.
private val gameAdJavascriptInterfaceHookInstalled = AtomicInteger(0)
private val gameAdBridgeEntryMethodsHooked = ConcurrentHashMap.newKeySet<String>()

fun installGameAdJavascriptInterfaceBridgeHook() {
    if (!gameAdJavascriptInterfaceHookInstalled.compareAndSet(0, 1)) return
    runCatching {
        val addInterfaceMethod = WebView::class.java.getDeclaredMethod(
            "addJavascriptInterface",
            Any::class.java,
            String::class.java
        )
        addInterfaceMethod.isAccessible = true
        XposedBridge.hookMethod(addInterfaceMethod, object : XC_MethodHook() {
            override fun afterHookedMethod(param: MethodHookParam) {
                val bridgeObject = param.args.getOrNull(0) ?: return
                runCatching { hookGameAdBridgeObject(bridgeObject, "addJavascriptInterface") }
                    .onFailure {
                        Log.w(TAG, "Failed to hook game bridge object ${bridgeObject.javaClass.name}", it)
                    }
            }
        })
        Log.i(TAG, "Waiting for game webview Javascript bridges")
    }.onFailure {
        Log.w(TAG, "Failed to hook WebView.addJavascriptInterface", it)
    }

    // Promise deliveries can happen before the DexKit scan, so the webview
    // script seams are installed alongside the bridge watcher.
    installGameAdScriptResultHooks()
}

private fun hookGameAdBridgeObject(bridgeObject: Any, source: String) {
    val bridgeClass = bridgeObject.javaClass

    val entryMethods = (bridgeClass.declaredMethods + bridgeClass.methods).filter { method ->
        !Modifier.isStatic(method.modifiers) &&
            method.parameterCount in 1..2 &&
            method.parameterTypes[0] == String::class.java &&
            method.isAnnotationPresent(JavascriptInterface::class.java)
    }.ifEmpty {
        (bridgeClass.declaredMethods + bridgeClass.methods).filter { method ->
            method.name == "postMessage" && method.parameterTypes.firstOrNull() == String::class.java
        }
    }

    entryMethods.forEach { method ->
        if (!gameAdBridgeEntryMethodsHooked.add(methodHookKey(method))) return@forEach
        method.isAccessible = true
        hookGameAdBridge(method)
        Log.i(TAG, "Hooked game bridge entry ${bridgeClass.name}.${method.name} via $source")
    }

    hookGameAdResultMethods(bridgeClass)
    hookGameAdServiceDispatchMethods(bridgeClass)
}

// The promise result is delivered back into the game webview as generated
// JavaScript (or a WebMessage) by plumbing whose shape varies per delegate —
// the same-process delegate (576: X.q10) has no promise helper on its class at
// all. These framework-level seams see every delivery regardless of the
// internal plumbing. A JS promise settles once, so the original failure call
// is rewritten in place, never shadowed by an extra call.
private val gameAdScriptHooksInstalled = AtomicInteger(0)
private val gameAdScriptDiagnostics = AtomicInteger(0)

fun installGameAdScriptResultHooks() {
    if (!gameAdScriptHooksInstalled.compareAndSet(0, 1)) return

    hookWebViewScriptDelivery("evaluateJavascript", String::class.java, ValueCallback::class.java)
    hookWebViewScriptDelivery("loadUrl", String::class.java)
    runCatching {
        val webMessageClass = Class.forName("android.webkit.WebMessage")
        val getData = webMessageClass.getDeclaredMethod("getData")
        val constructor = webMessageClass.getConstructor(String::class.java)
        val postWebMessage = WebView::class.java.getDeclaredMethod(
            "postWebMessage",
            webMessageClass,
            android.net.Uri::class.java
        )
        postWebMessage.isAccessible = true
        XposedBridge.hookMethod(postWebMessage, object : XC_MethodHook() {
            override fun beforeHookedMethod(param: MethodHookParam) {
                val message = param.args.getOrNull(0) ?: return
                val data = runCatching { getData.invoke(message) as? String }.getOrNull() ?: return
                val rewritten = rewriteGameAdDeliveryIfNeeded(data, "postWebMessage") ?: return
                runCatching {
                    param.args[0] = constructor.newInstance(rewritten)
                    Log.i(TAG, "Rewrote game ad web message promise delivery")
                }
            }
        })
        Log.i(TAG, "Watching WebView.postWebMessage for game ad promise results")
    }
}

private fun hookWebViewScriptDelivery(name: String, vararg parameterTypes: Class<*>) {
    runCatching {
        val method = WebView::class.java.getDeclaredMethod(name, *parameterTypes)
        method.isAccessible = true
        XposedBridge.hookMethod(method, object : XC_MethodHook() {
            override fun beforeHookedMethod(param: MethodHookParam) {
                val script = param.args.getOrNull(0) as? String ?: return
                val rewritten = rewriteGameAdDeliveryIfNeeded(script, name) ?: return
                param.args[0] = rewritten
            }
        })
        Log.i(TAG, "Watching WebView.$name for game ad promise results")
    }
}

private fun rewriteGameAdDeliveryIfNeeded(delivery: String, source: String): String? {
    if (gameAdPromiseSnapshots.isEmpty()) return null
    val promiseIds = gameAdPromiseSnapshots.keys.filter { delivery.contains(it) }
    if (promiseIds.isEmpty()) return null

    var result: String? = null
    promiseIds.forEach { promiseId ->
        val snapshot = gameAdPromiseSnapshots[promiseId] ?: return@forEach
        logGameAdDeliveryDiagnostic(delivery, promiseId, snapshot.messageType, source)
        if (!shouldForceGameAdSuccess(snapshot.payload, snapshot.messageType)) return@forEach

        val rewritten = rewritePromiseJsonInDelivery(delivery, promiseId, snapshot) ?: return@forEach
        if (rewritten != null && rewritten != delivery) {
            result = rewritten
        }
    }
    return result
}

// Logs the raw delivery for tracked promises so an unexpected response shape
// can be diagnosed from a single repro.
private fun logGameAdDeliveryDiagnostic(delivery: String, promiseId: String, messageType: String?, source: String) {
    val seen = gameAdScriptDiagnostics.incrementAndGet()
    if (seen > 40) return
    Log.i(
        TAG,
        "Game ad promise delivery source=$source type=$messageType promise=$promiseId " +
            "script=${delivery.take(900)}"
    )
}

// Rewrites the JSON object containing the promiseId inside the delivery
// script: error fields are dropped, success/reward outcome fields are forced.
private fun rewritePromiseJsonInDelivery(
    delivery: String,
    promiseId: String,
    snapshot: GameAdPromiseSnapshot
): String? {
    return runCatching {
        val index = delivery.indexOf(promiseId)
        if (index < 0) return null

        var start = delivery.lastIndexOf('{', index)
        if (start < 0) return null

        // Expand to an enclosing object when the promiseId is nested (e.g.
        // inside "content") — the rewrite should cover the whole response.
        while (start > 0) {
            val outerStart = delivery.lastIndexOf('{', start - 1)
            if (outerStart < 0) break
            val outer = extractBalancedJson(delivery, outerStart) ?: break
            if (!outer.contains(promiseId)) break
            start = outerStart
        }

        val balanced = extractBalancedJson(delivery, start) ?: return null
        val end = start + balanced.length - 1

        val originalJson = runCatching { JSONObject(delivery.substring(start, end + 1)) }.getOrNull()
            ?: return null
        val success = forceGameAdSuccessResult(
            promiseId = promiseId,
            original = originalJson,
            payload = snapshot.payload,
            messageType = snapshot.messageType
        )
        forceSuccessDeep(success, hasRewardGameAdSignal(snapshot.payload, snapshot.messageType))

        Log.i(
            TAG,
            "Rewrote game ad promise delivery promise=$promiseId type=${snapshot.messageType} " +
                "result=${success.toString().take(400)}"
        )
        delivery.substring(0, start) + success + delivery.substring(end + 1)
    }.getOrNull()
}

private fun extractBalancedJson(text: String, start: Int): String? {
    var depth = 0
    var inString = false
    var escaped = false
    var cursor = start
    while (cursor < text.length) {
        val c = text[cursor]
        if (escaped) {
            escaped = false
        } else if (c == '\\') {
            escaped = true
        } else if (c == '"') {
            inString = !inString
        } else if (!inString) {
            if (c == '{') depth++
            else if (c == '}') {
                depth--
                if (depth == 0) return text.substring(start, cursor + 1)
            }
        }
        cursor++
    }
    return null
}

// Outcome fields can live at the top level or inside "content"; error payloads
// at any level are dropped so the game cannot read a failure reason.
private fun forceSuccessDeep(json: JSONObject, reward: Boolean) {
    val keys = ArrayList<String>()
    val keyIterator = json.keys()
    while (keyIterator.hasNext()) {
        keys.add(keyIterator.next() as String)
    }
    keys.forEach { key ->
        val value = json.opt(key)
        when {
            key == "error" || key == "errorMessage" ||
                (key == "code" && json.opt(key) is String) ->
                json.remove(key)
            value is JSONObject -> forceSuccessDeep(value, reward)
            else -> Unit
        }
    }
    if (json.has("success") || json.has("error") || reward || json.has("completed")) {
        json.put("success", true)
        if (reward) {
            json.put("completed", true)
            json.put("didComplete", true)
            json.put("watched", true)
            json.put("rewarded", true)
            json.put("completionGesture", "post")
        }
    }
}

private fun hookGameAdResultMethods(bridgeClass: Class<*>) {
    if (!gameAdResultHookedClasses.add(bridgeClass.name)) return

    val resolveMethod = resolveGameAdResolveMethod(bridgeClass)
    val rejectMethod = resolveGameAdRejectMethod(bridgeClass)
    val bridgeRejectMethod = resolveGameAdBridgeRejectMethod(bridgeClass)
    var hooked = 0

    resolveMethod?.let { method ->
        XposedBridge.hookMethod(method, object : XC_MethodHook() {
            override fun beforeHookedMethod(param: MethodHookParam) {
                val promiseId = param.args.getOrNull(0) as? String ?: return
                val snapshot = gameAdPromiseSnapshots[promiseId] ?: return
                markGameAdDiagnosticFlow("resolve ${method.declaringClass.name}.${method.name}")
                logGameAdDiagnostic(
                    "resolve.before",
                    "${methodSignature(method)} promise=$promiseId snapshotType=${snapshot.messageType} args=${formatDiagArgs(param.args)}"
                )
                if (snapshot.messageType !in GAME_AD_MESSAGE_TYPES) return
                if (!ENABLE_GAME_AD_AUTOFIX) return
                if (!shouldForceGameAdSuccess(snapshot.payload, snapshot.messageType)) return

                val original = param.args.getOrNull(1)
                param.args[1] = forceGameAdSuccessResult(
                    promiseId = promiseId,
                    original = original,
                    payload = snapshot.payload,
                    messageType = snapshot.messageType
                )
                Log.i(TAG, "Forced successful game ad resolve promise=$promiseId type=${snapshot.messageType}")
            }

            override fun afterHookedMethod(param: MethodHookParam) {
                val promiseId = param.args.getOrNull(0) as? String ?: return
                val snapshot = gameAdPromiseSnapshots[promiseId] ?: return
                logGameAdDiagnostic(
                    "resolve.after",
                    "${methodSignature(method)} promise=$promiseId snapshotType=${snapshot.messageType} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                )
            }
        })
        hooked++
    }

    if (rejectMethod != null && resolveMethod != null) {
        XposedBridge.hookMethod(rejectMethod, object : XC_MethodHook() {
            override fun beforeHookedMethod(param: MethodHookParam) {
                val promiseId = param.args.getOrNull(0) as? String ?: return
                val reason = param.args.drop(1).joinToString(" ") { it?.toString().orEmpty() }
                if (gameAdPromiseSnapshots.containsKey(promiseId) || isRecentGameAdDiagnosticFlow() || reason.hasGameAdSignal()) {
                    markGameAdDiagnosticFlow("reject ${rejectMethod.declaringClass.name}.${rejectMethod.name}")
                    logGameAdDiagnostic(
                        "reject.before",
                        "${methodSignature(rejectMethod)} promise=$promiseId snapshotType=${gameAdPromiseSnapshots[promiseId]?.messageType} args=${formatDiagArgs(param.args)}"
                    )
                }
                if (!ENABLE_GAME_AD_AUTOFIX) return
                if (!shouldConvertGameAdRejectToSuccess(promiseId, reason)) return

                val snapshot = gameAdPromiseSnapshots[promiseId]
                val success = forceGameAdSuccessResult(
                    promiseId = promiseId,
                    original = null,
                    payload = snapshot?.payload,
                    messageType = snapshot?.messageType ?: gameAdPromiseTypeFromReason(reason)
                )
                runCatching {
                    XposedBridge.invokeOriginalMethod(resolveMethod, param.thisObject, arrayOf(promiseId, success))
                    param.result = null
                    Log.i(
                        TAG,
                        "Converted game ad reject to success promise=$promiseId type=${snapshot?.messageType} reason=$reason"
                    )
                }.onFailure {
                    Log.w(TAG, "Failed to convert game ad reject to success promise=$promiseId", it)
                }
            }

            override fun afterHookedMethod(param: MethodHookParam) {
                val promiseId = param.args.getOrNull(0) as? String ?: return
                val reason = param.args.drop(1).joinToString(" ") { it?.toString().orEmpty() }
                if (gameAdPromiseSnapshots.containsKey(promiseId) || isRecentGameAdDiagnosticFlow() || reason.hasGameAdSignal()) {
                    logGameAdDiagnostic(
                        "reject.after",
                        "${methodSignature(rejectMethod)} promise=$promiseId result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                    )
                }
            }
        })
        hooked++
    }

    if (bridgeRejectMethod != null && resolveMethod != null && bridgeRejectMethod != rejectMethod) {
        XposedBridge.hookMethod(bridgeRejectMethod, object : XC_MethodHook() {
            override fun beforeHookedMethod(param: MethodHookParam) {
                val payload = param.args.getOrNull(2) as? JSONObject ?: return
                val promiseId = extractPromiseId(payload) ?: return
                val reason = param.args.take(2).joinToString(" ") { it?.toString().orEmpty() }
                if (gameAdPromiseSnapshots.containsKey(promiseId) || isRecentGameAdDiagnosticFlow() || reason.hasGameAdSignal()) {
                    markGameAdDiagnosticFlow("bridgeReject ${bridgeRejectMethod.declaringClass.name}.${bridgeRejectMethod.name}")
                    logGameAdDiagnostic(
                        "bridgeReject.before",
                        "${methodSignature(bridgeRejectMethod)} promise=$promiseId snapshotType=${gameAdPromiseSnapshots[promiseId]?.messageType} args=${formatDiagArgs(param.args)}"
                    )
                }
                if (!ENABLE_GAME_AD_AUTOFIX) return
                if (!shouldConvertGameAdRejectToSuccess(promiseId, reason)) return

                val snapshot = gameAdPromiseSnapshots[promiseId]
                val success = forceGameAdSuccessResult(
                    promiseId = promiseId,
                    original = null,
                    payload = snapshot?.payload ?: payload,
                    messageType = snapshot?.messageType ?: gameAdPromiseTypeFromReason(reason)
                )
                runCatching {
                    XposedBridge.invokeOriginalMethod(resolveMethod, param.thisObject, arrayOf(promiseId, success))
                    param.result = null
                    Log.i(
                        TAG,
                        "Converted game ad bridge reject to success promise=$promiseId type=${snapshot?.messageType} reason=$reason"
                    )
                }.onFailure {
                    Log.w(TAG, "Failed to convert game ad bridge reject to success promise=$promiseId", it)
                }
            }

            override fun afterHookedMethod(param: MethodHookParam) {
                val payload = param.args.getOrNull(2) as? JSONObject ?: return
                val promiseId = extractPromiseId(payload) ?: return
                val reason = param.args.take(2).joinToString(" ") { it?.toString().orEmpty() }
                if (gameAdPromiseSnapshots.containsKey(promiseId) || isRecentGameAdDiagnosticFlow() || reason.hasGameAdSignal()) {
                    logGameAdDiagnostic(
                        "bridgeReject.after",
                        "${methodSignature(bridgeRejectMethod)} promise=$promiseId result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                    )
                }
            }
        })
        hooked++
    }

    Log.i(TAG, "Hooked $hooked game ad result helper method(s) in ${bridgeClass.name}")
}

private fun hookGameAdServiceDispatchMethods(bridgeClass: Class<*>) {
    if (!gameAdServiceDispatchHookedClasses.add(bridgeClass.name)) return

    val methods = (bridgeClass.declaredMethods + bridgeClass.methods)
        .filter { method ->
            !Modifier.isStatic(method.modifiers) &&
                method.returnType == Void.TYPE &&
                method.parameterCount == 2 &&
                method.parameterTypes[0] == Bundle::class.java
        }
        .distinctBy { method ->
            method.name + method.parameterTypes.joinToString(prefix = "(", postfix = ")") { it.name }
        }

    var hooked = 0
    methods.forEach { method ->
        method.isAccessible = true
        XposedBridge.hookMethod(method, object : XC_MethodHook() {
            override fun beforeHookedMethod(param: MethodHookParam) {
                val bundle = param.args.getOrNull(0) as? Bundle ?: return
                val messageType = param.args.getOrNull(1)?.toString()?.lowercase()
                    ?.takeIf { it in GAME_AD_MESSAGE_TYPES } ?: return
                val payload = buildGameAdPayloadFromServiceBundle(bundle, messageType)

                markGameAdDiagnosticFlow("serviceDispatch ${method.declaringClass.name}.${method.name}")
                logGameAdDiagnostic(
                    "serviceDispatch.before",
                    "${methodSignature(method)} type=$messageType args=${formatDiagArgs(param.args)}"
                )
                rememberGameAdPayload(param.thisObject, payload, messageType)
                if (!ENABLE_GAME_AD_AUTOFIX) return
                if (!shouldForceGameAdSuccess(payload, messageType)) return

                if (resolveGameAdPayload(param.thisObject, payload, messageType)) {
                    dispatchPostResolveGameAdSignals(param.thisObject, payload, messageType)
                    param.result = null
                    Log.i(
                        TAG,
                        "Resolved game ad service dispatch type=$messageType in ${method.declaringClass.name}.${method.name}"
                    )
                }
            }

            override fun afterHookedMethod(param: MethodHookParam) {
                val bundle = param.args.getOrNull(0) as? Bundle ?: return
                val messageType = param.args.getOrNull(1)?.toString()?.lowercase()
                    ?.takeIf { it in GAME_AD_MESSAGE_TYPES } ?: return
                logGameAdDiagnostic(
                    "serviceDispatch.after",
                    "${methodSignature(method)} type=$messageType result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                )
            }
        })
        hooked++
    }

    Log.i(TAG, "Hooked $hooked game ad service dispatch method(s) in ${bridgeClass.name}")
}

private fun hookGameAdSystemDiagnostics(classLoader: ClassLoader) {
    if (!ENABLE_GAME_AD_DIAGNOSTICS || !gameAdSystemDiagnosticsInstalled.compareAndSet(0, 1)) return

    hookMessengerSendDiagnostics()
    hookHandlerMessageDiagnostics(classLoader)
    hookActivityResultDiagnostics()
    hookAudienceNetworkViewDiagnostics()
    hookDynamicGameAdClassDiagnostics(classLoader)

    Log.i(
        TAG,
        "Hooked passive game ad diagnostic probes: marker=$BUILD_MARKER " +
            "broadHandler=$ENABLE_BROAD_HANDLER_GAME_AD_DIAGNOSTICS " +
            "anView=$ENABLE_AUDIENCE_NETWORK_VIEW_DIAGNOSTICS cap=$GAME_AD_DIAG_LOG_LIMIT"
    )
}

private fun hookMessengerSendDiagnostics() {
    val sendMethods = (Messenger::class.java.declaredMethods + Messenger::class.java.methods)
        .filter { method ->
            method.name == "send" &&
                method.parameterCount == 1 &&
                method.parameterTypes[0] == Message::class.java
        }
        .distinctBy { methodSignature(it) }

    sendMethods.forEach { method ->
        method.isAccessible = true
        XposedBridge.hookMethod(method, object : XC_MethodHook() {
            override fun beforeHookedMethod(param: MethodHookParam) {
                val message = param.args.getOrNull(0) as? Message ?: return
                if (!shouldLogGameAdMessage(message)) return
                markGameAdDiagnosticFlow("messenger.send")
                logGameAdDiagnostic(
                    "messenger.send.before",
                    "${methodSignature(method)} this=${formatDiagValue(param.thisObject)} message=${formatDiagValue(message)}"
                )
            }

            override fun afterHookedMethod(param: MethodHookParam) {
                val message = param.args.getOrNull(0) as? Message ?: return
                if (!shouldLogGameAdMessage(message)) return
                logGameAdDiagnostic(
                    "messenger.send.after",
                    "${methodSignature(method)} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                )
            }
        })
    }
}

private fun hookHandlerMessageDiagnostics(classLoader: ClassLoader) {
    if (ENABLE_BROAD_HANDLER_GAME_AD_DIAGNOSTICS) {
        (Handler::class.java.declaredMethods + Handler::class.java.methods)
            .filter { method ->
                method.name == "dispatchMessage" &&
                    method.parameterCount == 1 &&
                    method.parameterTypes[0] == Message::class.java
            }
            .distinctBy { methodSignature(it) }
            .forEach { method ->
                method.isAccessible = true
                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        val message = param.args.getOrNull(0) as? Message ?: return
                        val handlerName = param.thisObject?.javaClass?.name.orEmpty()
                        if (!shouldLogGameAdMessage(message) && !handlerName.contains("C95084edO") && !handlerName.contains("HandlerC95084edO")) {
                            return
                        }
                        markGameAdDiagnosticFlow("handler.dispatch $handlerName")
                        logGameAdDiagnostic(
                            "handler.dispatch.before",
                            "handler=$handlerName ${methodSignature(method)} message=${formatDiagValue(message)}"
                        )
                    }

                    override fun afterHookedMethod(param: MethodHookParam) {
                        val message = param.args.getOrNull(0) as? Message ?: return
                        val handlerName = param.thisObject?.javaClass?.name.orEmpty()
                        if (!shouldLogGameAdMessage(message)) {
                            return
                        }
                        logGameAdDiagnostic(
                            "handler.dispatch.after",
                            "handler=$handlerName result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                        )
                    }
                })
            }
    }
}

private fun hookActivityResultDiagnostics() {
    (Activity::class.java.declaredMethods + Activity::class.java.methods)
        .filter { method ->
            (method.name == "setResult" && method.parameterTypes.firstOrNull() == Int::class.javaPrimitiveType) ||
                (method.name in setOf("finish", "onPause", "onStop", "onDestroy") && method.parameterCount == 0) ||
                (method.name == "onActivityResult" &&
                    method.parameterCount == 3 &&
                    method.parameterTypes[0] == Int::class.javaPrimitiveType &&
                    method.parameterTypes[1] == Int::class.javaPrimitiveType &&
                    method.parameterTypes[2] == Intent::class.java)
        }
        .distinctBy { methodSignature(it) }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    val activity = param.thisObject as? Activity ?: return
                    if (!shouldLogGameAdActivityDiagnostic(activity, param.args)) return
                    markGameAdDiagnosticFlow("activity.${method.name} ${activity.javaClass.name}")
                    logGameAdDiagnostic(
                        "activity.${method.name}.before",
                        "${activity.javaClass.name} ${methodSignature(method)} args=${formatDiagArgs(param.args)} intent=${formatDiagValue(activity.intent)}"
                    )
                    if (method.name == "finish") {
                        dumpAudienceNetworkActivityState(activity, "activity.finish.before")
                    }
                }

                override fun afterHookedMethod(param: MethodHookParam) {
                    val activity = param.thisObject as? Activity ?: return
                    if (!shouldLogGameAdActivityDiagnostic(activity, param.args)) return
                    logGameAdDiagnostic(
                        "activity.${method.name}.after",
                        "${activity.javaClass.name} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                    )
                }
            })
        }

    (Instrumentation::class.java.declaredMethods + Instrumentation::class.java.methods)
        .filter { method ->
            method.name == "callActivityOnActivityResult" &&
                method.parameterCount == 4 &&
                Activity::class.java.isAssignableFrom(method.parameterTypes[0]) &&
                method.parameterTypes[1] == Int::class.javaPrimitiveType &&
                method.parameterTypes[2] == Int::class.javaPrimitiveType &&
                method.parameterTypes[3] == Intent::class.java
        }
        .distinctBy { methodSignature(it) }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    val activity = param.args.getOrNull(0) as? Activity ?: return
                    if (!shouldLogGameAdActivityDiagnostic(activity, param.args)) return
                    markGameAdDiagnosticFlow("instrumentation.activityResult ${activity.javaClass.name}")
                    logGameAdDiagnostic(
                        "instrumentation.activityResult.before",
                        "${methodSignature(method)} args=${formatDiagArgs(param.args)}"
                    )
                }

                override fun afterHookedMethod(param: MethodHookParam) {
                    val activity = param.args.getOrNull(0) as? Activity ?: return
                    if (!shouldLogGameAdActivityDiagnostic(activity, param.args)) return
                    logGameAdDiagnostic(
                        "instrumentation.activityResult.after",
                        "${methodSignature(method)} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                    )
                }
            })
        }
}

private fun hookAudienceNetworkViewDiagnostics() {
    if (!ENABLE_AUDIENCE_NETWORK_VIEW_DIAGNOSTICS ||
        !audienceNetworkViewDiagnosticsInstalled.compareAndSet(0, 1)
    ) {
        return
    }

    val viewMethods = (View::class.java.declaredMethods + View::class.java.methods)
        .filter { method ->
            when (method.name) {
                "performClick", "callOnClick" -> method.parameterCount == 0
                "setOnClickListener" -> method.parameterCount == 1 &&
                    View.OnClickListener::class.java.isAssignableFrom(method.parameterTypes[0])
                "setOnTouchListener" -> method.parameterCount == 1 &&
                    View.OnTouchListener::class.java.isAssignableFrom(method.parameterTypes[0])
                else -> false
            }
        }
        .distinctBy { methodSignature(it) }

    viewMethods.forEach { method ->
        runCatching {
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    val view = param.thisObject as? View ?: return
                    val shouldLogView = shouldLogAudienceNetworkViewDiagnostic(view, param.args)
                    param.args.getOrNull(0)?.takeIf {
                        shouldLogView || shouldHookAudienceNetworkListenerClass(it.javaClass.name)
                    }?.let { listener ->
                        tryHookAudienceNetworkViewListenerClass(listener.javaClass, "View.${method.name}")
                    }
                    findViewOnClickListener(view)?.takeIf {
                        shouldLogView || shouldHookAudienceNetworkListenerClass(it.javaClass.name)
                    }?.let { listener ->
                        tryHookAudienceNetworkViewListenerClass(listener.javaClass, "View.${method.name}.existingClick")
                    }
                    findViewOnTouchListener(view)?.takeIf {
                        shouldLogView || shouldHookAudienceNetworkListenerClass(it.javaClass.name)
                    }?.let { listener ->
                        tryHookAudienceNetworkViewListenerClass(listener.javaClass, "View.${method.name}.existingTouch")
                    }
                    if (!shouldLogView) return

                    markGameAdDiagnosticFlow("anView.${method.name} ${view.javaClass.name}")
                    logGameAdDiagnostic(
                        "anView.${method.name}.before",
                        "${methodSignature(method)} ${describeAudienceNetworkView(view)} args=${formatDiagArgs(param.args)}"
                    )
                }

                override fun afterHookedMethod(param: MethodHookParam) {
                    val view = param.thisObject as? View ?: return
                    if (!shouldLogAudienceNetworkViewDiagnostic(view, param.args) && !isRecentGameAdDiagnosticFlow()) return

                    logGameAdDiagnostic(
                        "anView.${method.name}.after",
                        "${methodSignature(method)} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)} ${describeAudienceNetworkView(view)}"
                    )
                }
            })
        }.onFailure {
            Log.w(TAG, "Failed to hook Audience Network view diagnostic ${method.declaringClass.name}.${method.name}", it)
        }
    }

    Log.i(TAG, "Hooked ${viewMethods.size} Audience Network view diagnostic method(s)")
}

private fun dumpAudienceNetworkActivityState(activity: Activity, source: String) {
    if (activity.javaClass.name !in setOf(AUDIENCE_NETWORK_ACTIVITY_CLASS, AUDIENCE_NETWORK_REMOTE_ACTIVITY_CLASS)) {
        return
    }

    val now = System.currentTimeMillis()
    val shouldDump = synchronized(audienceNetworkActivityStateDumps) {
        val previous = audienceNetworkActivityStateDumps[activity]
        if (previous != null && now - previous < 2_000L) {
            false
        } else {
            audienceNetworkActivityStateDumps[activity] = now
            true
        }
    }
    if (!shouldDump) return

    logGameAdDiagnostic(
        "anActivity.dump",
        "$source activity=${activity.javaClass.name} intent=${formatDiagValue(activity.intent)}"
    )
    dumpAudienceNetworkIntentExtras(activity.intent, source)
    dumpAudienceNetworkViewState(activity, source)
    dumpAudienceNetworkObjectGraph(activity, source)
}

private fun dumpAudienceNetworkIntentExtras(intent: Intent?, source: String) {
    val extras = intent?.extras ?: return
    val keys = runCatching { extras.keySet().toList() }.getOrDefault(emptyList())
    keys.take(24).forEach { key ->
        val value = runCatching { extras.get(key) }.getOrNull()
        logGameAdDiagnostic(
            "anActivity.intentExtra",
            "$source $key=${formatDiagValue(value)}"
        )
    }
}

private fun dumpAudienceNetworkViewState(activity: Activity, source: String) {
    val root = activity.window?.decorView ?: return

    collectAudienceNetworkCloseCandidates(root)
        .take(12)
        .forEachIndexed { index, view ->
            logGameAdDiagnostic(
                "anView.closeCandidate",
                "$source #$index score=${audienceNetworkCloseCandidateScore(view, root)} ${describeAudienceNetworkView(view)}"
            )
        }

    var logged = 0
    fun visit(view: View, depth: Int) {
        if (logged < 80 && shouldDescribeAudienceNetworkViewInTree(view)) {
            findViewOnClickListener(view)?.let { listener ->
                tryHookAudienceNetworkViewListenerClass(listener.javaClass, "viewTree.clickListener")
            }
            findViewOnTouchListener(view)?.let { listener ->
                tryHookAudienceNetworkViewListenerClass(listener.javaClass, "viewTree.touchListener")
            }
            logged++
            logGameAdDiagnostic(
                "anView.tree",
                "$source depth=$depth ${describeAudienceNetworkView(view)}"
            )
        }

        val group = view as? ViewGroup ?: return
        for (index in 0 until group.childCount) {
            visit(group.getChildAt(index), depth + 1)
        }
    }

    visit(root, 0)
}

private fun dumpAudienceNetworkObjectGraph(activity: Activity, source: String) {
    val seen = IdentityHashMap<Any, Boolean>()
    val queue = java.util.ArrayDeque<AudienceNetworkGraphNode>()
    queue.add(AudienceNetworkGraphNode(activity, "activity", 0))

    var inspected = 0
    var logged = 0
    while (!queue.isEmpty() && inspected < AUDIENCE_NETWORK_STATE_DUMP_LIMIT && logged < AUDIENCE_NETWORK_STATE_DUMP_LIMIT) {
        val node = queue.removeFirst()
        val value = node.value
        if (seen.put(value, true) != null) continue
        inspected++

        if (value !== activity) {
            logged++
            tryHookAudienceNetworkDiagnosticObjectClass(value.javaClass, "graph ${node.path}")
            logGameAdDiagnostic(
                "anActivity.object",
                "$source ${node.path}=${formatDiagValue(value)} methods=${audienceNetworkInterestingMethodsSummary(value.javaClass)}"
            )
        }

        if (node.depth >= 4) continue

        audienceNetworkFieldsFor(value.javaClass).forEach { field ->
            val fieldValue = runCatching { field.get(value) }.getOrNull() ?: return@forEach
            val fieldPath = "${node.path}.${field.name}"
            when (fieldValue) {
                is View -> {
                    tryHookAudienceNetworkDiagnosticObjectClass(fieldValue.javaClass, "graph view $fieldPath")
                    logGameAdDiagnostic(
                        "anActivity.field",
                        "$source $fieldPath=${describeAudienceNetworkView(fieldValue)}"
                    )
                }
                is Iterable<*> -> fieldValue.take(12).forEachIndexed { index, item ->
                    if (item != null && shouldQueueAudienceNetworkDiagnosticObject(item)) {
                        queue.add(AudienceNetworkGraphNode(item, "$fieldPath[$index]", node.depth + 1))
                    }
                }
                is Array<*> -> fieldValue.take(12).forEachIndexed { index, item ->
                    if (item != null && shouldQueueAudienceNetworkDiagnosticObject(item)) {
                        queue.add(AudienceNetworkGraphNode(item, "$fieldPath[$index]", node.depth + 1))
                    }
                }
                else -> if (shouldQueueAudienceNetworkDiagnosticObject(fieldValue)) {
                    queue.add(AudienceNetworkGraphNode(fieldValue, fieldPath, node.depth + 1))
                } else if (isGameAdDiagnosticValue(fieldValue)) {
                    logGameAdDiagnostic(
                        "anActivity.field",
                        "$source $fieldPath=${formatDiagValue(fieldValue)}"
                    )
                }
            }
        }
    }

    logGameAdDiagnostic("anActivity.dumpDone", "$source inspected=$inspected logged=$logged")
}

private fun tryHookAudienceNetworkDiagnosticObjectClass(clazz: Class<*>, source: String) {
    if (isGameAdDiagnosticClassName(clazz.name)) {
        tryHookGameAdDiagnosticClass(clazz)
    }
    if (isPotentialAudienceNetworkAppClass(clazz.name)) {
        tryHookAudienceNetworkViewListenerClass(clazz, source)
    }
}

private fun tryHookAudienceNetworkViewListenerClass(clazz: Class<*>, source: String) {
    val className = clazz.name
    if (!shouldHookAudienceNetworkListenerClass(className) ||
        !audienceNetworkViewListenerClassesHooked.add(className)
    ) {
        return
    }

    var hooked = 0
    val methods = runCatching { clazz.declaredMethods }.getOrDefault(emptyArray())
    methods.asSequence()
        .filter { method -> isAudienceNetworkViewListenerDiagnosticMethod(method) }
        .distinctBy { methodSignature(it) }
        .take(24)
        .forEach { method ->
            runCatching {
                method.isAccessible = true
                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        if (!shouldLogAudienceNetworkListenerCall(method, param.args)) return
                        markGameAdDiagnosticFlow("anListener.${method.name} ${method.declaringClass.name}")
                        logGameAdDiagnostic(
                            "anListener.${method.name}.before",
                            "${methodSignature(method)} this=${formatDiagValue(param.thisObject)} args=${formatDiagArgs(param.args)}"
                        )
                    }

                    override fun afterHookedMethod(param: MethodHookParam) {
                        if (!shouldLogAudienceNetworkListenerCall(method, param.args) && !isRecentGameAdDiagnosticFlow()) return
                        logGameAdDiagnostic(
                            "anListener.${method.name}.after",
                            "${methodSignature(method)} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                        )
                    }
                })
                hooked++
            }.onFailure {
                Log.w(TAG, "Failed to hook Audience Network listener diagnostic ${clazz.name}.${method.name}", it)
            }
        }

    if (hooked > 0) {
        logGameAdDiagnostic(
            "anListener.hooked",
            "$source class=$className hooked=$hooked methods=${audienceNetworkInterestingMethodsSummary(clazz)}"
        )
    }
}

private fun isAudienceNetworkViewListenerDiagnosticMethod(method: Method): Boolean {
    if (method.declaringClass == Any::class.java || method.isSynthetic || method.isBridge) return false
    if (Modifier.isStatic(method.modifiers) || method.parameterCount > 6) return false
    if (method.name in setOf("wait", "notify", "notifyAll", "hashCode", "equals", "toString")) return false

    val methodName = method.name.lowercase()
    if (methodName in setOf("onclick", "ontouch")) return true
    return method.parameterTypes.any { type ->
        isGameAdDiagnosticClassName(type.name)
    } || isGameAdDiagnosticClassName(method.returnType.name)
}

private fun shouldLogAudienceNetworkListenerCall(method: Method, args: Array<Any?>?): Boolean {
    if (args.orEmpty().any { value -> value is View && shouldLogAudienceNetworkViewDiagnostic(value, null) }) {
        return true
    }
    val methodName = method.name.lowercase()
    return isRecentGameAdDiagnosticFlow() &&
        (methodName in setOf("onclick", "ontouch") ||
            methodName.hasAudienceNetworkViewSignal() ||
            methodName.hasGameAdSignal())
}

private fun shouldLogAudienceNetworkViewDiagnostic(view: View, args: Array<Any?>?): Boolean {
    val activity = contextActivityForView(view)
    if (activity?.javaClass?.name in setOf(AUDIENCE_NETWORK_ACTIVITY_CLASS, AUDIENCE_NETWORK_REMOTE_ACTIVITY_CLASS)) {
        return true
    }

    if (view.javaClass.name.hasGameAdSignal() || audienceNetworkViewMarker(view).hasAudienceNetworkViewSignal()) {
        return true
    }

    if (audienceNetworkParentPath(view).hasGameAdSignal()) return true

    return args.orEmpty().any { value ->
        value?.javaClass?.name?.let { shouldHookAudienceNetworkListenerClass(it) || it.hasGameAdSignal() } == true ||
            isGameAdDiagnosticValue(value)
    }
}

private fun shouldDescribeAudienceNetworkViewInTree(view: View): Boolean {
    if (view.javaClass.name.hasGameAdSignal()) return true
    val marker = audienceNetworkViewMarker(view)
    if (marker.hasAudienceNetworkViewSignal()) return true
    if (view.isClickable || findViewOnClickListener(view) != null || findViewOnTouchListener(view) != null) return true
    return audienceNetworkParentPath(view).hasGameAdSignal()
}

private fun describeAudienceNetworkView(view: View): String {
    val location = IntArray(2)
    val locationText = runCatching {
        view.getLocationOnScreen(location)
        "${location[0]},${location[1]}"
    }.getOrDefault("?,?")

    val clickListener = findViewOnClickListener(view)?.javaClass?.name ?: "null"
    val touchListener = findViewOnTouchListener(view)?.javaClass?.name ?: "null"
    val text = truncateDiag((view as? TextView)?.text?.toString().orEmpty(), 80)
    val description = truncateDiag(view.contentDescription?.toString().orEmpty(), 80)
    val activityName = contextActivityForView(view)?.javaClass?.name ?: "null"

    return "view=${view.javaClass.name}@${Integer.toHexString(System.identityHashCode(view))} " +
        "activity=$activityName id=${viewIdLabel(view)} shown=${view.isShown} enabled=${view.isEnabled} " +
        "clickable=${view.isClickable} size=${view.width}x${view.height} loc=$locationText " +
        "text=\"$text\" desc=\"$description\" clickListener=$clickListener touchListener=$touchListener " +
        "parents=${audienceNetworkParentPath(view)}"
}

private fun viewIdLabel(view: View): String {
    if (view.id == View.NO_ID) return "NO_ID"
    return runCatching { view.resources.getResourceName(view.id) }.getOrDefault(view.id.toString())
}

private fun audienceNetworkViewMarker(view: View): String {
    return buildString {
        append(view.javaClass.name)
        append(' ')
        append(view.contentDescription?.toString().orEmpty())
        append(' ')
        append((view as? TextView)?.text?.toString().orEmpty())
        append(' ')
        append(viewIdLabel(view))
    }.lowercase()
}

private fun audienceNetworkParentPath(view: View): String {
    val names = ArrayList<String>()
    var current = view.parent
    var depth = 0
    while (current != null && depth < 8) {
        names.add(current.javaClass.name)
        current = (current as? View)?.parent
        depth++
    }
    return names.joinToString(">")
}

private fun contextActivityForView(view: View): Activity? {
    var context = view.context
    var depth = 0
    while (depth < 8) {
        if (context is Activity) return context
        context = (context as? ContextWrapper)?.baseContext ?: return null
        depth++
    }
    return null
}

private fun findViewOnClickListener(view: View): Any? {
    return findViewListenerInfoField(view, "mOnClickListener")
}

private fun findViewOnTouchListener(view: View): Any? {
    return findViewListenerInfoField(view, "mOnTouchListener")
}

private fun findViewListenerInfoField(view: View, fieldName: String): Any? {
    return runCatching {
        val listenerInfoField = View::class.java.getDeclaredField("mListenerInfo").apply {
            isAccessible = true
        }
        val listenerInfo = listenerInfoField.get(view) ?: return@runCatching null
        val listenerField = listenerInfo.javaClass.getDeclaredField(fieldName).apply {
            isAccessible = true
        }
        listenerField.get(listenerInfo)
    }.getOrNull()
}

private fun shouldQueueAudienceNetworkDiagnosticObject(value: Any): Boolean {
    if (value is View ||
        value is Activity ||
        value is String ||
        value is Number ||
        value is Boolean ||
        value is CharSequence
    ) {
        return false
    }

    val type = value.javaClass
    if (type.isPrimitive || type.isEnum) return false
    val className = type.name
    if (className.startsWith("android.") ||
        className.startsWith("java.") ||
        className.startsWith("javax.") ||
        className.startsWith("kotlin.") ||
        className.startsWith("dalvik.") ||
        className.startsWith("libcore.")
    ) {
        return false
    }

    return shouldTraverseAudienceNetworkObject(value, false) ||
        isPotentialAudienceNetworkAppClass(className) ||
        className.hasGameAdSignal()
}

private fun isPotentialAudienceNetworkAppClass(className: String): Boolean {
    return className.startsWith("com.facebook.") ||
        className.startsWith("X.") ||
        className.startsWith("p000X.") ||
        className.hasGameAdSignal()
}

private fun shouldHookAudienceNetworkListenerClass(className: String): Boolean {
    return className.startsWith("com.facebook.ads.") ||
        className.contains("audiencenetwork", ignoreCase = true)
}

private fun audienceNetworkInterestingMethodsSummary(type: Class<*>): String {
    return runCatching {
        audienceNetworkMethodsFor(type)
            .asSequence()
            .filter { method ->
                method.parameterCount <= 4 &&
                    method.name !in setOf("wait", "notify", "notifyAll", "hashCode", "equals", "toString")
            }
            .take(24)
            .joinToString(";") { method ->
                "${method.name}(${method.parameterTypes.joinToString(",") { it.simpleName }})>${method.returnType.simpleName}"
            }
    }.getOrDefault("")
}

private fun String.hasAudienceNetworkViewSignal(): Boolean {
    val normalized = lowercase()
    return normalized.contains("close") ||
        normalized.contains("dismiss") ||
        normalized.contains("skip") ||
        normalized.contains("done") ||
        normalized.contains("click") ||
        normalized.contains("touch") ||
        normalized.contains("reward") ||
        normalized.contains("complete") ||
        normalized.contains("watched") ||
        normalized.contains("video") ||
        normalized.contains("interstitial") ||
        normalized.contains("adchoices") ||
        normalized.contains("ads served by meta") ||
        normalized.contains("audiencenetwork") ||
        normalized.contains("com.facebook.ads")
}

private fun hookDynamicGameAdClassDiagnostics(classLoader: ClassLoader) {
    if (!gameAdDynamicDiagnosticsInstalled.compareAndSet(0, 1)) return

    listOf(
        AUDIENCE_NETWORK_ACTIVITY_CLASS,
        AUDIENCE_NETWORK_REMOTE_ACTIVITY_CLASS,
        "com.facebook.quicksilver.webviewprocess.QuicksilverSeparateProcessAdsLoader"
    ).forEach { className ->
        runCatching { tryHookGameAdDiagnosticClass(classLoader.loadClass(className)) }
    }

    (ClassLoader::class.java.declaredMethods + ClassLoader::class.java.methods)
        .filter { method ->
            method.name == "loadClass" &&
                method.parameterTypes.isNotEmpty() &&
                method.parameterTypes[0] == String::class.java
        }
        .distinctBy { methodSignature(it) }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun afterHookedMethod(param: MethodHookParam) {
                    val className = param.args.getOrNull(0) as? String ?: return
                    val clazz = param.result as? Class<*> ?: return
                    if (!isGameAdDiagnosticClassName(className) && !isGameAdDiagnosticClassName(clazz.name)) return
                    logGameAdDiagnosticClass(clazz)
                    tryHookGameAdDiagnosticClass(clazz)
                }
            })
        }
}

private fun tryHookGameAdDiagnosticClass(clazz: Class<*>) {
    if (!ENABLE_GAME_AD_DIAGNOSTICS) return
    val className = clazz.name
    if (!isGameAdDiagnosticClassName(className) || !gameAdDiagnosticClassesHooked.add(className)) return

    val methods = runCatching { clazz.declaredMethods + clazz.methods }.getOrDefault(emptyArray())
    var hooked = 0
    methods
        .filter { method -> isGameAdDiagnosticMethod(clazz, method) }
        .distinctBy { methodSignature(it) }
        .take(28)
        .forEach { method ->
            runCatching {
                method.isAccessible = true
                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        if (!shouldLogGameAdDiagnosticCall(method, param.args)) return
                        markGameAdDiagnosticFlow("dynamic ${method.declaringClass.name}.${method.name}")
                        logGameAdDiagnostic(
                            "dynamic.before",
                            "${methodSignature(method)} this=${formatDiagValue(param.thisObject)} args=${formatDiagArgs(param.args)}"
                        )
                    }

                    override fun afterHookedMethod(param: MethodHookParam) {
                        if (!shouldLogGameAdDiagnosticCall(method, param.args) && !isRecentGameAdDiagnosticFlow()) return
                        logGameAdDiagnostic(
                            "dynamic.after",
                            "${methodSignature(method)} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                        )
                    }
                })
                hooked++
            }.onFailure {
                Log.w(TAG, "Failed to hook game ad diagnostic method ${clazz.name}.${method.name}", it)
            }
        }

    if (hooked > 0) {
        Log.i(TAG, "Hooked $hooked passive game ad diagnostic method(s) in $className")
    }
}

private fun logGameAdDiagnosticClass(clazz: Class<*>) {
    if (!gameAdDiagnosticClassesLogged.add(clazz.name)) return

    val methodSummary = runCatching {
        (clazz.declaredMethods + clazz.methods)
            .asSequence()
            .filter { isGameAdDiagnosticMethod(clazz, it) }
            .distinctBy { methodSignature(it) }
            .take(16)
            .joinToString(";") { method -> "${method.name}(${method.parameterTypes.joinToString(",") { it.simpleName }})>${method.returnType.simpleName}" }
    }.getOrDefault("")

    logGameAdDiagnostic(
        "class.loaded",
        "${clazz.name} super=${clazz.superclass?.name} interfaces=${clazz.interfaces.joinToString { it.name }} methods=$methodSummary"
    )
}

private fun markGameAdDiagnosticFlow(reason: String) {
    if (!ENABLE_GAME_AD_DIAGNOSTICS) return
    lastGameAdDiagnosticFlowMs.set(System.currentTimeMillis())
    logGameAdDiagnostic("flow.mark", reason)
}

private fun isRecentGameAdDiagnosticFlow(): Boolean {
    val timestamp = lastGameAdDiagnosticFlowMs.get()
    return timestamp > 0 && System.currentTimeMillis() - timestamp < GAME_AD_DIAG_FLOW_WINDOW_MS
}

private fun logGameAdDiagnostic(event: String, detail: String) {
    if (!ENABLE_GAME_AD_DIAGNOSTICS) return

    val count = gameAdDiagnosticLogCount.incrementAndGet()
    when {
        count <= GAME_AD_DIAG_LOG_LIMIT -> Log.i(TAG, "GADIAG[$count] $event ${truncateDiag(detail)}")
        count == GAME_AD_DIAG_LOG_LIMIT + 1 -> Log.i(TAG, "GADIAG log limit reached; suppressing further diagnostics")
    }
}

private fun methodSignature(method: Method): String {
    return "${method.declaringClass.name}.${method.name}(${method.parameterTypes.joinToString(",") { it.name }}):${method.returnType.name}"
}

private fun formatDiagArgs(args: Array<Any?>?): String {
    if (args == null) return "[]"
    return args.mapIndexed { index, value -> "$index=${formatDiagValue(value)}" }
        .joinToString(prefix = "[", postfix = "]")
}

private fun formatDiagThrowable(throwable: Throwable?): String {
    return throwable?.let { "${it.javaClass.name}:${it.message}" } ?: "none"
}

@Suppress("DEPRECATION")
private fun formatDiagValue(value: Any?, depth: Int = 0): String {
    if (value == null) return "null"
    if (depth >= 3) return shortObjectLabel(value)

    val formatted = when (value) {
        JSONObject.NULL -> "JSONObject.NULL"
        is String -> "\"${truncateDiag(value, 260)}\""
        is Number, is Boolean -> value.toString()
        is JSONObject -> truncateDiag(value.toString(), 620)
        is JSONArray -> truncateDiag(value.toString(), 620)
        is Bundle -> {
            val entries = runCatching { value.keySet().toList() }.getOrDefault(emptyList())
                .take(24)
                .joinToString(",") { key ->
                    "$key=${formatDiagValue(runCatching { value.get(key) }.getOrNull(), depth + 1)}"
                }
            "Bundle{$entries}"
        }
        is Intent -> {
            val extras = value.extras?.let { formatDiagValue(it, depth + 1) } ?: "null"
            "Intent{action=${value.action}, component=${value.component?.flattenToShortString()}, data=${value.data}, flags=0x${value.flags.toString(16)}, extras=$extras}"
        }
        is Message -> {
            val obj = formatDiagValue(value.obj, depth + 1)
            val data = formatDiagValue(runCatching { value.peekData() }.getOrNull(), depth + 1)
            "Message{what=${value.what}, arg1=${value.arg1}, arg2=${value.arg2}, obj=$obj, data=$data, replyTo=${value.replyTo}}"
        }
        is Activity -> "Activity{${value.javaClass.name} intent=${formatDiagValue(value.intent, depth + 1)}}"
        is View -> "View{${value.javaClass.name} shown=${value.isShown} size=${value.width}x${value.height} id=${value.id}}"
        is ByteArray -> "ByteArray{len=${value.size}, hex=${byteArrayHexPreview(value)}, ascii=\"${byteArrayAsciiPreview(value)}\"}"
        is Array<*> -> value.take(12).joinToString(prefix = "Array[", postfix = "]") { formatDiagValue(it, depth + 1) }
        is Iterable<*> -> value.take(12).joinToString(prefix = "${value.javaClass.name}[", postfix = "]") {
            formatDiagValue(it, depth + 1)
        }
        else -> "${value.javaClass.name}{${truncateDiag(runCatching { value.toString() }.getOrDefault(""), 360)}}"
    }

    return truncateDiag(formatted)
}

private fun shortObjectLabel(value: Any): String {
    return "${value.javaClass.name}@${Integer.toHexString(System.identityHashCode(value))}"
}

private fun byteArrayHexPreview(value: ByteArray): String {
    return value.take(48).joinToString(" ") { byte -> "%02x".format(byte.toInt() and 0xff) }
}

private fun byteArrayAsciiPreview(value: ByteArray): String {
    return value.take(96).joinToString("") { byte ->
        val code = byte.toInt() and 0xff
        if (code in 32..126) code.toChar().toString() else "."
    }
}

private fun truncateDiag(text: String, limit: Int = GAME_AD_DIAG_TEXT_LIMIT): String {
    return if (text.length <= limit) text else text.take(limit) + "...<truncated ${text.length - limit}>"
}

private fun shouldLogGameAdMessage(message: Message): Boolean {
    if (isGameAdDiagnosticValue(message.obj)) return true
    if (isGameAdDiagnosticValue(runCatching { message.peekData() }.getOrNull())) return true
    return isRecentGameAdDiagnosticFlow() && (message.obj is Bundle || runCatching { message.peekData() }.getOrNull() != null)
}

private fun shouldLogGameAdActivityDiagnostic(activity: Activity, args: Array<Any?>?): Boolean {
    return isGameAdInterestingActivity(activity) ||
        args.orEmpty().any { isGameAdDiagnosticValue(it) } ||
        (isRecentGameAdDiagnosticFlow() && activity.javaClass.name.lowercase().contains("quicksilver"))
}

private fun shouldLogGameAdDiagnosticCall(method: Method, args: Array<Any?>?): Boolean {
    return isRecentGameAdDiagnosticFlow() ||
        isGameAdDiagnosticClassName(method.declaringClass.name) ||
        method.name.hasGameAdSignal() ||
        args.orEmpty().any { isGameAdDiagnosticValue(it) }
}

private fun isGameAdDiagnosticMethod(clazz: Class<*>, method: Method): Boolean {
    if (method.declaringClass == Any::class.java || method.isSynthetic || method.isBridge) return false
    if (method.name in setOf("wait", "notify", "notifyAll", "hashCode", "equals", "toString")) return false
    if (method.parameterCount > 8) return false

    val strongClass = isGameAdDiagnosticClassName(clazz.name)
    val methodName = method.name.lowercase()
    val signatureSignal = method.parameterTypes.any { isGameAdDiagnosticClassName(it.name) || it == Bundle::class.java || it == Intent::class.java || it == Message::class.java || it == JSONObject::class.java } ||
        isGameAdDiagnosticClassName(method.returnType.name)

    return (strongClass && method.parameterCount <= 6) ||
        methodName.hasGameAdSignal() ||
        signatureSignal
}

private fun isGameAdDiagnosticClassName(className: String): Boolean {
    val normalized = className.lowercase()
    val simple = normalized.substringAfterLast('.')
    return normalized.startsWith("com.facebook.ads.") ||
        normalized.contains("audiencenetwork") ||
        normalized.contains("instantgamesads") ||
        normalized.contains("neko.playables") ||
        (normalized.contains("quicksilver") && normalized.contains("ad")) ||
        simple in setOf(
            "adsregistry",
            "adsregistry\$adrecord",
            "audiencenetworkremoteserviceapiimpl",
            "audiencenetworkexportedactivityapiimpl",
            "clientmessagedispatchhelper"
        )
}

private fun isGameAdInterestingActivity(activity: Activity): Boolean {
    val className = activity.javaClass.name.lowercase()
    return activity.javaClass.name in GAME_AD_ACTIVITY_CLASS_NAMES ||
        className.contains("audiencenetwork") ||
        className.contains("neko.playables") ||
        className.contains("quicksilver")
}

@Suppress("DEPRECATION")
private fun isGameAdDiagnosticValue(value: Any?, depth: Int = 0): Boolean {
    if (value == null || depth > 3) return false
    return when (value) {
        is String -> value.hasGameAdSignal()
        is JSONObject -> value.toString().hasGameAdSignal()
        is JSONArray -> value.toString().hasGameAdSignal()
        is Bundle -> runCatching {
            value.keySet().any { key ->
                key.hasGameAdSignal() || isGameAdDiagnosticValue(value.get(key), depth + 1)
            }
        }.getOrDefault(false)
        is Intent -> {
            val className = value.component?.className.orEmpty()
            className in GAME_AD_ACTIVITY_CLASS_NAMES ||
                className.hasGameAdSignal() ||
                value.action.orEmpty().hasGameAdSignal() ||
                isGameAdDiagnosticValue(value.extras, depth + 1)
        }
        is Message -> isGameAdDiagnosticValue(value.obj, depth + 1) ||
            isGameAdDiagnosticValue(runCatching { value.peekData() }.getOrNull(), depth + 1)
        is Array<*> -> value.take(16).any { isGameAdDiagnosticValue(it, depth + 1) }
        is Iterable<*> -> value.take(16).any { isGameAdDiagnosticValue(it, depth + 1) }
        else -> value.javaClass.name.hasGameAdSignal() ||
            runCatching { value.toString().hasGameAdSignal() }.getOrDefault(false)
    }
}

private fun String.hasGameAdSignal(): Boolean {
    val normalized = lowercase()
    return normalized.contains("audiencenetwork") ||
        normalized.contains("instantgame") ||
        normalized.contains("quicksilver") ||
        normalized.contains("reward") ||
        normalized.contains("interstitial") ||
        normalized.contains("adinstance") ||
        normalized.contains("placementid") ||
        normalized.contains("showadasync") ||
        normalized.contains("loadadasync") ||
        normalized.contains("getrewarded") ||
        normalized.contains("getinterstitial") ||
        normalized.contains("bannerad") ||
        normalized.contains("didcomplete") ||
        normalized.contains("completiongesture") ||
        normalized.contains("com.facebook.ads") ||
        normalized.contains("neko.playables") ||
        normalized.contains("adsregistry") ||
        normalized.contains("clientmessagedispatchhelper")
}

private fun hookAudienceNetworkRewardFallbacks(classLoader: ClassLoader) {
    if (!audienceNetworkRewardHooksInstalled.compareAndSet(0, 1)) return

    listOf(
        "com.facebook.ads.RewardedVideoAd",
        "com.facebook.ads.RewardedInterstitialAd",
        "com.facebook.ads.RewardedVideoAdListener",
        "com.facebook.ads.RewardedInterstitialAdListener",
        "com.facebook.ads.RewardedVideoAd\$RewardedVideoAdLoadConfigBuilder",
        "com.facebook.ads.RewardedInterstitialAd\$RewardedInterstitialAdLoadConfigBuilder"
    ).forEach { className ->
        runCatching { tryHookAudienceNetworkRewardClass(classLoader.loadClass(className)) }
    }

    (ClassLoader::class.java.declaredMethods + ClassLoader::class.java.methods)
        .filter { method ->
            method.name == "loadClass" &&
                method.parameterTypes.isNotEmpty() &&
                method.parameterTypes[0] == String::class.java
        }
        .distinctBy { method ->
            method.name + method.parameterTypes.joinToString(prefix = "(", postfix = ")") { it.name }
        }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun afterHookedMethod(param: MethodHookParam) {
                    val clazz = param.result as? Class<*> ?: return
                    if (isAudienceNetworkRewardRelevantClass(clazz.name)) {
                        tryHookAudienceNetworkRewardClass(clazz)
                    }
                }
            })
        }

    Log.i(TAG, "Hooked Audience Network reward dynamic class fallback")
}

private fun tryHookAudienceNetworkRewardClass(clazz: Class<*>) {
    val className = clazz.name
    if (!isAudienceNetworkRewardRelevantClass(className) ||
        !audienceNetworkRewardClassesHooked.add(className)
    ) {
        return
    }

    var hooked = 0
    val methods = runCatching { clazz.declaredMethods + clazz.methods }.getOrDefault(emptyArray())
    methods.distinctBy { method ->
        method.name + method.parameterTypes.joinToString(prefix = "(", postfix = ")") { it.name }
    }.forEach { method ->
        runCatching {
            method.isAccessible = true
            if (isAudienceNetworkRewardShowMethod(clazz, method)) {
                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        val adObject = param.thisObject ?: return
                        markGameAdDiagnosticFlow("anReward.show ${method.declaringClass.name}.${method.name}")
                        logGameAdDiagnostic(
                            "anReward.show.before",
                            "${methodSignature(method)} this=${formatDiagValue(adObject)} args=${formatDiagArgs(param.args)}"
                        )
                        if (!ENABLE_GAME_AD_AUTOFIX) return

                        if (!completeAudienceNetworkRewardObject(
                                adObject,
                                "show ${method.declaringClass.name}.${method.name}"
                            )
                        ) {
                            return
                        }

                        param.result = when (method.returnType) {
                            Boolean::class.javaPrimitiveType, Boolean::class.java -> true
                            else -> null
                        }
                        Log.i(TAG, "Skipped Audience Network rewarded show via ${method.declaringClass.name}.${method.name}")
                    }

                    override fun afterHookedMethod(param: MethodHookParam) {
                        logGameAdDiagnostic(
                            "anReward.show.after",
                            "${methodSignature(method)} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                        )
                    }
                })
                hooked++
            } else if (isAudienceNetworkRewardListenerRegistrationMethod(method)) {
                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        logGameAdDiagnostic(
                            "anReward.listener.before",
                            "${methodSignature(method)} this=${formatDiagValue(param.thisObject)} args=${formatDiagArgs(param.args)}"
                        )
                        rememberAudienceNetworkRewardListeners(param.thisObject, param.args, method)
                    }

                    override fun afterHookedMethod(param: MethodHookParam) {
                        rememberAudienceNetworkRewardListeners(param.thisObject, param.args, method)
                        rememberAudienceNetworkRewardListeners(param.result, param.args, method)
                        logGameAdDiagnostic(
                            "anReward.listener.after",
                            "${methodSignature(method)} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                        )
                    }
                })
                hooked++
            } else if (isAudienceNetworkRewardLoadMethod(clazz, method)) {
                XposedBridge.hookMethod(method, object : XC_MethodHook() {
                    override fun beforeHookedMethod(param: MethodHookParam) {
                        markGameAdDiagnosticFlow("anReward.load ${method.declaringClass.name}.${method.name}")
                        logGameAdDiagnostic(
                            "anReward.load.before",
                            "${methodSignature(method)} this=${formatDiagValue(param.thisObject)} args=${formatDiagArgs(param.args)}"
                        )
                        rememberAudienceNetworkRewardListeners(param.thisObject, param.args, method)
                    }

                    override fun afterHookedMethod(param: MethodHookParam) {
                        logGameAdDiagnostic(
                            "anReward.load.after",
                            "${methodSignature(method)} result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
                        )
                    }
                })
                hooked++
            }
        }.onFailure {
            Log.w(TAG, "Failed to hook Audience Network reward method ${clazz.name}.${method.name}", it)
        }
    }

    if (hooked > 0) {
        Log.i(TAG, "Hooked $hooked Audience Network reward method(s) in $className")
    }
}

private fun isAudienceNetworkRewardRelevantClass(className: String): Boolean {
    val normalized = className.lowercase()
    return (normalized.startsWith("com.facebook.ads.") ||
        normalized.startsWith("com.facebook.audiencenetwork.") ||
        normalized.contains("audiencenetwork")) &&
        (
            normalized.contains("reward") ||
                normalized.contains("adlistener") ||
                normalized.contains("adconfig") ||
                normalized.endsWith(".ad")
            )
}

private fun isAudienceNetworkRewardShowMethod(clazz: Class<*>, method: Method): Boolean {
    val className = clazz.name.lowercase()
    return className.contains("reward") &&
        method.name == "show" &&
        !Modifier.isStatic(method.modifiers) &&
        method.parameterCount <= 1 &&
        (method.returnType == Void.TYPE ||
            method.returnType == Boolean::class.javaPrimitiveType ||
            method.returnType == Boolean::class.java)
}

private fun isAudienceNetworkRewardLoadMethod(clazz: Class<*>, method: Method): Boolean {
    return clazz.name.lowercase().contains("reward") &&
        method.name.lowercase().contains("load") &&
        !Modifier.isStatic(method.modifiers) &&
        method.parameterCount >= 1
}

private fun isAudienceNetworkRewardListenerRegistrationMethod(method: Method): Boolean {
    if (Modifier.isStatic(method.modifiers) || method.parameterCount == 0) return false
    val name = method.name.lowercase()
    if (name.contains("listener")) return true
    return method.parameterTypes.any { type ->
        val typeName = type.name.lowercase()
        typeName.contains("listener") &&
            (typeName.contains("reward") || typeName.contains("ad"))
    }
}

private fun rememberAudienceNetworkRewardListeners(owner: Any?, args: Array<Any?>?, method: Method) {
    if (owner == null || args == null) return
    args.forEach { arg ->
        if (arg != null && isAudienceNetworkRewardListenerObject(arg)) {
            audienceNetworkRewardAdListeners[owner] = arg
            Log.i(
                TAG,
                "Remembered Audience Network reward listener ${arg.javaClass.name} from ${method.declaringClass.name}.${method.name}"
            )
        } else {
            findAudienceNetworkRewardListeners(arg).firstOrNull()?.let { listener ->
                audienceNetworkRewardAdListeners[owner] = listener
                Log.i(
                    TAG,
                    "Remembered nested Audience Network reward listener ${listener.javaClass.name} from ${method.declaringClass.name}.${method.name}"
                )
            }
        }
    }
}

private fun isAudienceNetworkRewardListenerObject(value: Any?): Boolean {
    if (value == null) return false
    val type = value.javaClass
    val className = type.name.lowercase()
    if (className.contains("listener") && (className.contains("reward") || className.contains("ad"))) {
        return true
    }
    if (audienceNetworkInterfacesFor(type).any { iface ->
            val ifaceName = iface.name.lowercase()
            ifaceName.contains("listener") && (ifaceName.contains("reward") || ifaceName.contains("ad"))
        }) {
        return true
    }
    return audienceNetworkRewardMethodsFor(type).any { method ->
        method.name in AUDIENCE_NETWORK_REWARD_COMPLETION_METHOD_NAMES ||
            method.name.contains("Reward", ignoreCase = true) ||
            method.name.contains("InterstitialDismissed", ignoreCase = true)
    }
}

private fun audienceNetworkInterfacesFor(type: Class<*>): List<Class<*>> {
    val interfaces = LinkedHashSet<Class<*>>()
    fun collect(current: Class<*>?) {
        if (current == null || current == Any::class.java) return
        current.interfaces.forEach { iface ->
            if (interfaces.add(iface)) collect(iface)
        }
        collect(current.superclass)
    }
    collect(type)
    return interfaces.toList()
}

private fun completeAudienceNetworkRewardObject(adObject: Any, source: String): Boolean {
    if (!ENABLE_AUDIENCE_NETWORK_REWARD_FALLBACKS) return false

    val listeners = LinkedHashSet<Any>()
    synchronized(audienceNetworkRewardAdListeners) {
        audienceNetworkRewardAdListeners[adObject]?.let { listeners.add(it) }
    }
    listeners.addAll(findAudienceNetworkRewardListeners(adObject))

    var invoked = 0
    listeners.forEach { listener ->
        invoked += invokeAudienceNetworkRewardListenerCallbacks(listener, adObject, source)
    }

    if (invoked > 0) {
        Log.i(TAG, "Completed Audience Network reward callbacks invoked=$invoked listeners=${listeners.size} via $source")
        completeRecentGameAdRequests(source)
        return true
    }

    Log.w(TAG, "No Audience Network reward listener completed for ${adObject.javaClass.name} via $source")
    return false
}

private fun findAudienceNetworkRewardListeners(root: Any?): List<Any> {
    if (root == null) return emptyList()

    val listeners = LinkedHashSet<Any>()
    val seen = IdentityHashMap<Any, Boolean>()
    val queue = java.util.ArrayDeque<Pair<Any, Int>>()
    queue.add(root to 0)

    var inspected = 0
    while (!queue.isEmpty() && inspected < 96 && listeners.size < 8) {
        val (value, depth) = queue.removeFirst()
        if (seen.put(value, true) != null) continue
        inspected++

        if (value !== root && isAudienceNetworkRewardListenerObject(value)) {
            listeners.add(value)
            continue
        }
        if (depth >= 5 || !shouldQueueAudienceNetworkObject(value)) continue

        audienceNetworkFieldsFor(value.javaClass).forEach { field ->
            val fieldValue = runCatching { field.get(value) }.getOrNull() ?: return@forEach
            when (fieldValue) {
                is Iterable<*> -> fieldValue.take(12).forEach { item ->
                    if (item != null &&
                        (isAudienceNetworkRewardListenerObject(item) || shouldQueueAudienceNetworkObject(item))
                    ) {
                        queue.add(item to depth + 1)
                    }
                }
                is Array<*> -> fieldValue.take(12).forEach { item ->
                    if (item != null &&
                        (isAudienceNetworkRewardListenerObject(item) || shouldQueueAudienceNetworkObject(item))
                    ) {
                        queue.add(item to depth + 1)
                    }
                }
                else -> if (isAudienceNetworkRewardListenerObject(fieldValue) ||
                    shouldQueueAudienceNetworkObject(fieldValue)
                ) {
                    queue.add(fieldValue to depth + 1)
                }
            }
        }
    }

    return listeners.toList()
}

private fun invokeAudienceNetworkRewardListenerCallbacks(listener: Any, adObject: Any, source: String): Int {
    var invoked = 0
    val methodGroups = listOf(
        setOf("onAdLoaded", "onLoggingImpression", "onInterstitialDisplayed"),
        setOf(
            "onRewardedVideoCompleted",
            "onRewardedAdCompleted",
            "onRewardedInterstitialCompleted",
            "onAdComplete",
            "onAdCompleted"
        ),
        setOf("onRewardedVideoClosed", "onRewardedInterstitialClosed", "onAdClosed", "onInterstitialDismissed")
    )

    methodGroups.forEach { group ->
        audienceNetworkRewardMethodsFor(listener.javaClass)
            .filter { method -> method.name in group }
            .forEach { method ->
                val args = audienceNetworkCallbackArgs(method, adObject) ?: return@forEach
                runCatching {
                    method.invoke(listener, *args)
                    invoked++
                    Log.i(
                        TAG,
                        "Invoked Audience Network callback ${listener.javaClass.name}.${method.name} via $source"
                    )
                }.onFailure {
                    Log.w(TAG, "Failed Audience Network callback ${listener.javaClass.name}.${method.name}", it)
                }
            }
    }

    return invoked
}

private fun audienceNetworkCallbackArgs(method: Method, adObject: Any): Array<Any?>? {
    return when (method.parameterCount) {
        0 -> emptyArray()
        1 -> {
            val paramType = method.parameterTypes[0]
            if (paramType.isAssignableFrom(adObject.javaClass)) arrayOf(adObject) else null
        }
        else -> null
    }
}

private fun audienceNetworkRewardMethodsFor(type: Class<*>): List<Method> {
    val methods = LinkedHashMap<String, Method>()
    var current: Class<*>? = type
    while (current != null && current != Any::class.java && current != Activity::class.java) {
        (current.declaredMethods + current.methods).forEach { method ->
            if (!Modifier.isStatic(method.modifiers)) {
                method.isAccessible = true
                methods.putIfAbsent("${method.name}/${method.parameterTypes.joinToString { it.name }}", method)
            }
        }
        current = current.superclass
    }
    return methods.values.toList()
}

private fun inferGameAdMessageType(method: Method, payload: Any?): String? {
    val payloadType = (payload as? JSONObject)?.optString("type")?.takeIf { it.isNotBlank() }
    if (payloadType != null) return payloadType

    return when (method.name) {
        "D3s" -> "getinterstitialadasync"
        "D3x" -> "getrewardedinterstitialasync"
        "D3z" -> "getrewardedvideoasync"
        "D55" -> "hidebanneradasync"
        "D9v" -> "loadadasync"
        "D9x" -> "loadbanneradasync"
        "DX0" -> "showadasync"
        else -> null
    }
}

private fun dispatchPostResolveGameAdSignals(target: Any?, payload: Any?, messageType: String?) {
    when (messageType) {
        "loadbanneradasync", "hidebanneradasync" -> {
            val content = buildGameAdSuccessPayload(payload, messageType)
            if (dispatchGameEvent(target, "hidebannerad", content)) {
                Log.i(TAG, "Dispatched hidebannerad for game banner message type=$messageType")
            }
        }
    }
}

private fun rememberGameAdPayload(target: Any?, payload: Any?, messageType: String?) {
    if (target == null || payload !is JSONObject || messageType !in GAME_AD_MESSAGE_TYPES) return

    val now = System.currentTimeMillis()
    recentGameAdTargets[target] = now

    val snapshotPayload = runCatching { JSONObject(payload.toString()) }.getOrNull() ?: payload
    extractGameAdContent(snapshotPayload)
        ?.optString("adInstanceID")
        ?.takeIf { it.isNotBlank() }
        ?.let { adInstanceId ->
            messageType?.let { type -> gameAdInstanceTypes[adInstanceId] = type }
        }
    extractPromiseId(snapshotPayload)?.let { promiseId ->
        gameAdPromiseSnapshots.entries.removeIf { now - it.value.timestampMs > GAME_AD_PROMISE_WINDOW_MS }
        gameAdPromiseSnapshots[promiseId] = GameAdPromiseSnapshot(snapshotPayload, messageType, now)
    }
    synchronized(recentGameAdPayloads) {
        recentGameAdPayloads.removeAll { now - it.timestampMs > GAME_AD_RECENT_WINDOW_MS }
        recentGameAdPayloads.add(GameAdPayloadSnapshot(target, snapshotPayload, messageType, now))
        while (recentGameAdPayloads.size > 20) {
            recentGameAdPayloads.removeAt(0)
        }
    }
}

private fun completeRecentGameAdRequests(source: String) {
    val now = System.currentTimeMillis()
    val snapshots = synchronized(recentGameAdPayloads) {
        recentGameAdPayloads.removeAll { now - it.timestampMs > GAME_AD_RECENT_WINDOW_MS }
        recentGameAdPayloads.toList()
    }

    var resolved = 0
    snapshots.asReversed().forEach { snapshot ->
        if (shouldAutofixGameAdMessage(snapshot.messageType) &&
            resolveGameAdPayload(snapshot.target, snapshot.payload, snapshot.messageType)
        ) {
            dispatchPostResolveGameAdSignals(snapshot.target, snapshot.payload, snapshot.messageType)
            resolved++
        }
    }

    val targets = synchronized(recentGameAdTargets) {
        recentGameAdTargets.entries.removeIf { now - it.value > GAME_AD_RECENT_WINDOW_MS }
        recentGameAdTargets.keys.toList()
    }
    targets.forEach { target ->
        dispatchGameEvent(target, "hidebannerad", JSONObject().put("completed", true))
    }

    if (resolved > 0) {
        Log.i(TAG, "Re-resolved $resolved recent game ad request(s) via $source")
    }
}

private fun shouldConvertGameAdRejectToSuccess(promiseId: String, reason: String): Boolean {
    val snapshot = gameAdPromiseSnapshots[promiseId]
    if (shouldAutofixGameAdMessage(snapshot?.messageType)) return true
    if (snapshot != null && shouldForceGameAdSuccess(snapshot.payload, snapshot.messageType)) return true

    val normalized = reason.lowercase()
    if (!isRecentGameAdActivityClose()) return false
    return normalized.contains("banner")
}

private fun shouldAutofixGameAdMessage(messageType: String?): Boolean {
    return messageType in GAME_AD_AUTOFIX_MESSAGE_TYPES
}

// True when the message should be intercepted and resolved as success on the
// spot: banner lifecycle messages, rewarded requests, and reward-flavored
// load/show calls. The game then grants the reward without any ad rendering.
private fun shouldForceGameAdSuccess(payload: Any?, messageType: String?): Boolean {
    if (shouldAutofixGameAdMessage(messageType)) return true
    if (messageType !in setOf("loadadasync", "showadasync")) return false
    return hasRewardGameAdSignal(payload, messageType)
}

private fun hasRewardGameAdSignal(payload: Any?, messageType: String?): Boolean {
    if (messageType in GAME_AD_REWARD_MESSAGE_TYPES) return true

    val content = extractGameAdContent(payload)
    val adInstanceId = content?.optString("adInstanceID")?.takeIf { it.isNotBlank() }
    val knownType = adInstanceId?.let { gameAdInstanceTypes[it] }
    if (knownType in GAME_AD_REWARD_MESSAGE_TYPES) return true

    val placementText = listOf(
        content?.optString("placementID").orEmpty(),
        content?.optString("adType").orEmpty(),
        content?.optString("type").orEmpty(),
        content?.optString("format").orEmpty()
    ).joinToString(" ").lowercase()
    if (placementText.contains("reward")) return true

    return payload?.toString()?.lowercase()?.contains("rewarded") == true
}

private fun isRecentUnavailableGameAd(): Boolean {
    val rejectedAt = lastUnavailableGameAdMs.get()
    return rejectedAt > 0 && System.currentTimeMillis() - rejectedAt < GAME_AD_RECENT_WINDOW_MS
}

private fun isRecentGameAdActivityClose(): Boolean {
    val closedAt = lastGameAdActivityCloseMs.get()
    return closedAt > 0 && System.currentTimeMillis() - closedAt < 15_000L
}

private fun gameAdPromiseTypeFromReason(reason: String): String? {
    val normalized = reason.lowercase()
    return when {
        normalized.contains("reward") && normalized.contains("interstitial") -> "getrewardedinterstitialasync"
        normalized.contains("reward") -> "getrewardedvideoasync"
        normalized.contains("interstitial") -> "getinterstitialadasync"
        normalized.contains("banner") -> "loadbanneradasync"
        normalized.contains("show") || normalized.contains("watch") || normalized.contains("complete") -> "showadasync"
        normalized.contains("load") -> "loadadasync"
        else -> null
    }
}

private fun hasRecentGameAdRequest(): Boolean {
    val now = System.currentTimeMillis()
    return synchronized(recentGameAdPayloads) {
        recentGameAdPayloads.removeAll { now - it.timestampMs > GAME_AD_RECENT_WINDOW_MS }
        recentGameAdPayloads.isNotEmpty()
    }
}

private fun hookPlayableAdActivity(method: Method) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun afterHookedMethod(param: MethodHookParam) {
            val activity = param.thisObject as? Activity ?: return
            if (activity.javaClass.name != method.declaringClass.name) return
            handleGameAdActivity(activity, "direct hook ${method.declaringClass.name}.${method.name}")
        }
    })
}

private fun hookGlobalGameAdActivityLifecycleFallback() {
    if (!gameAdActivityLifecycleHookInstalled.compareAndSet(false, true)) return
    val onResume = (Activity::class.java.declaredMethods + Activity::class.java.methods).firstOrNull { method ->
        method.name == "onResume" && method.parameterCount == 0
    }?.apply { isAccessible = true } ?: return

    XposedBridge.hookMethod(onResume, object : XC_MethodHook() {
        override fun afterHookedMethod(param: MethodHookParam) {
            val activity = param.thisObject as? Activity ?: return
            val isGameAdActivity = activity.javaClass.name in GAME_AD_ACTIVITY_CLASS_NAMES
            if (!(ENABLE_GAME_AD_DIAGNOSTICS && isGameAdActivity)) {
                scheduleGameAdSurfaceSweep(activity.window?.decorView, "activity resume ${activity.javaClass.name}")
            }
            if (activity.javaClass.name !in GAME_AD_ACTIVITY_CLASS_NAMES) return
            markGameAdDiagnosticFlow("activity.onResume ${activity.javaClass.name}")
            logGameAdDiagnostic(
                "activity.onResume",
                "${activity.javaClass.name} intent=${formatDiagValue(activity.intent)}"
            )
            handleGameAdActivity(activity, "global lifecycle fallback")
        }
    })

    Log.i(TAG, "Hooked global game ad activity lifecycle fallback")
}

private fun hookGameAdActivityLaunchFallbacks() {
    val methods = LinkedHashMap<String, Method>()
    listOf(Instrumentation::class.java, Activity::class.java, ContextWrapper::class.java).forEach { type ->
        (type.declaredMethods + type.methods)
            .filter { method ->
                method.name in setOf("execStartActivity", "startActivity", "startActivityForResult", "startActivityIfNeeded") &&
                    method.parameterTypes.any { it == Intent::class.java }
            }
            .forEach { method ->
                method.isAccessible = true
                val signature = buildString {
                    append(method.declaringClass.name)
                    append('.')
                    append(method.name)
                    append('(')
                    append(method.parameterTypes.joinToString(",") { it.name })
                    append(')')
                }
                methods.putIfAbsent(signature, method)
            }
    }

    var hooked = 0
    methods.values.forEach { method ->
        runCatching {
            hookGameAdActivityLaunchMethod(method)
            hooked++
        }.onFailure {
            Log.w(TAG, "Failed to hook game ad launch fallback ${method.declaringClass.name}.${method.name}", it)
        }
    }
    Log.i(TAG, "Hooked $hooked game ad activity launch fallback method(s)")
}

private fun hookGameAdActivityLaunchMethod(method: Method) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val intent = param.args.firstOrNull { it is Intent } as? Intent ?: return
            val blockedClassName = resolveBlockedGameAdActivity(intent) ?: return
            markGameAdDiagnosticFlow("activity.launch $blockedClassName")
            logGameAdDiagnostic(
                "activity.launch.before",
                "${methodSignature(method)} target=$blockedClassName args=${formatDiagArgs(param.args)}"
            )
            if (!ENABLE_GAME_AD_AUTOFIX) return
            if (!shouldBlockGameAdActivityLaunch(blockedClassName)) return
            completeRecentGameAdRequests("launch fallback $blockedClassName")
            if (method.returnType == Boolean::class.javaPrimitiveType) {
                param.result = false
            } else {
                param.result = null
            }
            Log.i(
                TAG,
                "Blocked game ad activity launch to $blockedClassName via ${method.declaringClass.name}.${method.name}"
            )
        }

        override fun afterHookedMethod(param: MethodHookParam) {
            val intent = param.args.firstOrNull { it is Intent } as? Intent ?: return
            val blockedClassName = resolveBlockedGameAdActivity(intent) ?: return
            logGameAdDiagnostic(
                "activity.launch.after",
                "${methodSignature(method)} target=$blockedClassName result=${formatDiagValue(param.result)} throwable=${formatDiagThrowable(param.throwable)}"
            )
        }
    })
}

private fun shouldBlockGameAdActivityLaunch(className: String): Boolean {
    return className in HARD_BLOCKED_GAME_AD_ACTIVITY_CLASS_NAMES ||
        (className in setOf(AUDIENCE_NETWORK_ACTIVITY_CLASS, AUDIENCE_NETWORK_REMOTE_ACTIVITY_CLASS) &&
            isRecentUnavailableGameAd())
}

private fun resolveBlockedGameAdActivity(intent: Intent): String? {
    val explicitTarget = intent.component?.className
    if (explicitTarget != null && explicitTarget in GAME_AD_ACTIVITY_CLASS_NAMES) {
        return explicitTarget
    }
    return null
}

private fun handleGameAdActivity(activity: Activity, source: String) {
    if (!ENABLE_GAME_AD_AUTOFIX) {
        markGameAdDiagnosticFlow("activity.handle ${activity.javaClass.name}")
        logGameAdDiagnostic(
            "activity.handle.passive",
            "${activity.javaClass.name} source=$source intent=${formatDiagValue(activity.intent)}"
        )
        dumpAudienceNetworkActivityState(activity, "activity.handle.passive")
        return
    }

    when (activity.javaClass.name) {
        AUDIENCE_NETWORK_ACTIVITY_CLASS,
        AUDIENCE_NETWORK_REMOTE_ACTIVITY_CLASS -> {
            markGameAdDiagnosticFlow("activity.handle ${activity.javaClass.name}")
            logGameAdDiagnostic(
                "activity.handle.audienceNetworkCompat",
                "${activity.javaClass.name} source=$source intent=${formatDiagValue(activity.intent)}"
            )
            dumpAudienceNetworkActivityState(activity, "activity.handle.audienceNetworkCompat")
            forceAudienceNetworkRewardCompletion(activity, source)
            finishGameAdActivity(activity, source)
        }
        else -> finishGameAdActivity(activity, source)
    }
}

private fun scheduleAudienceNetworkRewardClose(activity: Activity, source: String) {
    if (activity.isFinishing) return

    val now = System.currentTimeMillis()
    val shouldSchedule = synchronized(scheduledGameAdActivityCloses) {
        val previous = scheduledGameAdActivityCloses[activity]
        if (previous != null && now - previous < AUDIENCE_NETWORK_REWARD_CLOSE_RETRY_WINDOW_MS) {
            false
        } else {
            scheduledGameAdActivityCloses[activity] = now
            true
        }
    }
    if (!shouldSchedule) return

    val root = activity.window?.decorView
    if (root == null) {
        Log.i(TAG, "Audience Network reward close skipped; missing decor via $source")
        return
    }

    Log.i(
        TAG,
        "Scheduled Audience Network reward close autoclick for ${activity.javaClass.name} via $source"
    )

    listOf(
        0L,
        120L,
        350L,
        750L,
        1_250L,
        2_000L,
        3_000L,
        AUDIENCE_NETWORK_REWARD_CLOSE_RETRY_WINDOW_MS
    ).forEach { delayMs ->
        root.postDelayed({
            if (activity.isFinishing) return@postDelayed
            val clicked = clickLikelyAudienceNetworkCloseButton(activity, "$source delay=${delayMs}ms")
            if (!clicked) {
                Log.i(TAG, "Audience Network close button not ready after ${delayMs}ms via $source")
            }
        }, delayMs)
    }
}

private fun clickLikelyAudienceNetworkCloseButton(activity: Activity, source: String): Boolean {
    val root = activity.window?.decorView ?: return false

    val candidates = collectAudienceNetworkCloseCandidates(root)
    candidates.forEach { view ->
        val clicked = runCatching { view.performClick() }.getOrDefault(false)
        if (clicked) {
            lastGameAdActivityCloseMs.set(System.currentTimeMillis())
            Log.i(TAG, "Clicked Audience Network close candidate ${view.javaClass.name} via $source")
            return true
        }
    }
    return false
}

private fun collectAudienceNetworkCloseCandidates(root: View): List<View> {
    val candidates = ArrayList<Pair<Int, View>>()

    fun visit(view: View) {
        val group = view as? ViewGroup
        if (group != null) {
            for (index in 0 until group.childCount) {
                visit(group.getChildAt(index))
            }
        }

        val score = audienceNetworkCloseCandidateScore(view, root)
        if (score > 0) {
            candidates.add(score to view)
        }
    }

    visit(root)
    return candidates
        .sortedWith(compareByDescending<Pair<Int, View>> { it.first }.thenBy { it.second.width * it.second.height })
        .map { it.second }
}

private fun audienceNetworkCloseCandidateScore(view: View, root: View): Int {
    if (!view.isShown || !view.isEnabled) return 0

    val className = view.javaClass.name.lowercase()
    val listenerName = findViewOnClickListener(view)?.javaClass?.name.orEmpty()
    val marker = buildString {
        append(className)
        append(' ')
        append(view.contentDescription?.toString()?.lowercase().orEmpty())
        append(' ')
        append((view as? TextView)?.text?.toString()?.lowercase().orEmpty())
        append(' ')
        append(listenerName.lowercase())
        append(' ')
        append(audienceNetworkParentPath(view).lowercase())
    }

    if (marker.contains("mute") ||
        marker.contains("sound") ||
        marker.contains("volume") ||
        marker.contains("keep watching") ||
        marker.contains("lose reward")
    ) {
        return 0
    }
    if (marker.contains("fullscreenadtoolbar") && marker.contains("close")) return 230
    if ((view.id == 33 || view.id == 34) && isTopRightSmallControl(view, root) && marker.contains("imageview")) return 160
    if (marker.contains("close") || marker.contains("dismiss") || marker.contains("skip") || marker.contains("done")) {
        return 120
    }
    if (!view.isClickable) return 0
    if (className.contains("close") || className.contains("dismiss")) return 70
    return 0
}

private fun isTopRightSmallControl(view: View, root: View): Boolean {
    val rootWidth = root.width.takeIf { it > 0 } ?: return false
    val rootHeight = root.height.takeIf { it > 0 } ?: return false
    val width = view.width
    val height = view.height
    if (width !in 1..260 || height !in 1..260) return false

    val location = IntArray(2)
    return runCatching {
        view.getLocationOnScreen(location)
        location[0] > rootWidth * 0.55f && location[1] < rootHeight * 0.32f
    }.getOrDefault(false)
}

private fun finishGameAdActivity(activity: Activity, source: String) {
    if (activity.isFinishing) return
    lastGameAdActivityCloseMs.set(System.currentTimeMillis())
    completeRecentGameAdRequests(source)
    if (activity.javaClass.name in GAME_AD_ACTIVITY_CLASS_NAMES) {
        activity.setResult(Activity.RESULT_OK, buildGameAdActivityResultIntent())
    } else {
        activity.setResult(Activity.RESULT_CANCELED, Intent())
    }
    activity.finish()
    Log.i(TAG, "Closed game ad activity ${activity.javaClass.name} via $source")
}

private fun buildGameAdActivityResultIntent(): Intent {
    return Intent().apply {
        putExtra("success", true)
    }
}

private fun forceAudienceNetworkRewardCompletion(activity: Activity, source: String) {
    if (!ENABLE_AUDIENCE_NETWORK_REWARD_FALLBACKS) return
    if (activity.javaClass.name !in GAME_AD_ACTIVITY_CLASS_NAMES) return

    val seen = IdentityHashMap<Any, Boolean>()
    val queue = java.util.ArrayDeque<Pair<Any, Int>>()
    queue.add(activity to 0)

    var inspected = 0
    var invoked = 0
    while (!queue.isEmpty() && inspected < 96) {
        val (value, depth) = queue.removeFirst()
        if (seen.put(value, true) != null) continue
        inspected++

        invoked += invokeAudienceNetworkRewardCompletionMethods(value)
        if (depth >= 5 || !shouldTraverseAudienceNetworkObject(value, value === activity)) continue

        audienceNetworkFieldsFor(value.javaClass).forEach { field ->
            val fieldValue = runCatching { field.get(value) }.getOrNull() ?: return@forEach
            when (fieldValue) {
                is Iterable<*> -> fieldValue.take(12).forEach { item ->
                    if (item != null && shouldQueueAudienceNetworkObject(item)) queue.add(item to depth + 1)
                }
                is Array<*> -> fieldValue.take(12).forEach { item ->
                    if (item != null && shouldQueueAudienceNetworkObject(item)) queue.add(item to depth + 1)
                }
                else -> if (shouldQueueAudienceNetworkObject(fieldValue)) {
                    queue.add(fieldValue to depth + 1)
                }
            }
        }
    }

    Log.i(TAG, "Forced Audience Network reward callbacks invoked=$invoked inspected=$inspected via $source")
}

private fun invokeAudienceNetworkRewardCompletionMethods(target: Any): Int {
    var invoked = 0
    audienceNetworkMethodsFor(target.javaClass)
        .filter { method ->
            !Modifier.isStatic(method.modifiers) &&
                method.parameterCount == 0 &&
                (
                    method.name in AUDIENCE_NETWORK_REWARD_COMPLETION_METHOD_NAMES ||
                        (method.name.contains("Reward", ignoreCase = true) &&
                            method.name.contains("Complete", ignoreCase = true))
                    )
        }
        .forEach { method ->
            runCatching {
                method.invoke(target)
                invoked++
            }.onFailure {
                Log.w(TAG, "Failed to invoke Audience Network reward callback ${target.javaClass.name}.${method.name}", it)
            }
        }
    return invoked
}

private fun audienceNetworkFieldsFor(type: Class<*>): List<Field> {
    val fields = ArrayList<Field>()
    var current: Class<*>? = type
    while (current != null &&
        current != Any::class.java &&
        current != Activity::class.java &&
        fields.size < 48
    ) {
        current.declaredFields.forEach { field ->
            if (!Modifier.isStatic(field.modifiers) && fields.size < 48) {
                field.isAccessible = true
                fields.add(field)
            }
        }
        current = current.superclass
    }
    return fields
}

private fun audienceNetworkMethodsFor(type: Class<*>): List<Method> {
    val methods = LinkedHashMap<String, Method>()
    var current: Class<*>? = type
    while (current != null &&
        current != Any::class.java &&
        current != Activity::class.java
    ) {
        current.declaredMethods.forEach { method ->
            if (!Modifier.isStatic(method.modifiers)) {
                method.isAccessible = true
                methods.putIfAbsent("${current.name}.${method.name}/${method.parameterCount}", method)
            }
        }
        current = current.superclass
    }
    return methods.values.toList()
}

private fun shouldQueueAudienceNetworkObject(value: Any): Boolean {
    val type = value.javaClass
    if (type.isPrimitive ||
        value is String ||
        value is Number ||
        value is Boolean ||
        value is CharSequence
    ) {
        return false
    }
    return shouldTraverseAudienceNetworkObject(value, false)
}

private fun shouldTraverseAudienceNetworkObject(value: Any, isRootActivity: Boolean): Boolean {
    if (isRootActivity) return true
    val className = value.javaClass.name.lowercase()
    return className.startsWith("com.facebook.ads.") ||
        className.startsWith("com.facebook.audiencenetwork.") ||
        className.contains("audiencenetwork") ||
        className.contains("reward") ||
        className.contains("interstitial") ||
        className.contains("fullscreen") ||
        className.contains("listener") ||
        className.contains(".ads.")
}

// Framework-only view-level safety net (View.addView/setText/setContentDescription/
// setVisibility, WebView, Activity.onResume). None of it needs DexKit, so it is
// installed right after Application.attach — before any feed, reels, or
// marketplace content mounts — closing the cold-start race in which the first
// sponsored tiles render before the full DexKit pass finishes seconds later.
// Both installers are idempotent, so the later DexKit-time invocation is a
// no-op.
fun installGlobalAdSurfaceFallbacksEarly() {
    runCatching { hookGlobalGameAdSurfaceFallbacks() }
        .onFailure { Log.w(TAG, "Failed early global ad surface fallbacks", it) }
    runCatching { hookGlobalGameAdActivityLifecycleFallback() }
        .onFailure { Log.w(TAG, "Failed early global ad activity lifecycle fallback", it) }
}

private fun hookGlobalGameAdSurfaceFallbacks() {
    if (!gameAdSurfaceHooksInstalled.compareAndSet(0, 1)) return

    var hooked = 0
    (ViewGroup::class.java.declaredMethods + ViewGroup::class.java.methods)
        .filter { method ->
            method.name == "addView" &&
                method.parameterTypes.any { it == View::class.java }
        }
        .distinctBy { method ->
            method.name + method.parameterTypes.joinToString(prefix = "(", postfix = ")") { it.name }
        }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun afterHookedMethod(param: MethodHookParam) {
                    val parent = param.thisObject as? ViewGroup
                    val child = param.args.firstOrNull { it is View } as? View ?: return
                    if (isPotentialNativeGameAdView(child)) {
                        hideLikelyAdContainer(child, "native ad view add ${child.javaClass.name}")
                        scheduleGameAdSurfaceSweep(child, "native ad view add ${child.javaClass.name}")
                    } else if (isPotentialExplicitFeedAdMarkerView(child)) {
                        hideLikelyAdContainer(child, "explicit feed ad view add ${child.javaClass.name}")
                        scheduleGameAdSurfaceSweep(child, "explicit feed ad view add ${child.javaClass.name}")
                    } else if (ENABLE_FEED_UI_MARKER_FALLBACKS && isPotentialFeedAdMarkerView(child)) {
                        hideLikelyAdContainer(child, "feed ad marker view add ${child.javaClass.name}")
                        scheduleGameAdSurfaceSweep(child, "feed ad marker view add ${child.javaClass.name}")
                    } else if (ENABLE_FEED_UI_MARKER_FALLBACKS && isPotentialFeedReelCtaAdMarkerView(child)) {
                        hideLikelyFeedReelCtaAdContainer(child, "feed reel CTA view add ${child.javaClass.name}")
                        scheduleGameAdSurfaceSweep(child, "feed reel CTA view add ${child.javaClass.name}")
                    } else if (shouldScheduleFeedRowSweep(parent, child)) {
                        scheduleFeedRowSweep(child, "feed row add ${child.javaClass.name}")
                    } else if (child is WebView) {
                        injectGameAdHidingScript(child)
                    }
                }
            })
            hooked++
        }

    (TextView::class.java.declaredMethods + TextView::class.java.methods)
        .filter { method ->
            method.name == "setText" &&
                method.parameterTypes.isNotEmpty() &&
                CharSequence::class.java.isAssignableFrom(method.parameterTypes[0])
        }
        .distinctBy { method ->
            method.name + method.parameterTypes.joinToString(prefix = "(", postfix = ")") { it.name }
        }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun afterHookedMethod(param: MethodHookParam) {
                    val textView = param.thisObject as? TextView ?: return
                    if (isExplicitFeedAdMarkerText(textView.text)) {
                        hideLikelyAdContainer(textView, "explicit feed ad text")
                        return
                    }
                    if (!ENABLE_FEED_UI_MARKER_FALLBACKS) return
                    if (isAnyAdMarkerText(textView.text)) {
                        hideLikelyAdContainer(textView, "ad marker text")
                    } else if (isFeedReelCtaAdMarkerText(textView.text)) {
                        hideLikelyFeedReelCtaAdContainer(textView, "feed reel CTA text")
                    }
                }
            })
            hooked++
        }

    (View::class.java.declaredMethods + View::class.java.methods)
        .filter { method ->
            method.name == "setContentDescription" &&
                method.parameterTypes.size == 1 &&
                CharSequence::class.java.isAssignableFrom(method.parameterTypes[0])
        }
        .distinctBy { method ->
            method.name + method.parameterTypes.joinToString(prefix = "(", postfix = ")") { it.name }
        }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun afterHookedMethod(param: MethodHookParam) {
                    val view = param.thisObject as? View ?: return
                    if (isExplicitFeedAdMarkerText(view.contentDescription)) {
                        hideLikelyAdContainer(view, "explicit feed ad content description")
                        return
                    }
                    // Litho ComponentHost overrides getContentDescription and can
                    // return an aggregated/different value mid-mount, so match on
                    // the value actually being set.
                    val descArg = param.args.getOrNull(0) as? CharSequence
                    if (isReelsShoppingStickerMarkerText(descArg ?: view.contentDescription)) {
                        hideReelsShoppingSticker(view, "reels shopping sticker content description")
                        return
                    }
                    if (!ENABLE_FEED_UI_MARKER_FALLBACKS) return
                    if (isFeedAdMarkerText(view.contentDescription)) {
                        hideLikelyAdContainer(view, "feed ad content description")
                    } else if (isFeedReelCtaAdMarkerText(view.contentDescription)) {
                        hideLikelyFeedReelCtaAdContainer(view, "feed reel CTA content description")
                    }
                }
            })
            hooked++
        }

    (WebView::class.java.declaredMethods + WebView::class.java.methods)
        .filter { method ->
            method.name in setOf("loadUrl", "loadData", "loadDataWithBaseURL") ||
                method.name == "onAttachedToWindow"
        }
        .distinctBy { method ->
            method.name + method.parameterTypes.joinToString(prefix = "(", postfix = ")") { it.name }
        }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun afterHookedMethod(param: MethodHookParam) {
                    val webView = param.thisObject as? WebView ?: return
                    injectGameAdHidingScript(webView)
                    scheduleGameAdSurfaceSweep(webView, "webview ${method.name}")
                }
            })
            hooked++
        }

    Log.i(TAG, "Hooked $hooked global ad surface fallback method(s)")
}

private fun scheduleGameAdSurfaceSweep(view: View?, reason: String) {
    val root = view?.rootView ?: view ?: return
    longArrayOf(0L, 250L, 1_000L, 2_500L, 5_000L).forEach { delayMs ->
        root.postDelayed({
            sweepGameAdSurface(root, reason)
        }, delayMs)
    }
}

private fun shouldScheduleFeedRowSweep(parent: ViewGroup?, child: View?): Boolean {
    if (parent == null || child !is ViewGroup) return false
    return parent.javaClass.name.contains("RecyclerView")
}

private fun scheduleFeedRowSweep(view: View?, reason: String) {
    val subtree = view ?: return
    longArrayOf(60L, 500L, 1_500L, 3_000L).forEach { delayMs ->
        subtree.postDelayed({
            sweepGameAdSurface(subtree, reason)
        }, delayMs)
    }
}

private fun sweepGameAdSurface(view: View?, reason: String): Boolean {
    if (view == null) return false

    var hidden = false
    if (view is WebView) {
        injectGameAdHidingScript(view)
    }
    if (isLikelyExplicitFeedAdCardContainer(view)) {
        hidden = hideLikelyExplicitFeedAdCardContainer(view, reason) || hidden
    }
    if (isPotentialNativeGameAdView(view) || isPotentialExplicitFeedAdMarkerView(view) || (ENABLE_FEED_UI_MARKER_FALLBACKS && (isPotentialFeedAdMarkerView(view) || (view is TextView && isAnyAdMarkerText(view.text))))) {
        hidden = hideLikelyAdContainer(view, reason) || hidden
    }
    if (ENABLE_FEED_UI_MARKER_FALLBACKS && isPotentialFeedReelCtaAdMarkerView(view)) {
        hidden = hideLikelyFeedReelCtaAdContainer(view, reason) || hidden
    }
    if (isReelsShoppingStickerMarkerText(view.contentDescription)) {
        hidden = hideReelsShoppingSticker(view, reason) || hidden
    }

    val group = view as? ViewGroup ?: return hidden
    for (index in 0 until group.childCount) {
        hidden = sweepGameAdSurface(group.getChildAt(index), reason) || hidden
    }
    return hidden
}

private fun injectGameAdHidingScript(webView: WebView) {
    webView.post {
        runCatching {
            webView.evaluateJavascript(GAME_AD_WEBVIEW_HIDE_SCRIPT, null)
        }
    }
}

private fun hideLikelyAdContainer(view: View, reason: String): Boolean {
    val root = view.rootView
    val target =
        if (shouldUseExplicitFeedMarkerCardTarget(view)) {
            if (BuildConfig.DEBUG && visibleAdTraceInstalled.get() > 0) {
                traceVisibleFacebookFeedAd(
                    view,
                    view.contentDescription?.toString() ?: reason,
                    view.context.classLoader,
                    0
                )
            }
            resolveLikelyExplicitFeedAdCardTarget(view) ?: run {
                Log.i(
                    TAG,
                    "Skipped explicit feed ad hide via $reason because no safe full-card target was found"
                )
                return false
            }
        } else if (shouldUseFeedMarkerCardTarget(view)) {
            resolveLikelyFeedMarkerCardTarget(view) ?: run {
                Log.i(
                    TAG,
                    "Skipped feed marker hide via $reason because no safe full-card target was found"
                )
                return false
            }
        } else {
            resolveLikelyAdContainerTarget(view)
        }
    return hideResolvedAdSurfaceTarget(
        target = target,
        source = view,
        root = root,
        reason = reason,
        forceCollapseHeight = false
    )
}

private fun hideLikelyExplicitFeedAdCardContainer(view: View, reason: String): Boolean {
    val target = resolveLikelyExplicitFeedAdCardTarget(view) ?: return false
    return hideResolvedAdSurfaceTarget(
        target = target,
        source = view,
        root = view.rootView,
        reason = "$reason explicit feed card",
        forceCollapseHeight = true
    )
}

private fun hideResolvedAdSurfaceTarget(
    target: View,
    source: View,
    root: View?,
    reason: String,
    forceCollapseHeight: Boolean
): Boolean {
    var hidden = false
    if (target.visibility != View.GONE) {
        target.visibility = View.GONE
        hidden = true
    }
    target.minimumHeight = 0
    target.layoutParams?.let { params ->
        if (
            forceCollapseHeight ||
            target !== source ||
            isLikelyBannerSized(target, root) ||
            isPotentialNativeGameAdView(target) ||
            isPotentialFeedAdMarkerView(source) ||
            isPotentialExplicitFeedAdMarkerView(source)
        ) {
            params.height = 0
            target.layoutParams = params
            hidden = true
        }
    }
    target.requestLayout()

    if (hidden) {
        Log.i(
            TAG,
            "Hid ad surface via $reason target=${target.javaClass.name} bounds=${target.left},${target.top},${target.right},${target.bottom}"
        )
    }
    return hidden
}

private fun traceSurvivingFeedAdSourceOnce(source: View, target: View, reason: String) {
    if (!BuildConfig.DEBUG || survivingFeedAdTraceCount.getAndIncrement() != 0) return

    val markerTexts = collectViewMarkerTexts(source)
        .plus(collectViewMarkerTexts(target))
        .distinct()
        .joinToString(" | ") { it.take(240) }
    Log.i(
        TAG,
        "SurvivingFeedAdTrace reason=$reason source=${source.javaClass.name} " +
            "target=${target.javaClass.name} markers=$markerTexts"
    )
    Throwable().stackTrace
        .asSequence()
        .filterNot { frame ->
            frame.className.startsWith("java.") ||
                frame.className.startsWith("kotlin.") ||
                frame.className.startsWith("de.robv.android.xposed.") ||
                frame.className.startsWith("org.lsposed.")
        }
        .take(48)
        .forEachIndexed { index, frame ->
            Log.i(TAG, "SurvivingFeedAdTrace stack[$index]=$frame")
        }

    val classLoader = target.javaClass.classLoader ?: source.javaClass.classLoader ?: return
    survivingFeedTypeClassNames().forEach { className ->
        logSurvivingFeedTypeContract(classLoader, className)
    }
    traceVisibleAdObjectGraph(
        target,
        "survivingCard",
        FeedItemInspector(emptyList())
    )
}

private fun hideLikelyFeedReelCtaAdContainer(view: View, reason: String): Boolean {
    val target = resolveLikelyFeedReelCtaAdContainerTarget(view) ?: return false
    var hidden = false
    if (target.visibility != View.GONE) {
        target.visibility = View.GONE
        hidden = true
    }
    target.minimumHeight = 0
    target.layoutParams?.let { params ->
        params.height = 0
        target.layoutParams = params
        hidden = true
    }
    target.requestLayout()

    if (hidden) {
        Log.i(
            TAG,
            "Hid ad surface via $reason reelCtaTarget=${target.javaClass.name} bounds=${target.left},${target.top},${target.right},${target.bottom}"
        )
    }
    return hidden
}

private fun resolveLikelyAdContainerTarget(view: View): View {
    val root = view.rootView ?: return view
    var current = view
    var selected = view
    val rootWidth = root.width.takeIf { it > 0 } ?: 0
    val rootHeight = root.height.takeIf { it > 0 } ?: 0

    while (true) {
        val parentView = current.parent as? View ?: break
        val parentClassName = parentView.javaClass.name
        if (parentClassName.contains("RecyclerView")) {
            break
        }

        val parentWidth = parentView.width
        val parentHeight = parentView.height
        val looksLikePostContainer =
            rootWidth > 0 &&
                rootHeight > 0 &&
                parentWidth >= (rootWidth * 0.82f).toInt() &&
                parentHeight > 0 &&
                parentHeight < (rootHeight * 0.72f).toInt()

        if (!looksLikePostContainer) {
            break
        }

        val currentHeight = current.height.takeIf { it > 0 } ?: parentHeight
        if (
            currentHeight > 0 &&
            parentHeight > maxOf((currentHeight * 1.25f).toInt(), currentHeight + 180)
        ) {
            break
        }

        selected = parentView
        current = parentView
    }

    return selected
}

private fun shouldUseFeedMarkerCardTarget(view: View): Boolean {
    return isPotentialFeedAdMarkerView(view) || (view is TextView && isFeedAdMarkerText(view.text))
}

private fun shouldUseExplicitFeedMarkerCardTarget(view: View): Boolean {
    return isPotentialExplicitFeedAdMarkerView(view) || (view is TextView && isExplicitFeedAdMarkerText(view.text))
}

private data class ExplicitFeedAdCardSignals(
    val hasHideAd: Boolean,
    val hasAdLabel: Boolean,
    val hasSharedLink: Boolean,
    val hasStrongCta: Boolean
)

private fun resolveLikelyExplicitFeedAdCardTarget(view: View): View? {
    val root = view.rootView ?: return null
    val rootWidth = root.width.takeIf { it > 0 } ?: return null
    val rootHeight = root.height.takeIf { it > 0 } ?: return null

    var current: View? = view
    var best: View? = null
    var bestHeight = -1

    while (current != null) {
        if (isLikelyExplicitFeedAdCardContainer(current, rootWidth, rootHeight)) {
            val candidateHeight = current.height
            if (candidateHeight > bestHeight) {
                best = current
                bestHeight = candidateHeight
            }
        }

        val parentView = current.parent as? View ?: break
        current = parentView
    }

    return best
}

private fun resolveLikelyFeedMarkerCardTarget(view: View): View? {
    val root = view.rootView ?: return null
    val rootWidth = root.width.takeIf { it > 0 } ?: return null
    val rootHeight = root.height.takeIf { it > 0 } ?: return null

    var current: View? = view
    var best: View? = null
    var bestHeight = -1

    while (current != null) {
        if (isSafeFeedMarkerCardCandidate(current, rootWidth, rootHeight)) {
            val candidateHeight = current.height
            if (candidateHeight > bestHeight) {
                best = current
                bestHeight = candidateHeight
            }
        }

        val parentView = current.parent as? View ?: break
        current = parentView
    }

    return best
}

private fun isSafeFeedMarkerCardCandidate(view: View, rootWidth: Int, rootHeight: Int): Boolean {
    val width = view.width
    val height = view.height
    if (width < (rootWidth * 0.82f).toInt()) return false
    if (height < maxOf(360, (rootHeight * 0.18f).toInt())) return false
    if (height > (rootHeight * 0.82f).toInt()) return false

    val location = IntArray(2)
    val topOnScreen = runCatching {
        view.getLocationOnScreen(location)
        location[1]
    }.getOrDefault(view.top)
    val bottomOnScreen = topOnScreen + height

    if (topOnScreen < (rootHeight * 0.04f).toInt()) return false
    if (bottomOnScreen > (rootHeight * 0.96f).toInt()) return false

    return true
}

private fun isLikelyExplicitFeedAdCardContainer(view: View): Boolean {
    val root = view.rootView ?: return false
    val rootWidth = root.width.takeIf { it > 0 } ?: return false
    val rootHeight = root.height.takeIf { it > 0 } ?: return false
    return isLikelyExplicitFeedAdCardContainer(view, rootWidth, rootHeight)
}

private fun isLikelyExplicitFeedAdCardContainer(view: View, rootWidth: Int, rootHeight: Int): Boolean {
    if (view !is ViewGroup) return false

    val width = view.width
    val height = view.height
    if (width < (rootWidth * 0.82f).toInt()) return false
    if (height < maxOf(420, (rootHeight * 0.18f).toInt())) return false
    if (height > (rootHeight * 0.96f).toInt()) return false

    val location = IntArray(2)
    val topOnScreen = runCatching {
        view.getLocationOnScreen(location)
        location[1]
    }.getOrDefault(view.top)
    val bottomOnScreen = topOnScreen + height

    if (topOnScreen < (rootHeight * 0.04f).toInt()) return false
    if (bottomOnScreen > (rootHeight * 0.98f).toInt()) return false

    val signals = collectExplicitFeedAdCardSignals(view)
    return signals.hasHideAd &&
        (signals.hasAdLabel || signals.hasSharedLink || signals.hasStrongCta)
}

private fun collectExplicitFeedAdCardSignals(root: View): ExplicitFeedAdCardSignals {
    val queue = java.util.ArrayDeque<View>()
    queue.add(root)

    var visited = 0
    var hasHideAd = false
    var hasAdLabel = false
    var hasSharedLink = false
    var hasStrongCta = false

    while (queue.isNotEmpty() && visited < 192 && !(hasHideAd && (hasAdLabel || hasSharedLink || hasStrongCta))) {
        val view = queue.removeFirst()
        visited++

        for (marker in collectViewMarkerTexts(view)) {
            val normalized = marker.lowercase()
            if (!hasHideAd && normalized.contains("hide ad")) hasHideAd = true
            if (!hasAdLabel && isExplicitFeedAdMarkerText(normalized)) hasAdLabel = true
            if (!hasSharedLink && normalized.contains("shared link:")) hasSharedLink = true
            if (!hasStrongCta && isExplicitFeedAdCtaText(normalized)) hasStrongCta = true
        }

        val group = view as? ViewGroup ?: continue
        for (index in 0 until group.childCount) {
            queue.addLast(group.getChildAt(index))
        }
    }

    return ExplicitFeedAdCardSignals(
        hasHideAd = hasHideAd,
        hasAdLabel = hasAdLabel,
        hasSharedLink = hasSharedLink,
        hasStrongCta = hasStrongCta
    )
}

private fun resolveLikelyFeedReelCtaAdContainerTarget(view: View): View? {
    val root = view.rootView ?: return null
    val rootWidth = root.width.takeIf { it > 0 } ?: return null
    val rootHeight = root.height.takeIf { it > 0 } ?: return null

    var current: View? = view
    while (current != null) {
        if (isLikelyFeedReelCtaAdContainer(current, rootWidth, rootHeight)) {
            return current
        }
        val parentView = current.parent as? View ?: break
        current = parentView
    }
    return null
}

private data class FeedReelCtaAdSignals(
    val hasSharedLink: Boolean,
    val hasSendMessageCta: Boolean,
    val hasReelSurface: Boolean,
    val hasLeadGenPrompt: Boolean
)

private fun isLikelyFeedReelCtaAdContainer(view: View, rootWidth: Int, rootHeight: Int): Boolean {
    val width = view.width
    val height = view.height
    if (width < (rootWidth * 0.82f).toInt()) return false
    if (height < (rootHeight * 0.45f).toInt() || height > (rootHeight * 0.92f).toInt()) return false

    val location = IntArray(2)
    val topOnScreen = runCatching {
        view.getLocationOnScreen(location)
        location[1]
    }.getOrDefault(view.top)
    if (topOnScreen < (rootHeight * 0.08f).toInt()) return false

    val signals = collectFeedReelCtaAdSignals(view)
    return signals.hasSharedLink &&
        signals.hasSendMessageCta &&
        (signals.hasReelSurface || signals.hasLeadGenPrompt)
}

private fun collectFeedReelCtaAdSignals(root: View): FeedReelCtaAdSignals {
    val queue = java.util.ArrayDeque<View>()
    queue.add(root)

    var visited = 0
    var hasSharedLink = false
    var hasSendMessageCta = false
    var hasReelSurface = false
    var hasLeadGenPrompt = false

    while (queue.isNotEmpty() && visited < 128 && !(hasSharedLink && hasSendMessageCta && (hasReelSurface || hasLeadGenPrompt))) {
        val view = queue.removeFirst()
        visited++

        val className = view.javaClass.name.lowercase()
        val contentDescription = view.contentDescription?.toString().orEmpty().lowercase()
        val text = (view as? TextView)?.text?.toString().orEmpty().lowercase()
        val marker = "$className $contentDescription $text"

        if (!hasSharedLink && marker.contains("shared link:")) hasSharedLink = true
        if (!hasSendMessageCta && marker.contains("send message")) hasSendMessageCta = true
        if (!hasLeadGenPrompt &&
            (
                marker.contains("your business") ||
                    marker.contains("your ad")
                )
        ) {
            hasLeadGenPrompt = true
        }
        if (!hasReelSurface &&
            (
                marker.contains("reel") ||
                    className.contains("surfaceview") ||
                    className.contains("textureview") ||
                    className.contains("videoview")
                )
        ) {
            hasReelSurface = true
        }

        val group = view as? ViewGroup ?: continue
        for (index in 0 until group.childCount) {
            queue.addLast(group.getChildAt(index))
        }
    }

    return FeedReelCtaAdSignals(
        hasSharedLink = hasSharedLink,
        hasSendMessageCta = hasSendMessageCta,
        hasReelSurface = hasReelSurface,
        hasLeadGenPrompt = hasLeadGenPrompt
    )
}

private fun isPotentialNativeGameAdView(view: View?): Boolean {
    val className = view?.javaClass?.name?.lowercase() ?: return false
    return className == "com.facebook.ads.adview" ||
        (className.endsWith(".adview") &&
            (className.startsWith("com.facebook.ads.") || className.contains("audiencenetwork"))) ||
        className.contains("adchoices")
}

private fun collectViewMarkerTexts(view: View?): List<String> {
    if (view == null) return emptyList()

    // Intentionally reads only contentDescription and text. Calling
    // createAccessibilityNodeInfo() here runs Facebook's custom view accessibility
    // code mid-mount, which blanks page-profile header text ("Sign up", "Followers",
    // "posts") after pull-to-refresh on 576, so that probe must stay out.
    val values = LinkedHashSet<String>()
    view.contentDescription?.toString()?.takeIf { it.isNotBlank() }?.let(values::add)
    (view as? TextView)?.text?.toString()?.takeIf { it.isNotBlank() }?.let(values::add)
    return values.toList()
}

private fun isPotentialFeedAdMarkerView(view: View?): Boolean {
    if (view == null) return false
    return collectViewMarkerTexts(view).any(::isFeedAdMarkerText)
}

private fun isPotentialExplicitFeedAdMarkerView(view: View?): Boolean {
    if (view == null) return false
    return collectViewMarkerTexts(view).any(::isExplicitFeedAdMarkerText)
}

private fun isPotentialFeedReelCtaAdMarkerView(view: View?): Boolean {
    if (view == null) return false
    return collectViewMarkerTexts(view).any(::isFeedReelCtaAdMarkerText)
}

private fun isAnyAdMarkerText(value: CharSequence?): Boolean {
    return isGameAdMarkerText(value) || isFeedAdMarkerText(value)
}

private fun isGameAdMarkerText(value: CharSequence?): Boolean {
    if (value.isNullOrBlank()) return false
    val normalized = value.toString().lowercase()
    return normalized.contains("ads served by meta") ||
        normalized.contains("ad choices") ||
        normalized.contains("adchoices")
}

private fun isFeedAdMarkerText(value: CharSequence?): Boolean {
    if (value.isNullOrBlank()) return false
    val normalized = value.toString().lowercase()
    return FEED_SURFACE_AD_MARKER_TOKENS.any { token -> normalized.contains(token) }
}

private fun isExplicitFeedAdMarkerText(value: CharSequence?): Boolean {
    if (value.isNullOrBlank()) return false
    val normalized = value.toString().lowercase()
    return EXPLICIT_FEED_CARD_AD_MARKER_TOKENS.any { token -> normalized.contains(token) }
}

private fun isExplicitFeedAdCtaText(value: CharSequence?): Boolean {
    if (value.isNullOrBlank()) return false
    val normalized = value.toString().lowercase()
    return EXPLICIT_FEED_AD_CTA_TOKENS.any { token -> normalized.contains(token) }
}

private fun isFeedReelCtaAdMarkerText(value: CharSequence?): Boolean {
    if (value.isNullOrBlank()) return false
    val normalized = value.toString().lowercase()
    return FEED_REEL_CTA_AD_MARKER_TOKENS.any { token -> normalized.contains(token) }
}

private fun isReelsShoppingStickerMarkerText(value: CharSequence?): Boolean {
    if (value.isNullOrBlank()) return false
    val normalized = value.toString().lowercase().trim()
    if (!normalized.contains(" - ") || !normalized.contains(", ")) return false
    return REELS_SHOPPING_STICKER_CTA_TOKENS.any { token -> normalized.endsWith(token) }
}

// Marketplace sponsored tiles are React Native content rendered from Relay
// data, so view-level hiding cannot reclaim the grid cell (Yoga ignores
// View.visibility) and a visibility guard against Yoga re-layouts causes an
// ANR. The tiles ride the organic home feed queries, so the module instead
// (1) blocks the dedicated ads fetches in the RN Networking module and
// (2) flips the server-honoured ad-skip variables in the organic feed
// requests — see installMarketplaceAdsQueryBlock.


private fun hideReelsShoppingSticker(view: View, reason: String): Boolean {
    // The sticker is a small self-contained pill (thumbnail + product title +
    // CTA) mounted as one Litho ComponentHost, so hiding the host itself —
    // instead of walking up to a full-card target — removes the whole pill
    // without touching the surrounding reel surface.
    var hidden = false
    if (view.visibility != View.GONE) {
        view.visibility = View.GONE
        hidden = true
    }
    view.minimumHeight = 0
    view.layoutParams?.let { params ->
        params.height = 0
        view.layoutParams = params
        hidden = true
    }
    view.requestLayout()
    if (hidden) {
        Log.i(
            TAG,
            "Hid reels shopping sticker via $reason view=${view.javaClass.name} " +
                "desc=${view.contentDescription?.toString()?.take(120)}"
        )
    }
    // Litho can re-bind the same mount and restore visibility after layout;
    // re-assert once the frame settles.
    view.post {
        if (view.visibility != View.GONE) {
            view.visibility = View.GONE
            view.requestLayout()
        }
    }
    return hidden
}


private fun isLikelyBannerSized(view: View, root: View?): Boolean {
    val rootHeight = root?.height?.takeIf { it > 0 } ?: return view.height in 1..360
    val height = view.height
    if (height <= 0 || height > maxOf(360, rootHeight / 3)) return false
    val location = IntArray(2)
    return runCatching {
        view.getLocationOnScreen(location)
        location[1] + height > rootHeight / 2
    }.getOrDefault(true)
}

private fun resolveGameAdPayload(target: Any?, payload: Any?, messageType: String? = null): Boolean {
    if (target == null || payload == null) return false

    val promiseId = extractPromiseId(payload)
    if (promiseId == null) {
        Log.w(TAG, "Unable to extract promiseID for resolved game ad payload")
        return false
    }

    val resolveMethod = resolveGameAdResolveMethod(target.javaClass)
    if (resolveMethod == null) {
        Log.w(TAG, "Unable to resolve success helper for resolved game ad payload")
        return false
    }

    val successPayload = buildGameAdSuccessPayload(payload, messageType)
    return runCatching {
        resolveMethod.invoke(target, promiseId, successPayload)
        true
    }.getOrElse {
        Log.e(TAG, "Failed to resolve game ad payload", it)
        false
    }
}

private fun rejectGameAdPayload(
    target: Any?,
    payload: Any?,
    message: String = GAME_AD_REJECTION_MESSAGE,
    code: String = GAME_AD_REJECTION_CODE
): Boolean {
    if (target == null || payload == null) return false

    val bridgeRejectMethod = resolveGameAdBridgeRejectMethod(target.javaClass)
    if (bridgeRejectMethod != null) {
        val success = runCatching {
            bridgeRejectMethod.invoke(target, message, code, payload)
            true
        }.getOrElse {
            Log.e(TAG, "Failed to reject game ad payload via bridge reject helper", it)
            false
        }
        if (success) {
            return true
        }
    }

    val promiseId = extractPromiseId(payload)
    if (promiseId == null) {
        Log.w(TAG, "Unable to extract promiseID for rejected game ad payload")
        return false
    }
    val rejectMethod = resolveGameAdRejectMethod(target.javaClass)
    if (rejectMethod == null) {
        Log.w(TAG, "Unable to resolve reject helper for rejected game ad payload")
        return false
    }
    return runCatching {
        rejectMethod.invoke(
            target,
            promiseId,
            message,
            code
        )
        true
    }.getOrElse {
        Log.e(TAG, "Failed to reject game ad payload", it)
        false
    }
}

private fun resolveGameAdResolveMethod(type: Class<*>?): Method? {
    if (type == null) return null

    // The Javascript bridge entry itself (X.q10.postMessage(String, String))
    // fits this shape but is NOT a promise helper — invoking it re-posts the
    // message into the native pipeline. Exclude annotated entries and the
    // postMessage name so they are never picked as a resolve method.
    val candidates = (type.declaredMethods + type.methods).filter { method ->
        !Modifier.isStatic(method.modifiers) &&
            method.returnType == Void.TYPE &&
            method.parameterCount == 2 &&
            method.parameterTypes[0] == String::class.java &&
            !method.parameterTypes[1].isPrimitive &&
            !method.isAnnotationPresent(JavascriptInterface::class.java) &&
            method.name != "postMessage"
    }

    return (candidates.firstOrNull { it.parameterTypes[1] == Any::class.java }
        ?: candidates.firstOrNull { JSONObject::class.java.isAssignableFrom(it.parameterTypes[1]) }
        ?: candidates.firstOrNull()
        )?.apply { isAccessible = true }
}

private fun resolveGameAdBridgeRejectMethod(type: Class<*>?): Method? {
    if (type == null) return null
    return (type.declaredMethods + type.methods).firstOrNull { method ->
        !Modifier.isStatic(method.modifiers) &&
            method.returnType == Void.TYPE &&
            method.parameterCount == 3 &&
            method.parameterTypes[0] == String::class.java &&
            method.parameterTypes[1] == String::class.java &&
            method.parameterTypes[2] == JSONObject::class.java
    }?.apply { isAccessible = true }
}

private fun resolveGameAdRejectMethod(type: Class<*>?): Method? {
    if (type == null) return null
    return (type.declaredMethods + type.methods).firstOrNull { method ->
        !Modifier.isStatic(method.modifiers) &&
            method.returnType == Void.TYPE &&
            method.parameterCount == 3 &&
            method.parameterTypes.all { it == String::class.java }
    }?.apply { isAccessible = true }
}

private fun dispatchGameEvent(target: Any?, eventType: String, content: Any?): Boolean {
    if (target == null) return false
    val dispatchMethod = resolveGameEventDispatchMethod(target.javaClass) ?: return false
    val eventValue = resolveGameEventValue(dispatchMethod.parameterTypes[0], eventType) ?: return false

    return runCatching {
        dispatchMethod.invoke(target, eventValue, content ?: JSONObject.NULL)
        true
    }.getOrElse {
        Log.w(TAG, "Failed to dispatch game event type=$eventType", it)
        false
    }
}

private fun resolveGameEventDispatchMethod(type: Class<*>?): Method? {
    if (type == null) return null
    return (type.declaredMethods + type.methods).firstOrNull { method ->
        !Modifier.isStatic(method.modifiers) &&
            method.returnType == Void.TYPE &&
            method.parameterCount == 2 &&
            method.parameterTypes[0] != String::class.java &&
            method.parameterTypes[1] == Any::class.java
    }?.apply { isAccessible = true }
}

private fun resolveGameEventValue(eventType: Class<*>, eventName: String): Any? {
    val valuesMethod = (eventType.declaredMethods + eventType.methods).firstOrNull { method ->
        Modifier.isStatic(method.modifiers) &&
            method.parameterCount == 0 &&
            method.returnType.isArray &&
            method.returnType.componentType == eventType
    }?.apply { isAccessible = true }

    val values = runCatching { valuesMethod?.invoke(null) as? Array<*> }.getOrNull().orEmpty()
    values.firstOrNull { value -> value?.toString() == eventName }?.let { return it }

    return eventType.declaredFields.firstOrNull { field ->
        Modifier.isStatic(field.modifiers) &&
            field.type == eventType &&
            runCatching {
                field.isAccessible = true
                field.get(null)?.toString() == eventName
            }.getOrDefault(false)
    }?.let { field -> runCatching { field.get(null) }.getOrNull() }
}

private fun extractGameAdContent(payload: Any?): JSONObject? {
    val json = payload as? JSONObject ?: return null
    return json.optJSONObject("content")
}

private fun buildGameAdPayloadFromServiceBundle(bundle: Bundle, messageType: String): JSONObject {
    return JSONObject().apply {
        put("type", messageType)
        put("content", bundleToJsonObject(bundle))
    }
}

@Suppress("DEPRECATION")
private fun bundleToJsonObject(bundle: Bundle): JSONObject {
    val json = JSONObject()
    runCatching { bundle.keySet().toList() }
        .getOrDefault(emptyList())
        .forEach { key ->
            val value = runCatching { bundle.get(key) }.getOrNull()
            putJsonCompatibleValue(json, key, value)
        }
    return json
}

private fun putJsonCompatibleValue(json: JSONObject, key: String, value: Any?) {
    when (value) {
        null -> json.put(key, JSONObject.NULL)
        is String -> json.put(key, value)
        is Boolean -> json.put(key, value)
        is Number -> json.put(key, value)
        is JSONObject -> json.put(key, value)
        is JSONArray -> json.put(key, value)
        is Bundle -> json.put(key, bundleToJsonObject(value))
        else -> json.put(key, value.toString())
    }
}

private fun buildGameAdSuccessPayload(payload: Any?, messageType: String? = null): JSONObject {
    val effectiveMessageType = messageType
        ?: (payload as? JSONObject)?.optString("type").orEmpty()
    val content = extractGameAdContent(payload)
    val result = JSONObject()

    val placementId = content?.optString("placementID")?.takeIf { it.isNotBlank() }
    val requestedAdInstanceId = content?.optString("adInstanceID")?.takeIf { it.isNotBlank() }
    val bannerPosition = content?.optString("bannerPosition")?.takeIf { it.isNotBlank() }

    result.put("success", true)
    if (hasRewardGameAdSignal(payload, effectiveMessageType)) {
        result.put("completed", true)
        result.put("didComplete", true)
        result.put("watched", true)
        result.put("rewarded", true)
        result.put("completionGesture", "post")
    }

    if (placementId != null) {
        result.put("placementID", placementId)
    }
    if (bannerPosition != null) {
        result.put("bannerPosition", bannerPosition)
    }

    val adInstanceId = when {
        requestedAdInstanceId != null -> {
            gameAdInstanceIds.putIfAbsent(requestedAdInstanceId, requestedAdInstanceId)
            requestedAdInstanceId
        }
        placementId != null && effectiveMessageType != "loadbanneradasync" ->
            resolveGameAdInstanceId(placementId, effectiveMessageType, bannerPosition)
        else -> null
    }

    if (adInstanceId != null) {
        result.put("adInstanceID", adInstanceId)
        effectiveMessageType.takeIf { it.isNotBlank() }?.let { type ->
            gameAdInstanceTypes.putIfAbsent(adInstanceId, type)
        }
    }

    return result
}

private fun forceGameAdSuccessResult(
    promiseId: String,
    original: Any?,
    payload: JSONObject?,
    messageType: String?
): JSONObject {
    val result = when (original) {
        is JSONObject -> copyJsonObject(original)
        else -> JSONObject()
    }
    val success = buildGameAdSuccessPayload(
        payload ?: JSONObject().put("content", JSONObject().put("promiseID", promiseId)),
        messageType
    )

    val keys = success.keys()
    while (keys.hasNext()) {
        val key = keys.next()
        result.put(key, success.opt(key))
    }

    result.put("success", true)
    if (hasRewardGameAdSignal(payload, messageType)) {
        result.put("completed", true)
        result.put("didComplete", true)
        result.put("watched", true)
        result.put("rewarded", true)
        result.put("completionGesture", "post")
    }
    return result
}

private fun copyJsonObject(source: JSONObject): JSONObject {
    val result = JSONObject()
    val keys = source.keys()
    while (keys.hasNext()) {
        val key = keys.next()
        result.put(key, source.opt(key))
    }
    return result
}

private fun resolveGameAdInstanceId(
    placementId: String,
    messageType: String?,
    bannerPosition: String?
): String {
    val key = listOf(messageType.orEmpty(), placementId, bannerPosition.orEmpty()).joinToString("|")
    return gameAdInstanceIds.computeIfAbsent(key) {
        val suffix = key.hashCode().toLong() and 0xffffffffL
        "${GAME_AD_SUCCESS_INSTANCE_PREFIX}_$suffix"
    }
}

private fun extractPromiseId(payload: Any?): String? {
    val jsonObjectClass = payload?.javaClass ?: return null
    if (jsonObjectClass.name != "org.json.JSONObject") return null
    val getJSONObject = (jsonObjectClass.declaredMethods + jsonObjectClass.methods).firstOrNull { method ->
        method.name == "getJSONObject" &&
            method.parameterCount == 1 &&
            method.parameterTypes[0] == String::class.java
    }?.apply { isAccessible = true } ?: return null
    val getString = (jsonObjectClass.declaredMethods + jsonObjectClass.methods).firstOrNull { method ->
        method.name == "getString" &&
            method.parameterCount == 1 &&
            method.parameterTypes[0] == String::class.java
    }?.apply { isAccessible = true } ?: return null

    val content = runCatching { getJSONObject.invoke(payload, "content") }.getOrNull() ?: return null
    return runCatching { getString.invoke(content, "promiseID") as? String }.getOrNull()
}

private fun hookSponsoredPoolAdd(method: Method): Boolean {
    if (!sponsoredPoolMethodsHooked.add(methodHookKey(method))) {
        return false
    }
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            param.result = false
            logHookHitThrottled("sponsoredPoolBlock", method)
        }
    })
    return true
}

private fun hookSponsoredStoryNext(method: Method) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            param.result = null
            Log.i(TAG, "Blocked sponsored story vending from feed manager")
        }
    })
}

private fun hookSponsoredStoryListMethods(managerClass: Class<*>) {
    var hooked = 0
    managerClass.declaredMethods
        .filter { method ->
            !Modifier.isStatic(method.modifiers) &&
                isSponsoredStoryListMethod(method)
        }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    buildEmptyListReturn(method.returnType)?.let { emptyResult ->
                        param.result = emptyResult
                    }
                }
            })
            hooked++
        }
    Log.i(TAG, "Hooked $hooked sponsored story list method(s) on ${managerClass.name}")
}

private fun isSponsoredStoryListMethod(method: Method): Boolean {
    if (method.parameterCount > 2) return false
    if (!Iterable::class.java.isAssignableFrom(method.returnType) &&
        method.returnType.name != "com.google.common.collect.ImmutableList"
    ) {
        return false
    }
    return method.parameterTypes.all { type ->
        type == Int::class.javaPrimitiveType ||
            type == Long::class.javaPrimitiveType ||
            type == Boolean::class.javaPrimitiveType
    }
}

private fun buildEmptyListReturn(returnType: Class<*>): Any? {
    if (returnType.name == "com.google.common.collect.ImmutableList") {
        return runCatching {
            val of = returnType.getDeclaredMethod("of")
            of.isAccessible = true
            of.invoke(null)
        }.getOrNull()
    }
    return when {
        returnType.isAssignableFrom(ArrayList::class.java) -> arrayListOf<Any?>()
        Iterable::class.java.isAssignableFrom(returnType) -> emptyList<Any?>()
        else -> null
    }
}

private fun hookStoryAdsMerge(method: Method, source: String) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            val originalBuckets = param.args.getOrNull(2)
            if (originalBuckets != null) {
                param.result = originalBuckets
                Log.i(TAG, "Blocked story ad bucket merge in $source")
            }
        }
    })
}

private fun hookStoryAdsNoOp(method: Method, reason: String, source: String) {
    XposedBridge.hookMethod(method, object : XC_MethodHook() {
        override fun beforeHookedMethod(param: MethodHookParam) {
            param.result = null
            Log.i(TAG, "Blocked $reason in $source")
        }
    })
}

private fun hookStoryAdProvider(provider: StoryAdProviderHooks) {
    if (!storyAdProviderClassesHooked.add(provider.providerClass.name)) return

    val hooked = ArrayList<String>()

    provider.mergeMethod?.let { method ->
        hookStoryAdsMerge(method, provider.providerClass.name)
        hooked.add("merge")
    }
    provider.fetchMoreAdsMethod?.let { method ->
        hookStoryAdsNoOp(method, "story ad fetchMoreAds", provider.providerClass.name)
        hooked.add("fetchMoreAds")
    }
    provider.deferredUpdateMethod?.let { method ->
        hookStoryAdsNoOp(method, "story ad deferred update", provider.providerClass.name)
        hooked.add("deferredUpdate")
    }
    provider.insertionTriggerMethod?.let { method ->
        hookStoryAdsNoOp(method, "story ad insertion trigger", provider.providerClass.name)
        hooked.add("insertionTrigger")
    }

    if (hooked.isNotEmpty()) {
        Log.i(TAG, "Hooked story ad provider ${provider.providerClass.name}: ${hooked.joinToString()}")
    }
}

private fun hookSponsoredPoolListMethods(poolClass: Class<*>) {
    var hooked = 0
    poolClass.declaredMethods
        .filter { method ->
            !Modifier.isStatic(method.modifiers) &&
                method.parameterCount == 0 &&
                List::class.java.isAssignableFrom(method.returnType)
        }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    param.result = arrayListOf<Any?>()
                }
            })
            hooked++
        }
    Log.i(TAG, "Hooked $hooked feed pool list method(s) on ${poolClass.name}")
}

private fun hookSponsoredPoolResultMethods(poolClass: Class<*>) {
    var hooked = 0
    poolClass.declaredMethods
        .filter { method ->
            !Modifier.isStatic(method.modifiers) &&
                isSponsoredResultCarrier(method.returnType) &&
                (
                    method.parameterCount == 0 ||
                        (method.parameterCount == 1 && method.parameterTypes[0] == Boolean::class.javaPrimitiveType)
                    )
        }
        .forEach { method ->
            method.isAccessible = true
            XposedBridge.hookMethod(method, object : XC_MethodHook() {
                override fun beforeHookedMethod(param: MethodHookParam) {
                    buildSponsoredEmptyResult(method.returnType)?.let { emptyResult ->
                        param.result = emptyResult
                    }
                }
            })
            hooked++
        }
    Log.i(TAG, "Hooked $hooked feed pool result method(s) on ${poolClass.name}")
}

private fun isSponsoredResultCarrier(type: Class<*>): Boolean {
    val constructor = type.declaredConstructors.firstOrNull { it.parameterCount == 2 } ?: return false
    val reasonType = constructor.parameterTypes.getOrNull(1) ?: return false
    return reasonType.enumConstants?.any { it.toString() == "SPONSORED_GET_NEXT_RETURN_NULL" } == true
}

private fun buildSponsoredEmptyResult(type: Class<*>): Any? {
    val constructor = type.declaredConstructors.firstOrNull { it.parameterCount == 2 } ?: return null
    val reasonType = constructor.parameterTypes.getOrNull(1) ?: return null
    val emptyReason = reasonType.enumConstants?.firstOrNull { it.toString() == "SPONSORED_GET_NEXT_RETURN_NULL" }
        ?: reasonType.enumConstants?.firstOrNull { it.toString() == "FAIL" }
        ?: return null
    constructor.isAccessible = true
    return constructor.newInstance(null, emptyReason)
}

private fun filterAdItems(list: MutableList<Any?>, inspector: AdStoryInspector): Int {
    var removed = 0
    val iterator = list.iterator()
    while (iterator.hasNext()) {
        if (inspector.containsAdStory(iterator.next())) {
            iterator.remove()
            removed++
        }
    }
    return removed
}

private fun buildImmutableListLike(
    sample: Any?,
    items: List<Any?>,
    loaderHint: ClassLoader? = null
): Any? {
    if (sample == null) return null
    // The sample's own classloader can be the bootstrap one (e.g. a
    // java.util.Collections singleton list), which cannot see the host's
    // Guava — hence the hint, plus a fallback on the first element.
    val loaders = sequenceOf(
        loaderHint,
        sample.javaClass.classLoader,
        items.firstOrNull { it != null }?.javaClass?.classLoader
    ).filterNotNull().distinct()
    for (loader in loaders) {
        val rebuilt = runCatching {
            val immutableListClass = Class.forName(
                "com.google.common.collect.ImmutableList",
                false,
                loader
            )
            val copyOf = immutableListClass.getDeclaredMethod("copyOf", Iterable::class.java)
            copyOf.invoke(null, items)
        }.getOrNull()
        if (rebuilt != null) return rebuilt
    }
    return null
}

private fun replaceFeedItemsInResult(param: XC_MethodHook.MethodHookParam, items: List<Any?>): Boolean {
    val result = param.result ?: return false
    val rebuiltResult = rebuildFeedResult(result, items) ?: return false
    param.result = rebuiltResult
    return true
}

private fun rebuildFeedResult(result: Any, items: List<Any?>): Any? {
    val type = result.javaClass
    val fields = runCatching {
        type.declaredFields.onEach { it.isAccessible = true }
    }.getOrNull() ?: return null

    val listField = fields.firstOrNull { candidate ->
        !Modifier.isStatic(candidate.modifiers) &&
            Iterable::class.java.isAssignableFrom(candidate.type)
    } ?: return null

    val intArrayField = fields.firstOrNull { candidate ->
        !Modifier.isStatic(candidate.modifiers) && candidate.type == IntArray::class.java
    } ?: return null

    val intFields = fields.filter { candidate ->
        !Modifier.isStatic(candidate.modifiers) && candidate.type == Int::class.javaPrimitiveType
    }
    if (intFields.size < 3) return null

    val originalList = runCatching { listField.get(result) }.getOrNull()
    val rebuiltList = buildImmutableListLike(originalList, items) ?: return null
    val stats = runCatching { intArrayField.get(result) as? IntArray }.getOrNull()?.clone() ?: return null
    val ints = intFields.map { field -> runCatching { field.getInt(result) }.getOrNull() ?: return null }

    val constructor = type.declaredConstructors.firstOrNull { constructor ->
        constructor.parameterCount == 5 &&
            constructor.parameterTypes.getOrNull(0)?.name == "com.google.common.collect.ImmutableList" &&
            constructor.parameterTypes.getOrNull(1) == IntArray::class.java &&
            constructor.parameterTypes.drop(2).all { it == Int::class.javaPrimitiveType }
    } ?: return null

    constructor.isAccessible = true
    return runCatching {
        constructor.newInstance(rebuiltList, stats, ints[0], ints[1], ints[2])
    }.getOrNull()
}

private fun extractFeedItemsFromResult(result: Any?): Iterable<*>? {
    if (result == null) return null
    if (result is Iterable<*>) return result

    return runCatching {
        val field = result.javaClass.declaredFields.firstOrNull { candidate ->
            Iterable::class.java.isAssignableFrom(candidate.type)
        } ?: return null
        field.isAccessible = true
        field.get(result) as? Iterable<*>
    }.getOrNull()
}

private fun logFeedItems(source: String, items: Iterable<*>, feedItemInspector: FeedItemInspector) {
    var index = 0
    for (item in items) {
        Log.i(TAG, "FeedItem $source[$index] ${feedItemInspector.describe(item)}")
        index++
    }
    Log.i(TAG, "FeedItem $source count=$index")
}
