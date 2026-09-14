# Facebook App Ads Remover

An LSPosed/Xposed module for `com.facebook.katana` that removes ads using structural DexKit discovery and guarded early-install caches.

Current static verification: Facebook `577.0.0.50.72`, module `1.10` source. The resolver does not select hooks by Facebook's obfuscated class or method names. Exact host-version keys only invalidate cached targets after an update; DexKit re-discovers the new shapes automatically.

## Scope

- News Feed sponsored units
- Story ads and in-disc story ads
- Reels / upstream ad-backed story append paths
- Quicksilver game ad requests
- Audience Network and Neko playable ad activities used by games

## Main Findings

- Obfuscated names such as `AiD`, `A84`, `A8t`, `ADF`, or `Aue` are too unstable to hardcode. They changed across builds and caused broken hooks.
- Stable strings and structural signatures are much more reliable than direct obfuscated names.
- Feed ads are inserted at multiple layers. Blocking only one layer is not enough.
- The main News Feed request is a mixed GraphQL payload containing organic and sponsored units. Blocking its host or request would also block the organic feed.
- The earliest safe client boundary found so far is the dedicated story-ad store layer identified by `AdsPaginatingNetworkAdBucketFetcher`, `FbStoryAdInDiscStoreImpl`, `IN_DISC_METADATA_KEY`, and `AD_BUCKETS_KEY`. The module blocks fetch, merge, deferred-update, and insertion methods there before ad units enter feed pools. The telemetry labels `ads_deletion`/`ads_insertion` are deliberately NOT used as class selectors anymore: unrelated story viewer classes log those labels, and hooking them blanks the story viewer (576's `X.BAl` was the story viewer's own `onDataChanged` handler).
- Game ads are not a single pipeline either. Quicksilver request hooks, postMessage hooks, and UI activity fallbacks all matter.
- Blocking `AudienceNetworkActivity` at `startActivity(...)` was too early and caused game hangs. Letting it launch and closing it immediately from activity lifecycle hooks worked better.

## Hook Strategy

### Obfuscation and version changes

- Stable strings are discovery seeds only. Every candidate is checked against its behavior: owner role, parameter/return shape, neighboring methods, implemented interfaces, and the data type it reads or writes.
- Reels insertion is accepted only for a controller method carrying a candidate item and numeric position beside a numeric boolean gate. Sponsored-pool suppression is accepted only for the three-argument pool-add shape beside a boolean item classifier. RTI suppression is limited to Kotlin `Function0.invoke` request builders.
- Shopping-card render hooks require a non-framework product model with a data-model field shape and suppress only when that payload is present on the instance. This prevents an optional empty field on a shared organic component from blanking the Reels surface.
- Cached class names are scoped to both Facebook and module versions. A Facebook update discards stale names and performs structural discovery; no per-release obfuscated-name table is required.

### Feed / Stories / Reels

- Resolve classes with DexKit using stable strings and method shapes.
- Resolve every matching story-ad provider instead of assuming one provider class; Facebook may split this pipeline between releases.
- Install feed, Reels, and game hooks independently so a changed Reels target cannot prevent feed-source filtering from loading.
- Remove ad-backed stories from the upstream list builder append path.
- Sanitize feed CSR filter inputs and outputs.
- Sanitize late-stage feed lists before they reach rendering.
- Block sponsored entries from the sponsored pool and story pool.
- Block story ad providers by intercepting merge/fetch/update style methods.
- Keep marker-based view removal as a last-resort safety net, not the primary News Feed path.

#### Facebook 577 Findings

- The installed APK analyzed on 2026-09-14 is `577.0.0.50.72` (`versionCode 474426253`). The existing Reels classification enum/interface shape remains present, as do the video-home insertion marker, sponsored-pool marker, and shoppable payload model.
- The 577 Reels product payload resolves structurally to the model shared by the shoppable component anchors. Render suppression now checks that model field at runtime; an organic component instance with a null optional payload passes through.
- The previous broad marker-only void hooks were narrowed because a changed build can reuse diagnostic strings in unrelated methods. The current source leaves those methods untouched unless their surrounding role matches the ad pipeline.

#### Historical Facebook 576 findings

- The feed component pair (576: wrapper `X.2q8`, component `X.2q4`) is discovered by Litho component name, not by obfuscated class name. Litho generated components pass a stable spec name to their base class constructor — `"NewsFeedFeedUnitComponent"` for the feed unit component and `"LoggingComponent"` for the generic wrapper Litho renders feed units through — and those strings survive Facebook's obfuscator. The class-load notifier reads the name reflectively (the generated base stores it in a final String field filled by a String constructor; the class is instantiated through its no-arg constructor to read it), and the full DexKit pass finds the same classes with an exact `usingStrings` match as a backstop.
- The cached initial News Feed (including a sponsored slot) assembles and renders within ~2s of a cold start — before any DexKit scan can finish. To win that race, the discovered guard pair is persisted in the host's `cacheDir` keyed by the Facebook version, and later launches load it right after `Application.attach`. The cached class names still fail `Class.forName` at attach time (the secondary dex is not configured yet), so every timed guard attempt re-tries registering them; the guard then installs ~200ms after attach, before the cached feed renders. This is what removes the "second feed item is a sponsored post" on force-close/reopen. A Facebook update changes the version key and falls back to the DexKit discovery, which then rewrites the cache.
- The wrapper renders via `A1F` only (no `A1H`), so the guard matches Litho layout entry points by shape — instance methods taking the Litho context (`X.3Qp`) with a non-primitive return — instead of requiring a method literally named `A1H`. Static builder factories with the same shape are excluded.
- The edge and wrapper-child fields are resolved structurally: the component's edge field is the one whose type is (or implements) the feed-item contract exposing `GraphQLFeedStoryCategory` (576: `X.3yV` via `B9B()`); the wrapper's child field is the one assignable to the component class.
- `StoryAdsInDisc` no longer exists anywhere in 576, and the story ad store moved to `X.BEC`. See the selector change above.
- The feed-item contract hooks (`X.3YX`/`X.3Xk` on 576) and the CSR/network/pool hooks all resolve structurally via DexKit (`X.21r` CSR filters, `X.21e` sponsored pool, `X.BEC` story ad store, late feed list hooks). The hardcoded 571 contract-class hints (`X.3YX`/`X.3Xk`), the Audience Network listener names (`X.mGv`/`X.mGo`), the Quicksilver handler name (`X.edO`), and the `X.2Jy` feed-object hint were removed entirely — the inspector and edge-field resolution work structurally (GraphQL edge class name, `GraphQLFeedUnitEdge`/`GraphQL`+`Feed` name matching, feed-story-category enum constants), and the AN reward no longer depends on them since the webview-delivery rewrite delivers the reward.
- The 571 hardcoded fast paths (`X.21p.Ani`, `X.1fM.A0B`, `X.21O.A03`, `X.2mm.A3F`, `X.1vr.addNewEdgeToCollection`, the `X.9xH`-style curated story-ad class list) were removed: they were all dead on 576, and the curated list even matched a network-connectivity helper (`X.9xH`) whose shape coincidentally fit the deferred-update rule. The seeded component guard seeds (`X.2q4`/`X.2q8`) were removed with the Litho-name discovery above.
- The global `addView` safety-net hook must never call `View.createAccessibilityNodeInfo()` on freshly added views. On 576, building the accessibility node mid-mount runs Facebook's custom-view accessibility code with side effects, and page-profile header text ("Sign up", "Followers", "posts") ends up blank after pull-to-refresh. `collectViewMarkerTexts` therefore reads only `contentDescription` and `text`.

### Native / Network Boundary

Facebook 571 stores most application bytecode in 18 Superpack secondary dex files. The small libraries visible directly in the APK, including `libfbunwindstack.so`, are not the feed-ad source. Networking may ultimately use native transports, but host-level blocking is too coarse because feed ads share the normal GraphQL request.

The preferred interception point is therefore after GraphQL data has been decoded but before dedicated ad providers merge it into the feed. Native or KernelSU hooks should only be considered if runtime logs show that the `ads_deletion` / `ads_insertion` provider hooks no longer resolve or fire.

### Game Ads

- Resolve Quicksilver ad request methods by their stable JSON error strings.
- Hook the Quicksilver `postMessage(String, String)` bridge as a second request-layer fallback.
- The runtime delegate the game webview actually uses (576: `X.q10`) is NOT the DexKit-discovered service delegate (`X.gJA`); it is caught at registration by hooking `WebView.addJavascriptInterface`. It is a thin delegate with no promise-resolve helper on its class, so request payloads can only be snapshotted there, not resolved.
- The promise result is delivered back into the webview as `evaluateJavascript("e = new Event('message');e.data = {...};window.dispatchEvent(e);")`. The module rewrites that JSON in place: for rewarded requests (`getrewardedvideoasync`/`getrewardedinterstitialasync`, and `showadasync` with a rewarded ad instance) error fields are dropped and `success/completed/didComplete/watched/rewarded` + `completionGesture:"post"` are forced, so the game grants the reward with no ad shown. The rewrite also covers `loadUrl` and `postWebMessage` deliveries. Note the envelope `type` stays `"rejectpromise"` on the rewritten `showadasync` responses — the game reads the outcome fields in `data`, and converting the envelope is unnecessary.
- Close `AudienceNetworkActivity`, `AudienceNetworkRemoteActivity`, and `NekoPlayableAdActivity` from lifecycle hooks as UI-level fallbacks.
- Only hard-block the playable activity launch path directly; Audience Network activity launches are allowed so their internal close/error flow can run before the activity is closed.

## Notes About Logs

- Runtime logs are debug-only.
- `Patches.kt` and `Module.java` now gate logging behind `BuildConfig.DEBUG`.
- Release builds should stay quiet unless you re-enable logging yourself.

## About `feedCsr=0`

The startup line:

```text
DexKit groups: ... feedCsr=0 ...
```

is normal in the current implementation.

That number is only the result of the initial batch string-group search. Feed CSR hooks are also resolved by later structural and fallback matchers, so `feedCsr=0` does not mean feed CSR filtering is disabled.

The line that actually matters is:

```text
Resolved feed CSR filters=...
```

If that later line contains resolved classes, the CSR filtering path is active even when the earlier batch count is zero.

## Build

- Android app module: `app`
- Host package: `com.facebook.katana`
- Application ID: `tn.loukious.facebookappadsremover`

Build the debug APK with:

```powershell
./gradlew :app:assembleDebug
```

## Current Direction

- Prefer stable strings, type signatures, and runtime structure over obfuscated identifiers.
- Keep debug instrumentation available in debug builds only.
- Treat feed, story, and game ads as separate pipelines with separate fallbacks.
