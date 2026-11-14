# Facebook App Ads Remover

An Xposed module that removes ads and unwanted content from the Facebook Android app, with media downloads, playback controls and account tools.

Current version: **1.26**.

## Requirements

- Android **8.1 or newer**.
- A compatible Xposed framework supporting the modern libxposed API **101 or newer**. Development testing uses Vector with API 102.
- The main Facebook app, **`com.facebook.katana`**. Facebook Lite and Messenger are not supported.

Development and device testing have covered Facebook **576.0.0.42.73**, **580.0.0.51.74** and **587.0.0.39.55**. Facebook 571 and earlier are unsupported. Facebook updates can change individual features; compatibility with arbitrary versions is not guaranteed.

The new account-capture integration was checked on Facebook 587. Startup capture was observed on device; account switching, token refresh and logout have regression-test coverage but have not been verified on device. This integration has not been verified against older Facebook APKs.

## Install

1. Download and install the APK from [Releases](https://github.com/Xposed-Modules-Repo/tn.loukious.facebookappadsremover/releases).
2. Enable the module in your Xposed manager and select **Facebook** as its scope.
3. Fully close Facebook and reopen it so the module loads.
4. Open **Facebook App Ads Remover** from its launcher icon or your Xposed manager's module settings button.

Feature switches stay disabled until the settings app connects to the framework. The first Facebook launch after a module or Facebook update can take longer while features are discovered.

## Features

- **Ads:** block sponsored News Feed posts, Story and Reels ads, Marketplace promotions and Instant Games ads. Extra feed protection also covers supported cached-feed paths. Supported rewarded games can still grant rewards after an ad is skipped.
- **Feed filters:** hide Threads posts, Reels, suggestions, People You May Know, Stories blocks and detected Facebook-labeled AI content. Filter posts by keywords and optionally block automatic feed refreshes.
- **Stories:** watch without marking stories as seen, or hide the Stories tray.
- **Appearance:** force dark mode and use true-black AMOLED backgrounds. AMOLED mode requires Facebook's dark theme or Force dark mode.
- **Privacy:** allow screenshots and recording, and block Facebook's capture detection.
- **Navigation:** hide Reels, Marketplace or Gaming tabs while keeping their destinations accessible elsewhere.
- **Links:** use an external browser and optionally remove Facebook redirect tracking. Facebook pages and login flows stay in the app.
- **Media:** download the active Reel or Story, choose media quality, use a browser or the built-in downloader, and optionally trigger downloads from copied links. Repost active Reels and Stories through the Facebook Page posting flow.
- **Video:** resume playback position and optionally keep the current video playing in the background.
- **Account:** export and restore Facebook login-session files.
- **Module:** show or hide the launcher icon without disabling the module.

Ad blocking, external browsing, browser downloads and contextual download buttons default **ON**. Other optional switches default **OFF**.

Ad-family settings are independent, but methods shared by Stories and Reels may require both ad switches to be enabled. Feed-filter coverage depends on the hooks available in your Facebook version; hiding many suggestions can slow feed loading.

## Settings and Apply changes

The settings app has a home/status screen, separate feature pages, Diagnostics and About. It follows your system light/dark theme and uses wallpaper colors on Android 12 or newer.

After changing a feature setting or successfully importing a session, return home and tap **Apply changes**. The module waits for participating Facebook processes to exit before reopening Facebook. Pending changes survive closing or recreating the settings app; edits made during a restart remain pending.

If a restart cannot be confirmed, changes remain pending. Open Facebook and retry, or force-stop Facebook manually before reopening it.

## Account backups

**Export** saves Facebook's live authentication/login-session files to `Download/FacebookAppAdsRemover` as `FBAR-Session-*.json`. Separately captured tokens and cookies are not added to the export.

**Import latest** restores the newest backup. **Import from file** lets you select a backup, including one copied from another device. After a successful import, return home and tap **Apply changes**.

Backups contain login credentials and can give access to your account. Keep them private and do not attach them to issue reports.

## Diagnostics

Open Facebook before using **Save report** or **Share report**. Reports contain sanitized configuration and hook-discovery diagnostics, excluding raw activity and media payloads. Pending requests and private cached reports survive settings recreation, including while the system save picker is open.

When reporting a problem, include your Facebook version, framework version, the affected feature and a diagnostics report.

## Hide the launcher icon

The **Module** page can hide the launcher icon. You can still reopen settings from the Xposed manager's module list. Hiding the icon does not disable Facebook's hooks.

On Pixel Launcher, searching for the module can still show an App Info entry even when its drawer icon is hidden.

## Support and source

- [Report a problem or request a feature](https://github.com/Loukious/FacebookAppAdsRemover/issues)
- [Source code and technical documentation](https://github.com/Loukious/FacebookAppAdsRemover)
- [Support development](https://buymeacoffee.com/loukious)

This repository hosts the module listing and release APKs. Development source is maintained in the linked source repository.
