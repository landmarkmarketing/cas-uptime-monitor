#!/usr/bin/env python3
"""
CreditAssociates - website uptime monitor (runs every 15 minutes)
==================================================================
The site counts as "UP" only when ALL of these pass on the homepage, on BOTH desktop and mobile:
  1. The CreditAssociates logo loads and is visible at the top of the page
     (top-left on desktop; top of the screen on mobile)
  2. The "How it Works" headline is visible in the page content (a "How it Works" menu link doesn't count)
  3. "CreditAssociates" appears in the footer (as text, or as the logo image in the footer)

Alerting (Microsoft Teams): DOWN alert after a confirmed failure, a STILL DOWN reminder every
60 minutes, and a BACK UP message when it recovers. Status is remembered in state/cas-status.json.

Usage:
  python monitor_cas.py                       # normal check
  python monitor_cas.py --test-alert down     # send a sample DOWN alert to Teams
  python monitor_cas.py --test-alert recovery # send a sample BACK UP message to Teams
"""
from __future__ import annotations

import datetime as dt
import json
import os
import re
import socket
import ssl
import sys
import time
from pathlib import Path
from urllib.parse import urlparse
from zoneinfo import ZoneInfo

import requests

# ------------------------------------------------------------------ settings
SITE = os.getenv("MONITOR_SITE", "https://www.creditassociates.com").rstrip("/")
SITE_NAME = "creditassociates.com"
TARGETS = {
    "home": {"label": "Homepage", "url": f"{SITE}/"},
}
VIEWS = ("desktop", "mobile")
WEBHOOK = os.getenv("TEAMS_WEBHOOK_URL", "").strip()
RETRY_DELAY = int(os.getenv("RETRY_DELAY_SECONDS", "60"))
REMINDER_MINUTES = int(os.getenv("REMINDER_MINUTES", "60"))
STATE_FILE = Path(os.getenv("STATE_FILE", "state/cas-status.json"))
SHOT_DIR = Path(os.getenv("SCREENSHOT_DIR", "screenshots-cas"))
RUN_URL = (
    f"{os.getenv('GITHUB_SERVER_URL')}/{os.getenv('GITHUB_REPOSITORY')}/actions/runs/{os.getenv('GITHUB_RUN_ID')}"
    if os.getenv("GITHUB_RUN_ID") else ""
)
MONITOR_TAG = "CAS-UptimeMonitor/1.0"  # firewall teams can allowlist this
DESKTOP_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
              f"Chrome/130.0.0.0 Safari/537.36 {MONITOR_TAG}")
CT = ZoneInfo("America/Chicago")

# What we look for. Patterns ignore capitalization and spacing differences.
BRAND = r"credit[\s\-_]*associates"
# Logo: an image or drawn logo near the top whose file name / description / link mentions the brand or "logo"
LOGO_HINT = r"credit[\s\-_]*associates|logo"
# The headline must read just "How it Works" (a sentence that merely contains those words doesn't count)
HEADING_PATTERN = r"^\s*how\s+it\s+works\s*[.!?:]?\s*$"
HEADING_HINT = r"how\s+it\s+works"
HEADING_LABEL = "How it Works"
CHECK_LABELS = {"logo": "Logo", "heading": "How it Works", "footer": "Footer"}
TARGET_CHECKS = {"home": ("logo", "heading", "footer")}

ERROR_SIGNATURES = {
    "error establishing a database connection":
        "WordPress can't reach its database (the database server is down or overloaded, or the DB credentials changed).",
    "there has been a critical error on this website":
        "WordPress PHP fatal error, usually caused by a plugin, theme, or PHP-version update.",
    "briefly unavailable for scheduled maintenance":
        "WordPress is stuck in maintenance mode after an update. Deleting the .maintenance file in the site root fixes it.",
    "just a moment...": "A Cloudflare/bot-protection challenge page was served instead of the site.",
    "attention required! | cloudflare": "A Cloudflare firewall block page was served.",
    "your access to this site has been limited": "The Wordfence security plugin blocked the request.",
}
BLOCK_WORDS = ("cloudflare", "wordfence", "challenge")
HTTP_MEANINGS = {
    500: "Internal Server Error: the site's code crashed",
    502: "Bad Gateway: the CDN/proxy can't reach the web server behind it",
    503: "Service Unavailable: the server is overloaded or in maintenance mode",
    504: "Gateway Timeout: the web server took too long to answer the CDN/proxy",
    520: "Cloudflare 520: the web server returned an empty/invalid response",
    521: "Cloudflare 521: the web server is down or refusing Cloudflare",
    522: "Cloudflare 522: connection to the web server timed out",
    523: "Cloudflare 523: the web server's address is unreachable",
    524: "Cloudflare 524: the web server took too long to respond",
    525: "Cloudflare 525: SSL handshake with the web server failed",
    526: "Cloudflare 526: the web server's SSL certificate is invalid",
}

# ------------------------------------------------------------------ browser-side JS
VIS_JS = """const vis = el => { const r = el.getBoundingClientRect(); return r.width > 0 && r.height > 0 &&
  (el.checkVisibility ? el.checkVisibility({opacityProperty: true, visibilityProperty: true}) : true); };"""

LOGO_JS = "([hint, mobile]) => {" + VIS_JS + r"""
  window.scrollTo(0, 0);
  const vw = window.innerWidth, re = new RegExp(hint, 'i');
  const cls = el => !el ? '' : typeof el.className === 'string' ? el.className : (el.className && el.className.baseVal) || '';
  const attrs = el => el ? [el.getAttribute('src'), el.currentSrc, el.getAttribute('alt'), el.getAttribute('aria-label'),
                            el.getAttribute('title'), el.id, cls(el)].join(' ') : '';
  const ancestors = (el, n) => { const out = []; let p = el.parentElement;
    while (p && out.length < n && p !== document.body) { out.push(p); p = p.parentElement; } return out; };
  const ctx = el => ancestors(el, 4).map(a => cls(a) + ' ' + (a.id || '') + ' ' + (a.getAttribute('aria-label') || '')).join(' ');
  // Logos almost always link to the homepage. Other links aren't evidence: every link contains the site's address.
  const isHomeLink = a => { if (!a) return false;
    try { const u = new URL(a.getAttribute('href') || '', location.href); return (u.pathname === '/' || u.pathname === '') && !u.hash; }
    catch (e) { return false; } };
  // Small interface icons (menu arrows/carets, hamburger, search, close): judged by the graphic's OWN name only,
  // because website builders often put a real logo inside a box named "icon".
  const iconLike = el => /(^|[\s_-])(caret|arrow|chevron|fa[srb]?|e-font-icon-svg|hamburger|toggle|close|search)([\s_-]|$)/i.test(cls(el));
  // Award banners, badges and review stars are never the logo
  const bannerWords = /banner|award|badge|top[\s_-]?work|t100|trustpilot|rating|bbb|stars?\b|review/i;
  const inMenuItem = el => !!el.closest('li, [role=menuitem], .menu-item, .e-n-menu-item, .sub-menu, .dropdown');
  const maxShare = mobile ? 0.65 : 0.45;

  const info = [...document.querySelectorAll('img, svg')]
    .filter(el => el.tagName.toLowerCase() !== 'svg' || !el.parentElement.closest('svg'))
    .filter(el => !iconLike(el))
    .map(el => {
      const a = el.closest('a'), r = el.getBoundingClientRect(), x = r.left + scrollX, y = r.top + scrollY;
      const own = attrs(el), around = attrs(el.parentElement) + ' ' + attrs(a) + ' ' + ctx(el);
      const ownMatch = re.test(own), ctxMatch = re.test(around), home = isHomeLink(a);
      const isBanner = bannerWords.test(own + ' ' + attrs(a)) || r.width > vw * maxShare;
      const isImg = el.tagName.toLowerCase() === 'img';
      const src = isImg ? (el.currentSrc || el.src || '') : '';
      const loaded = !isImg || (el.complete && (el.naturalWidth > 0 || (/\.svg(\?|$)/i.test(src) && r.width > 0)));
      const score = (/logo/i.test(own + ' ' + around) ? 4 : 0) + (home ? 2 : 0) + (ownMatch ? 2 : 0) + (ctxMatch ? 1 : 0);
      return { el, keep: !isBanner && (ownMatch || ((ctxMatch || home) && !inMenuItem(el))), score, isImg, src, loaded, x, y, r, a };
    });
  const describe = c => ({
    kind: c.isImg ? 'image' : 'drawn (svg)', url: c.src,
    file: (c.isImg ? c.src.split('/').pop() : (c.el.getAttribute('aria-label') || cls(c.el) || cls(c.el.parentElement) ||
           (c.a && (c.a.getAttribute('aria-label') || cls(c.a))) || 'logo')).slice(0, 70),
    isHeaderLogoFile: true, loaded: c.loaded, visible: vis(c.el), x: Math.round(c.x), y: Math.round(c.y), w: Math.round(c.r.width),
    stuckAnimation: !!c.el.closest('.elementor-invisible, .et_animated:not(.et-animated)'),
    waitingToFadeIn: !vis(c.el) && c.r.width > 0 && c.r.height > 0 && !!c.el.closest('.elementor-invisible, .et_animated:not(.et-animated)')
                     && getComputedStyle(c.el).display !== 'none',
    inPlace: c.y < 250 && (mobile || c.x < vw * 0.4) });
  const kept = info.filter(c => c.keep).map(c => Object.assign(describe(c), { score: c.score }));
  const good = kept.filter(c => c.loaded && (c.visible || c.waitingToFadeIn) && c.inPlace && c.w >= 40)
                   .sort((p, q) => (q.visible - p.visible) || q.score - p.score || p.y - q.y);
  const rest = kept.filter(c => !good.includes(c)).sort((p, q) => (q.visible - p.visible) || (p.y - q.y));
  // For troubleshooting: every visible graphic near the top of the page, whether or not it counted
  const topGraphics = good.length ? [] : info.filter(c => c.y < 300 && (c.r.width >= 20 || !vis(c.el)))
    .sort((p, q) => (q.keep - p.keep) || q.score - p.score || (q.r.width - p.r.width)).slice(0, 10)
    .map(c => `${c.isImg ? 'image ' + c.src.split('/').pop() : 'drawn'} | ${cls(c.el).slice(0, 40)} | box: ${cls(c.el.parentElement).slice(0, 50)} | link: ${c.a ? (c.a.getAttribute('href') || '').slice(0, 60) : 'none'} | ${Math.round(c.r.width)}px at x=${Math.round(c.x)}, y=${Math.round(c.y)}${vis(c.el) ? '' : ' (hidden)'}${c.keep ? '' : ' (skipped)'}`);
  return { ok: good.length > 0, candidates: [...good, ...rest].slice(0, 8), topGraphics };
}"""

CHROME_SELECTOR = ("header, nav, [role=navigation], [role=banner], [data-elementor-type=header], "
                   ".menu, .main-navigation, #site-navigation")
TEXT_JS = "([pattern, hint, chromeSel]) => {" + VIS_JS + r"""
  // Hidden code (like a script that writes the year) is invisible to visitors, so ignore it too.
  document.querySelectorAll('script, noscript, template').forEach(s => s.remove());
  const norm = s => (s || '').replace(/\s+/g, ' ');
  const inMenu = el => !!(chromeSel && el.closest(chromeSel));
  const leavesFor = rx => {
    const hits = [...document.body.querySelectorAll('*')].filter(el => el.tagName !== 'STYLE' && rx.test(norm(el.textContent)));
    return hits.filter(el => ![...el.children].some(c => rx.test(norm(c.textContent))));
  };
  const out = leavesFor(new RegExp(pattern, 'i')).filter(el => !inMenu(el)).map(el => ({
    tag: el.tagName.toLowerCase(), visible: vis(el),
    stuckAnimation: !!el.closest('.elementor-invisible, .et_animated:not(.et-animated)'),
    text: norm(el.textContent).trim().slice(0, 140),
  }));
  const ok = out.some(o => o.visible);
  const saw = (!ok && hint) ? leavesFor(new RegExp(hint, 'i'))
      .map(el => ({ text: norm(el.textContent).trim().slice(0, 140), visible: vis(el), inMenu: inMenu(el) })).slice(0, 3) : [];
  return { inDom: out.length > 0, ok, matches: out.slice(0, 6), saw };
}"""

FOOTER_SELECTOR = ("footer, [role=contentinfo], [data-elementor-type=footer], .site-footer, #footer, #colophon, "
                   "[class*=footer], [id*=footer]")
FOOTER_JS = "([pattern, footerSel]) => {" + VIS_JS + r"""
  document.querySelectorAll('script, noscript, template').forEach(s => s.remove());
  const re = new RegExp(pattern, 'i'), norm = s => (s || '').replace(/\s+/g, ' ');
  const pageH = document.documentElement.scrollHeight;
  const inFooter = el => !!el.closest(footerSel) || (el.getBoundingClientRect().top + scrollY) > pageH * 0.75;
  const hits = [...document.body.querySelectorAll('*')].filter(el => el.tagName !== 'STYLE' && re.test(norm(el.textContent)));
  const texts = hits.filter(el => ![...el.children].some(c => re.test(norm(c.textContent))))
    .map(el => ({ kind: 'text', inFooter: inFooter(el), visible: vis(el), text: norm(el.textContent).trim().slice(0, 140) }));
  const imgs = [...document.querySelectorAll('img')].filter(i => re.test((i.alt || '') + ' ' + (i.getAttribute('src') || '')))
    .map(i => ({ kind: 'image', inFooter: inFooter(i), visible: vis(i) && i.complete && i.naturalWidth > 0,
                 text: 'logo image: ' + (i.alt || (i.getAttribute('src') || '').split('/').pop()).slice(0, 80) }));
  const all = [...texts, ...imgs], mine = all.filter(i => i.inFooter);
  return { inDom: mine.length > 0, ok: mine.some(i => i.visible), matches: mine.slice(0, 6),
           saw: all.filter(i => !i.inFooter).slice(0, 3), footerExists: !!document.querySelector(footerSel) };
}"""

# ------------------------------------------------------------------ network checks
def base_network(site: str) -> dict:
    """DNS and SSL certificate. Shared by every page on the site."""
    d: dict = {}
    host = urlparse(site).hostname or ""
    try:
        d["dns"] = {"ok": True, "ips": sorted({a[4][0] for a in socket.getaddrinfo(host, 443, proto=socket.IPPROTO_TCP)})}
    except socket.gaierror as e:
        d["dns"] = {"ok": False, "error": str(e)}
        return d
    if urlparse(site).scheme != "https":
        return d  # no SSL to check
    try:
        ctx = ssl.create_default_context()
        with socket.create_connection((host, 443), timeout=15) as sock, ctx.wrap_socket(sock, server_hostname=host) as tls:
            cert = tls.getpeercert()
        expires = dt.datetime.strptime(cert["notAfter"], "%b %d %H:%M:%S %Y %Z").replace(tzinfo=dt.timezone.utc)
        d["tls"] = {"ok": True, "expires": expires.date().isoformat(),
                    "days_left": (expires - dt.datetime.now(dt.timezone.utc)).days}
    except ssl.SSLCertVerificationError as e:
        d["tls"] = {"ok": False, "kind": "cert", "error": getattr(e, "verify_message", "") or str(e)}
    except (socket.timeout, TimeoutError):
        d["tls"] = {"ok": False, "kind": "timeout", "error": "No answer on port 443 within 15s"}
    except ConnectionRefusedError:
        d["tls"] = {"ok": False, "kind": "refused", "error": "Connection refused on port 443"}
    except Exception as e:  # noqa: BLE001
        d["tls"] = {"ok": False, "kind": "other", "error": f"{type(e).__name__}: {e}"[:200]}
    return d


def http_check(url: str) -> dict:
    """Raw server response for one page: status code, response time, error-page fingerprints."""
    try:
        r = requests.get(url, timeout=(15, 45), headers={"User-Agent": DESKTOP_UA}, allow_redirects=True)
        body = r.text.lower()[:500_000]
        return {"ok": r.status_code < 400, "status": r.status_code,
                "ttfb_ms": int(r.elapsed.total_seconds() * 1000), "final_url": r.url,
                "redirects": [h.status_code for h in r.history], "server": r.headers.get("server", ""),
                "cache": r.headers.get("cf-cache-status") or r.headers.get("x-cache") or "",
                "signatures": [m for s, m in ERROR_SIGNATURES.items() if s in body]}
    except requests.exceptions.Timeout:
        return {"ok": False, "error": "timeout", "detail": "Connected, but no response within 45s"}
    except requests.exceptions.SSLError as e:
        return {"ok": False, "error": "ssl", "detail": str(e)[:200]}
    except requests.exceptions.ConnectionError as e:
        return {"ok": False, "error": "connection", "detail": str(e)[:200]}
    except Exception as e:  # noqa: BLE001
        return {"ok": False, "error": "other", "detail": f"{type(e).__name__}: {e}"[:200]}


# ------------------------------------------------------------------ browser checks
def _context_args(pw, view: str) -> dict:
    if view == "desktop":
        return {"viewport": {"width": 1440, "height": 900}, "user_agent": DESKTOP_UA}
    dev = dict(pw.devices.get("Pixel 7") or {
        "viewport": {"width": 412, "height": 839}, "device_scale_factor": 2.625, "is_mobile": True, "has_touch": True,
        "user_agent": "Mozilla/5.0 (Linux; Android 14; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) "
                      "Chrome/130.0.0.0 Mobile Safari/537.36"})
    dev.pop("default_browser_type", None)
    dev["user_agent"] = f"{dev['user_agent']} {MONITOR_TAG}"
    return dev


def _scroll_through(page) -> None:
    """Scroll like a visitor so lazy-loaded content and scroll-triggered animations appear."""
    height = page.evaluate("document.body ? document.body.scrollHeight : 0") or 0
    step = page.viewport_size["height"] if page.viewport_size else 700
    for y in range(0, height + step, step):
        page.evaluate(f"window.scrollTo(0, {y})")
        page.wait_for_timeout(120)
    page.wait_for_timeout(1200)


def _act_like_a_visitor(page) -> None:
    """Many WordPress speed plugins hold back parts of the page (often the header) until the visitor moves the
    mouse, scrolls the wheel, or touches the screen. Real visitors always do, so the monitor does too."""
    try:
        page.mouse.move(200, 300)
        page.mouse.move(420, 360, steps=5)
        page.mouse.wheel(0, 300)
        page.evaluate("""() => {
          for (const ev of ['mousemove', 'mousedown', 'keydown', 'touchstart', 'touchmove', 'wheel', 'scroll'])
            window.dispatchEvent(new Event(ev, {bubbles: true}));
          document.dispatchEvent(new Event('mousemove', {bubbles: true}));
        }""")
        page.wait_for_timeout(2500)
        page.evaluate("window.scrollTo(0, 0)")
        page.wait_for_timeout(800)
    except Exception:  # noqa: BLE001
        pass


def check_page(pw, browser, target: str, view: str) -> dict:
    from playwright.sync_api import TimeoutError as PWTimeout

    url = TARGETS[target]["url"]
    res = {"loaded": False, "status": None, "load_ms": None, "load_error": None, "notes": [],
           "checks": {}, "console_errors": [], "failed_requests": [], "screenshot": None}
    ctx = browser.new_context(**_context_args(pw, view))
    page = ctx.new_page()
    page.on("console", lambda m: m.type == "error" and res["console_errors"].append(m.text[:200]))
    page.on("requestfailed", lambda r: res["failed_requests"].append(f"{r.failure or 'failed'}: {r.url[:150]}"))
    page.on("response", lambda r: r.status >= 400 and res["failed_requests"].append(f"HTTP {r.status}: {r.url[:150]}"))

    try:
        t0 = time.monotonic()
        try:
            resp = page.goto(url, wait_until="domcontentloaded", timeout=45_000)
            res["status"] = resp.status if resp else None
        except Exception as e:  # noqa: BLE001
            res["load_error"] = str(e).splitlines()[0][:300]
            return res
        try:
            page.wait_for_load_state("load", timeout=30_000)
        except PWTimeout:
            res["notes"].append("The browser 'load' event didn't fire within 30s, so some files are hanging.")
        try:
            page.wait_for_load_state("networkidle", timeout=8_000)
        except PWTimeout:
            pass  # chat widgets and trackers often keep the network busy; not a failure
        res["load_ms"] = int((time.monotonic() - t0) * 1000)
        res["loaded"] = True
        _act_like_a_visitor(page)

        if target == "home":
            deadline = time.monotonic() + 10
            while True:
                logo = page.evaluate(LOGO_JS, [LOGO_HINT, view == "mobile"])
                if logo["ok"] or time.monotonic() > deadline:
                    break
                page.wait_for_timeout(1000)
            res["checks"]["logo"] = {"ok": logo["ok"], "candidates": logo["candidates"], "topGraphics": logo["topGraphics"]}
            _scroll_through(page)
            try:  # bring the heading into view in case it has an entrance animation
                page.get_by_text(re.compile(HEADING_HINT, re.I)).last.scroll_into_view_if_needed(timeout=3000)
                page.wait_for_timeout(1200)
            except Exception:  # noqa: BLE001
                pass
            res["checks"]["heading"] = page.evaluate(TEXT_JS, [HEADING_PATTERN, HEADING_HINT, CHROME_SELECTOR])
            page.evaluate("window.scrollTo(0, document.body.scrollHeight)")
            page.wait_for_timeout(1500)
            res["checks"]["footer"] = page.evaluate(FOOTER_JS, [BRAND, FOOTER_SELECTOR])

    finally:
        if not (res["loaded"] and all(c.get("ok") for c in res["checks"].values())):
            try:
                SHOT_DIR.mkdir(parents=True, exist_ok=True)
                path = SHOT_DIR / f"{target}-{view}.png"
                page.evaluate("window.scrollTo(0, 0)")
                page.screenshot(path=str(path), full_page=True, timeout=20_000)
                res["screenshot"] = str(path)
            except Exception:  # noqa: BLE001
                pass
        ctx.close()
    return res


def view_ok(br: dict) -> bool:
    return bool(br.get("loaded")) and bool(br.get("checks")) and all(c.get("ok") for c in br["checks"].values())


def run_all() -> tuple[bool, dict, dict]:
    base = base_network(SITE)
    results: dict = {t: {"http": http_check(TARGETS[t]["url"])} for t in TARGETS}
    if not base.get("dns", {}).get("ok"):
        for t in TARGETS:
            for v in VIEWS:
                results[t][v] = {"loaded": False, "skipped": True, "checks": {}}
        return False, base, results
    try:
        from playwright.sync_api import sync_playwright
        with sync_playwright() as pw:
            browser = pw.chromium.launch()
            try:
                for t in TARGETS:
                    for v in VIEWS:
                        try:
                            results[t][v] = check_page(pw, browser, t, v)
                        except Exception as e:  # noqa: BLE001
                            results[t][v] = {"loaded": False, "checks": {},
                                             "load_error": f"Browser error: {type(e).__name__}: {e}"[:300]}
            finally:
                browser.close()
    except Exception as e:  # noqa: BLE001  (browser failed to start: a monitor problem, never a silent pass)
        for t in TARGETS:
            for v in VIEWS:
                results[t].setdefault(v, {"loaded": False, "checks": {},
                                          "load_error": f"Monitor could not start its browser: {e}"[:300]})
    up = all(view_ok(results[t][v]) for t in TARGETS for v in VIEWS)
    return up, base, results


# ------------------------------------------------------------------ diagnosis
class Diagnosis:
    def __init__(self):
        self.headline: str | None = None
        self._reasons: dict[tuple[str, str], list[str]] = {}  # (scope, text) -> views
        self._steps: list[str] = []
        self.false_alarm_possible = False

    def head(self, text):
        self.headline = self.headline or text

    def reason(self, scope, text, view=None):
        views = self._reasons.setdefault((scope, text), [])
        if view and view not in views:
            views.append(view)

    def step(self, text, first=False):
        if text in self._steps:
            return
        self._steps.insert(0, text) if first else self._steps.append(text)

    @property
    def reasons(self):
        out = []
        for (scope, text), views in self._reasons.items():
            tag = f"{scope} · {' & '.join(views)}" if views else scope
            out.append(f"[{tag}] {text}")
        return out

    @property
    def steps(self):
        return self._steps


def _diag_http(d: Diagnosis, http: dict, label: str) -> None:
    if http.get("error"):
        if http["error"] == "timeout":
            d.head("The server accepted the connection but didn't respond within 45 seconds. It's likely overloaded or hung.")
            d.step("Check the hosting dashboard for CPU/memory spikes or unusual traffic (bot attack).")
            d.step("Ask the host to restart PHP/the web server if resources are maxed out.")
        else:
            d.head("The web server couldn't be reached.")
            d.step("Check the hosting provider's status page and contact hosting support.")
        d.reason(label, f"Raw page request failed: {http.get('detail')}")
        return
    status = http.get("status", 0)
    if status >= 500:
        d.head(f"The server is returning an error page (HTTP {status}).")
        d.reason(label, f"Returned HTTP {status}: {HTTP_MEANINGS.get(status, 'Server error')}.")
        d.step("Check the hosting error logs (PHP error log) for the time of this alert.")
        d.step("Undo any plugin, theme, or WordPress updates made in the last 24 hours.")
        d.step("If a CDN/proxy is involved (502/504/52x), check whether the origin server is running.")
    elif status in (403, 429):
        d.false_alarm_possible = True
        d.head(f"The site refused the monitor (HTTP {status}). It may be up for real visitors, with a firewall blocking the check.")
        d.reason(label, f"Returned HTTP {status} ({'Forbidden' if status == 403 else 'Too Many Requests'}).")
        d.step("Open the site on a phone using cellular data. If it loads, the site is up and a firewall is blocking the monitor.", first=True)
        d.step(f"Allowlist the user agent '{MONITOR_TAG.split('/')[0]}' in Cloudflare/Wordfence/security settings.")
    elif status == 404:
        d.head(f"The {label.lower()} page is returning 'Not Found' (HTTP 404).")
        d.reason(label, "Returned HTTP 404 (page not found).")
        d.step("Check whether the page was trashed or its URL (slug) changed in WordPress, then re-save Settings > Permalinks.")
    elif status >= 400:
        d.head(f"The {label.lower()} page returned an error (HTTP {status}).")
        d.reason(label, f"Returned HTTP {status}.")
    for sig in http.get("signatures", []):
        d.reason(label, f"Error page detected: {sig}")
        d.head("The server is showing an error page instead of the website.")
        if any(w in sig.lower() for w in BLOCK_WORDS):
            d.false_alarm_possible = True
            d.step("Open the site on a phone using cellular data. If it loads, it's a firewall/bot-protection block on the monitor, not an outage.", first=True)
        elif "maintenance" in sig:
            d.step("Remove the .maintenance file from the WordPress root folder (via hosting file manager or SFTP).", first=True)
        else:
            d.step("Check the hosting PHP error log and deactivate the most recently updated plugin.", first=True)


def _diag_view(d: Diagnosis, target: str, view: str, br: dict) -> None:
    label = TARGETS[target]["label"]
    if br.get("skipped") or view_ok(br):
        return
    if not br.get("loaded"):
        d.reason(label, f"The page didn't load in a real browser: {br.get('load_error')}", view)
        d.step("Look for slow or failing third-party scripts (chat widgets, tracking tags) and purge the site/CDN cache.")
        return
    c = br.get("checks", {})

    logo = c.get("logo")
    if logo and not logo.get("ok"):
        cands = [x for x in logo.get("candidates", []) if x.get("y", 0) < 300]  # pictures far down the page aren't the header logo
        files = [x for x in cands if x.get("isHeaderLogoFile")]
        broken = [x for x in files if not x.get("loaded")]
        if not cands:
            d.reason(label, "Logo: no CreditAssociates logo was found at the top of the page.", view)
            d.step("The header may not be rendering. Check recent edits to the site header template (Theme Builder/Elementor).")
        elif broken:
            d.reason(label, f"Logo: the image file failed to download ({broken[0]['url']}).", view)
            d.step("Open the logo URL directly. If it shows 'Not Found', the file was deleted or renamed in the WordPress "
                   "Media Library. Re-upload it or re-select it in the header settings, then purge cache.")
        elif files and not any(x.get("visible") for x in files) and any(x.get("stuckAnimation") for x in files):
            d.reason(label, "Logo: it's on the page but stuck invisible. The header's fade-in never ran, which happens when site JavaScript breaks.", view)
            d.step("Check the JavaScript errors below. Clear the cache/speed plugin (e.g. WP Rocket, LiteSpeed, Autoptimize); these commonly break scripts.")
        elif files and not any(x.get("visible") for x in files):
            d.reason(label, "Logo: the logo is on the page but hidden.", view)
            d.step("A stylesheet may have failed or the header was edited. Purge cache and review recent header changes.")
        else:
            d.reason(label, "Logo: a logo is present but not where it belongs in the header.", view)
            d.step("The header layout appears broken or changed. Check the header template and whether CSS files loaded.")

    def _saw(chk):
        seen = [x for x in chk.get("saw", []) if x.get("text")]
        if not seen:
            return ""
        notes = [n for n, on in (("only in the menu", seen[0].get("inMenu")), ("hidden", not seen[0].get("visible"))) if on]
        note = f" ({', '.join(notes)})" if notes else ""
        return f' Closest text it found{note}: "{seen[0]["text"]}".'

    def _elsewhere(chk):
        seen = [x for x in chk.get("saw", []) if x.get("text")]
        return f' (The name does appear higher up the page: "{seen[0]["text"]}".)' if seen else ""

    h = c.get("heading")
    if h and not h.get("ok"):
        if not h.get("inDom"):
            d.reason(label, f'Headline: "{HEADING_LABEL}" isn\'t in the page content.' + _saw(h), view)
            d.step("Check the homepage's edit history. The \"How it Works\" section or its wording may have been edited "
                   "or removed. (If the wording changed on purpose, update HEADING_PATTERN in monitor_cas.py.)")
        elif any(m.get("stuckAnimation") for m in h.get("matches", [])):
            d.reason(label, "Headline: it's on the page but stuck invisible. Its entrance animation never ran, which happens when site JavaScript breaks.", view)
            d.step("Check the JavaScript errors below. Clear the cache/minification plugin (e.g. WP Rocket, Autoptimize); these commonly break scripts.")
        else:
            d.reason(label, "Headline: it's on the page but hidden by styling.", view)
            d.step("Check whether the section's responsive visibility settings (desktop/tablet/mobile) were changed.")

    f = c.get("footer")
    if f and not f.get("ok"):
        if not f.get("footerExists") and not f.get("inDom"):
            d.reason(label, "Footer: no footer was found. The page may be cut off partway through." + _elsewhere(f), view)
            d.step("A server error partway through the page often cuts it off. Check the hosting error log and recent "
                   "footer/plugin changes.")
        elif not f.get("inDom"):
            d.reason(label, "Footer: the footer is there, but \"CreditAssociates\" isn't in it." + _elsewhere(f), view)
            d.step("Check recent edits to the footer. (If the footer's wording changed on purpose, update BRAND in monitor_cas.py.)")
        else:
            d.reason(label, "Footer: \"CreditAssociates\" is in the footer but hidden (or its logo image didn't load).", view)
            d.step("Check the footer's mobile/desktop visibility settings, and whether its logo image or CSS files loaded.")

    for chk in (h,):
        if chk and not chk.get("ok") and any(x.get("visible") and not x.get("inMenu") for x in chk.get("saw", [])):
            d.step("Compare the 'closest text it found' above with the live site. If it looks right, this is a false "
                   "alarm from changed wording; update HEADING_PATTERN near the top of monitor_cas.py.", first=True)

    assets = [r for r in br.get("failed_requests", []) if any(x in r.lower() for x in (".css", ".js"))]
    if assets:
        d.reason(label, f"{len(assets)} stylesheet/script file(s) failed to load, which can break layout, animations, and forms.", view)
        d.step("Purge the WordPress cache plugin and the CDN cache, then re-check.")


def diagnose(base: dict, results: dict) -> Diagnosis:
    d = Diagnosis()
    host = urlparse(SITE).hostname
    dns, tls = base.get("dns", {}), base.get("tls", {})

    if not dns.get("ok"):
        d.head("The domain name isn't resolving (DNS failure), so visitors can't reach the site at all.")
        d.reason("Whole site", f"DNS lookup for {host} failed: {dns.get('error')}")
        d.step("Confirm the domain hasn't expired at the registrar.")
        d.step("Check the DNS provider for an outage or recently changed/deleted DNS records.")
        return d
    if tls and not tls.get("ok"):
        if tls.get("kind") == "cert":
            d.head("The SSL certificate is invalid or expired, so browsers show a security warning instead of the site.")
            d.reason("Whole site", f"SSL certificate problem: {tls.get('error')}")
            d.step("Renew or reissue the SSL certificate in the hosting or CDN dashboard.")
            d.step("Make sure the certificate covers both creditassociates.com and www.creditassociates.com.")
        else:
            d.head("The web server isn't accepting connections. The hosting server or CDN appears to be down.")
            d.reason("Whole site", f"Secure connection failed: {tls.get('error')}")
            d.step("Check the hosting provider's status page and the server's CPU, memory, and disk usage.")
            d.step("Contact hosting support and give them the time of this alert.")
    elif tls.get("ok") and tls.get("days_left", 999) < 14:
        d.reason("Whole site", f"Note: the SSL certificate expires in {tls['days_left']} days ({tls['expires']}).")

    for t in TARGETS:
        _diag_http(d, results[t].get("http", {}), TARGETS[t]["label"])

    # Headline from the pattern of what failed (used only if no server-level cause was found above)
    failing = {(t, v) for t in TARGETS for v in VIEWS if not view_ok(results[t].get(v, {}))}
    all_views = {(t, v) for t in TARGETS for v in VIEWS}
    order = list(CHECK_LABELS)
    broken_items = sorted({k for t in TARGETS for v in VIEWS for k in TARGET_CHECKS[t]
                           if results[t].get(v, {}).get("loaded")
                           and not results[t][v].get("checks", {}).get(k, {}).get("ok")}, key=order.index)
    any_unloaded = any(not results[t].get(v, {}).get("loaded") for t in TARGETS for v in VIEWS)
    if failing == all_views and (any_unloaded or len(broken_items) == len(order)):
        d.head("The server responds, but the homepage isn't displaying correctly on any device. Visitors likely see a broken page.")
    elif failing == all_views:
        names = " and ".join(f'"{CHECK_LABELS[k]}"' for k in broken_items)
        d.head(f"The site is up, but part of the homepage is broken: {names} "
               f"{'is' if len(broken_items) == 1 else 'are'} not displaying on desktop or mobile.")
    elif failing and all(v == "mobile" for _, v in failing):
        d.head("Desktop looks fine, but the MOBILE version is broken, and most visitors are on phones.")
    elif failing and all(v == "desktop" for _, v in failing):
        d.head("Mobile looks fine, but the DESKTOP version is broken.")
    else:
        d.head("Parts of the site are missing or broken.")

    for t in TARGETS:
        for v in VIEWS:
            _diag_view(d, t, v, results[t].get(v, {}))

    d.step("Check whether anything changed recently (plugin/theme/WordPress updates, page edits, DNS or hosting changes). "
           "Most outages follow a change.")
    d.step("Open 'View run & screenshots' below to see exactly what the monitor saw.")
    return d


# ------------------------------------------------------------------ Teams cards
def _tb(text, **kw):
    return {"type": "TextBlock", "text": text, "wrap": True, **kw}


def _fmt_duration(minutes: float) -> str:
    m = int(round(minutes))
    if m < 60:
        return f"{m} min"
    h, m = divmod(m, 60)
    return f"{h}h {m}m" if m else f"{h}h"


def _view_summary(t: str, br: dict) -> str:
    if br.get("skipped") or not br.get("loaded"):
        return "⚪ Page didn't load"
    c = br.get("checks", {})
    return " · ".join(f"{'✅' if c.get(k, {}).get('ok') else '❌'} {CHECK_LABELS[k]}" for k in TARGET_CHECKS[t])


def _actions():
    acts = [{"type": "Action.OpenUrl", "title": "Open the website", "url": TARGETS["home"]["url"]}]
    if RUN_URL:
        acts.append({"type": "Action.OpenUrl", "title": "View run & screenshots", "url": RUN_URL})
    return acts


def _card(body, actions):
    return {"$schema": "http://adaptivecards.io/schemas/adaptive-card.json", "type": "AdaptiveCard",
            "version": "1.4", "msteams": {"width": "Full"}, "body": body, "actions": actions}


def build_down_card(base, results, d: Diagnosis, down_since: dt.datetime, reminder=False, test=False) -> dict:
    now = dt.datetime.now(CT)
    dur = _fmt_duration((now - down_since).total_seconds() / 60)
    prefix = "🧪 TEST ALERT: " if test else ("🔴 STILL DOWN: " if reminder else "🔴 ")
    title = f"{prefix}{SITE_NAME} {'(down ' + dur + ')' if reminder else 'is DOWN'}"
    sub = (f"Down since {down_since.strftime('%I:%M %p CT')}. Still failing as of {now.strftime('%I:%M %p CT')}. "
           f"Next reminder in {REMINDER_MINUTES} min unless it recovers."
           if reminder else f"Detected {now.strftime('%b %d, %Y %I:%M %p CT')}. Confirmed on 2 checks {RETRY_DELAY}s apart.")

    facts = []
    for t in TARGETS:
        for v in VIEWS:
            facts.append({"title": f"{TARGETS[t]['label']} ({v})", "value": _view_summary(t, results[t].get(v, {}))})
    home_http = results["home"].get("http", {})
    facts.append({"title": "Server response (homepage)",
                  "value": f"HTTP {home_http['status']} in {home_http['ttfb_ms']:,} ms" if "status" in home_http
                  else f"No response ({home_http.get('error', 'n/a')})"})

    body = [
        {"type": "Container", "style": "attention", "bleed": True, "items": [
            _tb(title, size="Large", weight="Bolder"), _tb(sub, isSubtle=True, spacing="None")]},
        _tb(f"**Most likely cause:** {d.headline}", spacing="Medium"),
        {"type": "FactSet", "facts": facts},
    ]
    if d.false_alarm_possible:
        body.append(_tb("⚠️ **This may be a false alarm.** The site might be fine for real visitors while a firewall "
                        "blocks the monitor. Verify on a phone using cellular data.", color="Warning"))
    if d.reasons:
        body += [_tb("**Why we flagged it**", spacing="Medium"), _tb("\n".join(f"- {r}" for r in d.reasons))]
    body += [_tb("**What to check first**", spacing="Medium"),
             _tb("\n".join(f"{i}. {s}" for i, s in enumerate(d.steps, 1)))]

    tech = []
    if base.get("dns", {}).get("ips"):
        tech.append(f"- Server IP(s): {', '.join(base['dns']['ips'][:4])}")
    if home_http.get("server") or home_http.get("cache"):
        tech.append(f"- Server/CDN: {home_http.get('server') or 'n/a'} | cache: {home_http.get('cache') or 'n/a'}")
    if base.get("tls", {}).get("ok"):
        tech.append(f"- SSL certificate valid until {base['tls']['expires']} ({base['tls']['days_left']} days)")
    seen = set()
    for t in TARGETS:
        for v in VIEWS:
            br = results[t].get(v, {})
            if view_ok(br):
                continue
            for r in br.get("failed_requests", [])[:4]:
                if r not in seen:
                    seen.add(r)
                    tech.append(f"- Failed file ({TARGETS[t]['label']}, {v}): {r}")
            for e in br.get("console_errors", [])[:2]:
                if e not in seen:
                    seen.add(e)
                    tech.append(f"- JavaScript error ({TARGETS[t]['label']}, {v}): {e}")
            for n in br.get("notes", []):
                tech.append(f"- {TARGETS[t]['label']} ({v}): {n}")
    if tech:
        body += [_tb("**Technical details (for the web/hosting team)**", spacing="Medium", size="Small"),
                 _tb("\n".join(tech[:14]), size="Small", isSubtle=True)]
    return _card(body, _actions())


def build_recovery_card(down_since: dt.datetime, prior_headline: str, test=False) -> dict:
    now = dt.datetime.now(CT)
    dur = _fmt_duration((now - down_since).total_seconds() / 60)
    body = [
        {"type": "Container", "style": "good", "bleed": True, "items": [
            _tb(f"{'🧪 TEST: ' if test else ''}✅ {SITE_NAME} is back UP", size="Large", weight="Bolder"),
            _tb(f"Recovered {now.strftime('%b %d, %Y %I:%M %p CT')}", isSubtle=True, spacing="None")]},
        {"type": "FactSet", "facts": [
            {"title": "Down for", "value": f"about {dur}"},
            {"title": "Went down", "value": down_since.strftime("%b %d, %I:%M %p CT")},
            {"title": "What was wrong", "value": prior_headline or "n/a"},
            {"title": "Now passing", "value": "Logo, How it Works headline, and footer, on desktop and mobile"},
        ]},
        _tb("Tip: note what fixed it in this chat so the team knows next time.", isSubtle=True, size="Small"),
    ]
    return _card(body, _actions()[:1])


def send_to_teams(card: dict) -> bool:
    if not WEBHOOK:
        print("TEAMS_WEBHOOK_URL is not set. Card that would have been sent:")
        print(json.dumps(card, indent=2, ensure_ascii=False))
        return False
    payload = {"type": "message", "attachments": [
        {"contentType": "application/vnd.microsoft.card.adaptive", "contentUrl": None, "content": card}]}
    try:
        r = requests.post(WEBHOOK, json=payload, timeout=30)
    except requests.RequestException as e:
        print(f"Could not reach the Teams webhook: {e}")
        return False
    if r.status_code in (200, 202):
        print("Teams message sent.")
        return True
    print(f"Teams webhook returned HTTP {r.status_code}: {r.text[:300]}")
    return False


# ------------------------------------------------------------------ state (remembered between runs)
def load_state() -> dict:
    try:
        return json.loads(STATE_FILE.read_text())
    except Exception:  # noqa: BLE001
        return {"status": "up"}


def save_state(state: dict) -> None:
    STATE_FILE.parent.mkdir(parents=True, exist_ok=True)
    STATE_FILE.write_text(json.dumps(state, indent=2) + "\n")


def _parse(ts: str | None) -> dt.datetime | None:
    return dt.datetime.fromisoformat(ts) if ts else None


# ------------------------------------------------------------------ main
def _sample_results():
    bad_logo = {"loaded": True, "load_ms": 4100, "console_errors": [], "notes": [],
                "failed_requests": ["HTTP 404: https://www.creditassociates.com/wp-content/uploads/creditassociates-logo.svg"],
                "checks": {"logo": {"ok": False, "candidates": [{"isHeaderLogoFile": True, "loaded": False, "visible": False,
                                    "url": "https://www.creditassociates.com/wp-content/uploads/creditassociates-logo.svg"}]},
                           "heading": {"ok": True, "inDom": True}, "footer": {"ok": True, "inDom": True}}}
    base = {"dns": {"ok": True, "ips": ["203.0.113.20"]}, "tls": {"ok": True, "expires": "2027-02-01", "days_left": 103}}
    http = {"ok": True, "status": 200, "ttfb_ms": 580, "server": "cloudflare", "cache": "HIT", "signatures": []}
    return base, {"home": {"http": http, "desktop": bad_logo, "mobile": bad_logo}}


def main() -> int:
    if "--test-alert" in sys.argv:
        kind = sys.argv[sys.argv.index("--test-alert") + 1] if len(sys.argv) > sys.argv.index("--test-alert") + 1 else "down"
        since = dt.datetime.now(CT) - dt.timedelta(minutes=47)
        if kind == "recovery":
            card = build_recovery_card(since, "The server responds, but the homepage logo didn't load.", test=True)
        else:
            base, results = _sample_results()
            card = build_down_card(base, results, diagnose(base, results), dt.datetime.now(CT), test=True)
        return 0 if send_to_teams(card) else 2

    state = load_state()
    up, base, results = run_all()
    if not up:
        print(f"A check failed. Re-checking in {RETRY_DELAY}s to rule out a momentary blip...")
        time.sleep(RETRY_DELAY)
        up, base, results = run_all()

    now = dt.datetime.now(CT)
    print(json.dumps({"time": now.isoformat(), "up": up, "previous_status": state.get("status"),
                      "views": {f"{t}/{v}": _view_summary(t, results[t].get(v, {})) for t in TARGETS for v in VIEWS},
                      "what_it_found": {v: {
                          "logo": [f"{c.get('kind')}: {c.get('file')} at x={c.get('x')}, y={c.get('y')}, {c.get('w')}px wide"
                                   f"{'' if c.get('visible') else (' (waiting for its fade-in; counts as OK)' if c.get('waitingToFadeIn') else ' (hidden)')}"
                                   for c in results["home"].get(v, {}).get("checks", {}).get("logo", {}).get("candidates", [])[:3]],
                          "top_of_page_graphics": results["home"].get(v, {}).get("checks", {}).get("logo", {}).get("topGraphics", []),
                          "headline": [m.get("text") for m in results["home"].get(v, {}).get("checks", {}).get("heading", {}).get("matches", [])[:2]],
                          "footer": [m.get("text") for m in results["home"].get(v, {}).get("checks", {}).get("footer", {}).get("matches", [])[:2]],
                          "page_problems": (results["home"].get(v, {}).get("console_errors", [])[:3]
                                            + [r for r in results["home"].get(v, {}).get("failed_requests", []) if ".js" in r.lower()][:3]),
                      } for v in VIEWS}},
                     indent=2, ensure_ascii=False, default=str))

    if up:
        if state.get("status") == "down":
            since = _parse(state.get("since")) or now
            print(f"✅ RECOVERED after {_fmt_duration((now - since).total_seconds() / 60)}.")
            send_to_teams(build_recovery_card(since, state.get("headline", "")))
            save_state({"status": "up", "since": now.isoformat()})
        else:
            print("✅ UP: all checks passing on desktop and mobile.")
        return 0

    d = diagnose(base, results)
    print("❌ DOWN:", d.headline)
    for r in d.reasons:
        print("  -", r)

    if state.get("status") != "down":
        sent = send_to_teams(build_down_card(base, results, d, now))
        save_state({"status": "down", "since": now.isoformat(), "headline": d.headline,
                    "last_alert": now.isoformat() if sent else None})
    else:
        since = _parse(state.get("since")) or now
        last = _parse(state.get("last_alert"))
        if last is None or (now - last).total_seconds() >= REMINDER_MINUTES * 60 - 120:
            sent = send_to_teams(build_down_card(base, results, d, since, reminder=True))
            if sent:
                state["last_alert"] = now.isoformat()
        else:
            print(f"Still down; last alert at {last.strftime('%I:%M %p CT')}. Next reminder after {REMINDER_MINUTES} min.")
        state["headline"] = d.headline
        save_state(state)
    return 1  # marks the GitHub run red and keeps the screenshots


if __name__ == "__main__":
    sys.exit(main())
