// Day / night theme.  style.css paints from the system preference by default
// and honours an explicit choice on <html data-theme="light|dark">; this module
// owns that choice: it is remembered in localStorage (index.html applies it
// before first paint with a tiny inline script), toggled by every element with
// [data-theme-toggle] (the desktop header button here; the phone toggle is a
// Preact component in ui.js that calls toggleTheme), and announced to listeners
// through a 'themechange' event on document.
const KEY = 'theme';

const stored = () => { try { return localStorage.getItem(KEY); } catch (_) { return null; } };
const remember = t => { try { t ? localStorage.setItem(KEY, t) : localStorage.removeItem(KEY); } catch (_) { /* private mode */ } };

/** The theme the page paints with right now: the explicit choice, else the system's. */
export function currentTheme() {
  const explicit = document.documentElement.dataset.theme;
  if (explicit === 'light' || explicit === 'dark') return explicit;
  return typeof matchMedia === 'function' && matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
}

/** Paint and remember `theme` ('light' | 'dark'), or null to follow the system again. */
export function applyTheme(theme) {
  if (theme) document.documentElement.dataset.theme = theme;
  else delete document.documentElement.dataset.theme;
  remember(theme);
  paintThemeColor(theme);
  for (const b of document.querySelectorAll('[data-theme-toggle]')) label(b);
  document.dispatchEvent(new CustomEvent('themechange', { detail: currentTheme() }));
}

const THEME_COLOR = { light: '#f7f6f2', dark: '#191817' };
/** Keep the browser chrome (<meta name=theme-color>) in step with an explicit choice;
 *  with no choice the two media-gated metas in index.html follow the system again. */
function paintThemeColor(theme) {
  for (const m of document.querySelectorAll('meta[name="theme-color"]')) {
    const media = m.getAttribute('media') || '';
    const system = media.includes('dark') ? 'dark' : 'light';
    m.setAttribute('content', THEME_COLOR[theme || system]);
  }
}

export function toggleTheme() { applyTheme(currentTheme() === 'dark' ? 'light' : 'dark'); }

/** The toggle's accessible name says what pressing it will do. */
export function label(button) {
  const next = currentTheme() === 'dark' ? 'light' : 'dark';
  button.setAttribute('aria-label', `switch to the ${next} theme`);
  button.title = `${next} theme`;
}

// boot: honour a remembered choice (index.html's inline script already did, so
// no flash) and wire the static toggles
applyTheme(stored());
for (const b of document.querySelectorAll('[data-theme-toggle]')) b.addEventListener('click', toggleTheme);
