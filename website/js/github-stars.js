// Live GitHub star count: fills the desktop header button here and is imported
// by ui.js for the compact (phone) header.  The page keeps working when GitHub
// is unavailable or the anonymous API rate limit has been reached.
const REPO_API = 'https://api.github.com/repos/thomasahle/fast-polynomials';

let pending = null;
/** The repository's star count (memoized promise; null when unavailable). */
export function fetchStars() {
  pending ??= fetch(REPO_API, { headers: { Accept: 'application/vnd.github+json' } })
    .then(response => {
      if (!response.ok) throw new Error(`GitHub API returned ${response.status}`);
      return response.json();
    })
    .then(repo => {
      const count = Number(repo.stargazers_count);
      return Number.isSafeInteger(count) && count >= 0 ? count : null;
    })
    .catch(() => null);
  return pending;
}

const link = document.querySelector('#github-star');
const countNode = document.querySelector('#github-star-count');
if (link && countNode) {
  fetchStars().then(count => {
    if (count === null) return;
    countNode.textContent = new Intl.NumberFormat().format(count);
    countNode.hidden = false;
    link.setAttribute('aria-label',
      `Star fast-polynomials on GitHub (${count} ${count === 1 ? 'star' : 'stars'})`);
  });
}
