const link = document.querySelector('#github-star');
const countNode = document.querySelector('#github-star-count');

if (link && countNode) {
  fetch('https://api.github.com/repos/thomasahle/fast-polynomials', {
    headers: { Accept: 'application/vnd.github+json' },
  })
    .then(response => {
      if (!response.ok) throw new Error(`GitHub API returned ${response.status}`);
      return response.json();
    })
    .then(repo => {
      const count = Number(repo.stargazers_count);
      if (!Number.isSafeInteger(count) || count < 0) return;

      countNode.textContent = new Intl.NumberFormat().format(count);
      countNode.hidden = false;
      link.setAttribute(
        'aria-label',
        `Star fast-polynomials on GitHub (${count} ${count === 1 ? 'star' : 'stars'})`,
      );
    })
    .catch(() => {
      // The repository link remains fully functional if GitHub is unavailable
      // or the anonymous API rate limit has been reached.
    });
}
