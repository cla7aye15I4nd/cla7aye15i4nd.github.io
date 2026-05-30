# dataisland.org

Personal homepage, research archive, and technical blog for Zheng Yu.

The site is statically generated from YAML, Markdown, and Jinja templates into
`dist/`. It keeps the deployment surface simple while adding a small app-shell
navigation layer so internal pages feel like a single-page site.

## Quick Start

```sh
make install      # uv sync
make build        # render dist/
make serve        # local dev server with watch + rebuild
make check        # mypy + ruff + build
```

For a plain static preview after building:

```sh
python3 -m http.server 8000 -d dist
```

Then open `http://127.0.0.1:8000/`.

## Structure

```text
content/data/        Structured data for profile, news, publications, etc.
content/blog/        Blog posts as Markdown with YAML frontmatter
content/pages/       Top-level generated pages
templates/           Jinja2 templates
static/              CSS, fonts, icons, and the lightweight SPA script
src/site_builder/    Static site generator
dist/                Build output
```

## Frontend

- `templates/index.html` renders the main profile page.
- `templates/archive.html` renders the blog archive.
- `templates/papers.html` renders the paper archive.
- `templates/article.html` renders individual posts.
- `static/style.css` contains the shared print-like visual system.
- `static/spa.js` intercepts same-origin HTML links, fetches the next page, swaps
  the persistent `#app` shell, updates the URL/title, and preserves browser
  back/forward behavior.

External links, PDFs, downloads, `mailto:` links, and `target="_blank"` links
are intentionally left to the browser.

## Content

Most homepage content should come from YAML rather than hard-coded template text:

- Profile and homepage copy: `content/data/profile.yaml`
- News: `content/data/news.yaml`
- Experience: `content/data/experience.yaml`
- Publications: `content/data/publications.yaml`
- Talks: `content/data/talks.yaml`

Blog posts live in `content/blog/`. Bilingual posts share a slug and use the
language in the filename:

```text
content/blog/btc.md       # English -> dist/blog/btc.html
content/blog/btc.zh.md    # Chinese -> dist/blog/btc.zh.html
```

## Checks

Before deploying, run:

```sh
make check
```

For quick iteration on styling or templates:

```sh
uv run site build
uv run ruff check src
```

## Deployment

Pushing to `main` triggers `.github/workflows/deploy.yml`, which type-checks,
lints, builds the resume if needed, renders `dist/`, and publishes it to GitHub
Pages. The repository's Pages source should be set to **GitHub Actions**.
