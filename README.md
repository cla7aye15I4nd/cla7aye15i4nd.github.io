# dataisland.org

Personal homepage and blog. Sources under `content/` and `templates/`, built into `dist/`, deployed via GitHub Actions.

## Quick start

```sh
make install      # uv sync
make build        # render dist/
make serve        # local dev server with watch
make check        # typecheck + lint + strict build
```

## Layout

```
content/data/        Structured data consumed by templates (news, publications, ...)
content/pages/       Top-level pages (index.yaml, 404.yaml, patchagent.html, ...)
content/blog/        Blog posts as markdown with YAML frontmatter
templates/           Jinja2 templates (base, index, article, archive, partials/)
static/              Copied to dist/static/ as-is
src/site_builder/    Build engine
```

## Bilingual posts

Posts share a `slug` across languages; the language is part of the filename:

```
content/blog/btc.md       # lang: en  -> dist/blog/btc.html
content/blog/btc.zh.md    # lang: zh  -> dist/blog/btc.zh.html
```

The archive merges entries by slug and renders a language switcher on each post.

## Deployment

Pushing to `main` triggers `.github/workflows/deploy.yml` which builds the site
and publishes `dist/` to GitHub Pages. The repository's Pages source must be
set to "GitHub Actions".
