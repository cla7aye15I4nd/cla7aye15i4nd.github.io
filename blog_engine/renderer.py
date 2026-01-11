"""
HTML rendering with Jinja2 templates.
"""

from collections import defaultdict
from pathlib import Path
from typing import Dict, List

from jinja2 import Environment, FileSystemLoader

from .models import Article


class BlogRenderer:
    """Render blog articles and archive pages using Jinja2 templates."""

    def __init__(self, template_dir: Path):
        """
        Initialize renderer with template directory.

        Args:
            template_dir: Path to directory containing Jinja2 templates
        """
        self.env = Environment(loader=FileSystemLoader(str(template_dir)))

    def render_article(self, article: Article) -> str:
        """
        Render article to HTML using article.html template.

        Args:
            article: Article to render

        Returns:
            Complete HTML string
        """
        template = self.env.get_template('article.html')
        return template.render(
            title=article.title,
            date=article.date,
            tags=article.tags,
            description=article.description,
            content=article.html_content,
            toc=article.toc_html
        )

    def render_archive(self, articles: List[Article]) -> str:
        """
        Render archive page listing all articles.

        Groups articles by date (chronological) and by tag.

        Args:
            articles: List of articles to include in archive

        Returns:
            Complete HTML string for archive page
        """
        # Sort articles by date (newest first)
        sorted_articles = sorted(articles, key=lambda x: x.date, reverse=True)

        # Group articles by tag
        articles_by_tag = self._group_by_tag(sorted_articles)

        # Render template
        template = self.env.get_template('archive.html')
        return template.render(
            articles=sorted_articles,
            articles_by_tag=articles_by_tag
        )

    def _group_by_tag(self, articles: List[Article]) -> Dict[str, List[Article]]:
        """
        Group articles by tag.

        Args:
            articles: List of articles to group

        Returns:
            Dictionary mapping tag names to lists of articles
        """
        tag_dict = defaultdict(list)

        for article in articles:
            for tag in article.tags:
                tag_dict[tag].append(article)

        # Sort each tag's articles by date (newest first)
        for tag in tag_dict:
            tag_dict[tag] = sorted(tag_dict[tag], key=lambda x: x.date, reverse=True)

        # Sort tags alphabetically
        return dict(sorted(tag_dict.items()))
