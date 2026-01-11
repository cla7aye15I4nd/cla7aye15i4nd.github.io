"""
Frontmatter and markdown parsing.
"""

import re
from pathlib import Path
from typing import Tuple

import frontmatter
import markdown

from .models import Article, ArticleMetadata


class ParseError(Exception):
    """Exception raised when parsing fails."""
    pass


class FrontmatterParser:
    """Parse YAML frontmatter from markdown files."""

    def parse_file(self, path: Path) -> Tuple[ArticleMetadata, str]:
        """
        Parse markdown file with YAML frontmatter.

        Args:
            path: Path to markdown file

        Returns:
            Tuple of (ArticleMetadata, markdown_content)

        Raises:
            ParseError: If parsing fails
        """
        try:
            post = frontmatter.load(path)

            # Extract metadata with defaults
            metadata = ArticleMetadata(
                date=post.get('date', ''),
                title=post.get('title'),
                tags=post.get('tags', []),
                description=post.get('description')
            )

            return metadata, post.content

        except Exception as e:
            raise ParseError(f"Failed to parse {path}: {e}")


class MarkdownParser:
    """Convert markdown to HTML with GitHub-flavored extensions."""

    def __init__(self):
        """Initialize markdown parser with extensions."""
        self.md = markdown.Markdown(extensions=[
            'pymdownx.superfences',      # Better code blocks
            'pymdownx.arithmatex',        # Math formula support
            'pymdownx.magiclink',         # Auto-link URLs
            'pymdownx.betterem',          # Better emphasis handling
            'pymdownx.tasklist',          # Task lists
            'pymdownx.emoji',             # Emoji support
            'pymdownx.highlight',         # Syntax highlighting
            'tables',                     # Tables
            'fenced_code',                # Fenced code blocks
            'sane_lists',                 # Better list handling
            'attr_list',                  # Attribute lists
            'def_list',                   # Definition lists
            'admonition'                  # Admonitions (for callouts)
        ], extension_configs={
            'pymdownx.highlight': {
                'css_class': 'highlight',
                'use_pygments': False  # Use CSS classes instead of inline styles
            },
            'pymdownx.superfences': {
                'custom_fences': []
            },
            'pymdownx.arithmatex': {
                'generic': True  # Use generic mode for MathJax
            }
        })

    def convert(self, content: str) -> str:
        """
        Convert markdown content to HTML.

        Args:
            content: Markdown text

        Returns:
            HTML string
        """
        # Reset parser state
        self.md.reset()

        # Convert to HTML
        return self.md.convert(content)

    def extract_title(self, markdown_content: str) -> str:
        """
        Extract title from first H1 heading in markdown.

        Args:
            markdown_content: Markdown text

        Returns:
            Title string or empty string if not found
        """
        pattern = r'^#\s+(.+)$'
        match = re.search(pattern, markdown_content, re.MULTILINE)

        if match:
            return match.group(1).strip()

        return ""
