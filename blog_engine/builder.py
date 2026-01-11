"""
Build orchestration for blog generation.
"""

import glob
from pathlib import Path
from typing import List, Optional

from .markdown_ext import preprocess_markdown
from .models import Article, BuildResult
from .parser import FrontmatterParser, MarkdownParser, ParseError
from .renderer import BlogRenderer


class BlogBuilder:
    """Orchestrate the blog build process."""

    def __init__(self, source_dir: Path, output_dir: Path, template_dir: Path):
        """
        Initialize builder with directories.

        Args:
            source_dir: Directory containing markdown source files
            output_dir: Directory for generated HTML files
            template_dir: Directory containing Jinja2 templates
        """
        self.source_dir = Path(source_dir)
        self.output_dir = Path(output_dir)
        self.template_dir = Path(template_dir)

        # Initialize components
        self.frontmatter_parser = FrontmatterParser()
        self.markdown_parser = MarkdownParser()
        self.renderer = BlogRenderer(template_dir)

    def build(self, files: Optional[List[str]] = None, verbose: bool = False) -> BuildResult:
        """
        Build blog from markdown files.

        Args:
            files: Optional list of specific files to process. If None, process all .md files
            verbose: Whether to print verbose output

        Returns:
            BuildResult with success/error counts
        """
        result = BuildResult()

        # Discover markdown files
        if files:
            md_files = [Path(f) for f in files]
        else:
            md_files = list(self.source_dir.glob('*.md'))

        if not md_files:
            if verbose:
                print("No markdown files found")
            return result

        if verbose:
            print(f"Found {len(md_files)} markdown file(s)")

        # Process each file
        articles = []
        for md_file in md_files:
            try:
                if verbose:
                    print(f"Processing {md_file.name}...")

                # Parse and build article
                article = self._process_file(md_file)
                articles.append(article)

                # Write article HTML
                self._write_article(article, verbose)
                result.add_success()

            except Exception as e:
                error_msg = f"{md_file.name}: {str(e)}"
                result.add_error(error_msg)
                if verbose:
                    print(f"  ✗ Error: {error_msg}")

        # Generate archive page if we have any articles
        if articles:
            try:
                self._generate_archive(articles, verbose)
            except Exception as e:
                result.add_error(f"Archive generation failed: {str(e)}")
                if verbose:
                    print(f"  ✗ Error generating archive: {str(e)}")

        return result

    def _process_file(self, md_file: Path) -> Article:
        """
        Process a single markdown file into an Article.

        Args:
            md_file: Path to markdown file

        Returns:
            Article object with parsed metadata and content

        Raises:
            ParseError: If parsing fails
        """
        # Parse frontmatter
        metadata, markdown_content = self.frontmatter_parser.parse_file(md_file)

        # If title not in metadata, try to extract from markdown
        if not metadata.title:
            title = self.markdown_parser.extract_title(markdown_content)
            if title:
                metadata.title = title

        # Preprocess markdown for GitHub compatibility
        processed_markdown = preprocess_markdown(markdown_content)

        # Convert to HTML
        html_content, toc_html = self.markdown_parser.convert(processed_markdown)

        # Create article object
        article = Article(
            metadata=metadata,
            source_path=md_file,
            markdown_content=markdown_content,
            html_content=html_content,
            toc_html=toc_html
        )

        return article

    def _write_article(self, article: Article, verbose: bool = False):
        """
        Render and write article HTML to disk.

        Args:
            article: Article to render
            verbose: Whether to print verbose output
        """
        html = self.renderer.render_article(article)
        output_path = self.output_dir / article.html_filename

        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html)

        if verbose:
            print(f"  → Generated {output_path.name}")

    def _generate_archive(self, articles: List[Article], verbose: bool = False):
        """
        Generate archive page listing all articles.

        Args:
            articles: List of articles to include
            verbose: Whether to print verbose output
        """
        html = self.renderer.render_archive(articles)
        output_path = self.output_dir / 'index.html'

        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html)

        if verbose:
            print(f"Generated {output_path}")

    def clean(self, verbose: bool = False) -> int:
        """
        Remove all generated HTML files from output directory.

        Args:
            verbose: Whether to print verbose output

        Returns:
            Number of files removed
        """
        pattern = str(self.output_dir / '*.html')
        html_files = glob.glob(pattern)

        for file in html_files:
            Path(file).unlink()
            if verbose:
                print(f"Removed {file}")

        if verbose:
            print(f"Cleaned {len(html_files)} HTML file(s)")

        return len(html_files)
