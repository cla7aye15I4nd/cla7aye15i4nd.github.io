"""
Data models for blog articles and metadata.
"""

from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import List, Optional


@dataclass
class ArticleMetadata:
    """Article frontmatter metadata with validation."""

    date: str
    title: Optional[str] = None
    tags: List[str] = field(default_factory=list)
    description: Optional[str] = None

    def __post_init__(self):
        """Validate and normalize metadata after initialization."""
        # Validate and normalize date
        if self.date:
            # Handle both string and datetime.date objects from frontmatter parser
            if hasattr(self.date, 'strftime'):
                # It's a datetime.date object, convert to string
                self.date = self.date.strftime('%Y-%m-%d')
            else:
                # It's a string, validate format
                try:
                    datetime.strptime(self.date, '%Y-%m-%d')
                except ValueError:
                    raise ValueError(f"Invalid date format: {self.date}. Expected YYYY-MM-DD")
        else:
            raise ValueError("Date is required in frontmatter")

        # Normalize tags (lowercase, strip whitespace)
        if self.tags:
            self.tags = [tag.strip().lower() for tag in self.tags]


@dataclass
class Article:
    """Complete article representation."""

    metadata: ArticleMetadata
    source_path: Path
    markdown_content: str
    html_content: str = ""

    @property
    def filename(self) -> str:
        """Get the filename stem without extension."""
        return self.source_path.stem

    @property
    def html_filename(self) -> str:
        """Get the output HTML filename."""
        return f"{self.filename}.html"

    @property
    def title(self) -> str:
        """Get article title from metadata or filename."""
        if self.metadata.title:
            return self.metadata.title
        # Fallback to filename converted to title case
        return self.filename.replace('-', ' ').replace('_', ' ').title()

    @property
    def date(self) -> str:
        """Get article date."""
        return self.metadata.date

    @property
    def tags(self) -> List[str]:
        """Get article tags."""
        return self.metadata.tags

    @property
    def description(self) -> Optional[str]:
        """Get article description."""
        return self.metadata.description


@dataclass
class BuildResult:
    """Result of a build operation."""

    success_count: int = 0
    error_count: int = 0
    errors: List[str] = field(default_factory=list)

    def add_success(self):
        """Increment success count."""
        self.success_count += 1

    def add_error(self, error: str):
        """Add an error message."""
        self.errors.append(error)
        self.error_count += 1
