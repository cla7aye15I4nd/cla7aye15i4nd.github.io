"""
Custom markdown preprocessing for GitHub-flavored markdown.
"""

import re


def normalize_list_indentation(markdown_text: str) -> str:
    """
    Convert 2-space GitHub-style indents to 4-space for markdown parser.

    GitHub uses 2-space indentation for nested lists, but standard markdown
    requires 4-space indentation. This function normalizes the indentation.

    Args:
        markdown_text: Markdown content with potential 2-space indents

    Returns:
        Markdown content with normalized 4-space indents
    """
    lines = markdown_text.split('\n')
    result = []

    for line in lines:
        # Count leading spaces
        stripped = line.lstrip(' ')

        # Check if this is a list item line
        if stripped.startswith(('-', '*', '+')) or (stripped and stripped[0].isdigit() and '.' in stripped[:4]):
            indent = len(line) - len(stripped)
            # Convert 2-space multiples to 4-space multiples
            if indent > 0:
                new_indent = (indent // 2) * 4
                result.append(' ' * new_indent + stripped)
            else:
                result.append(line)
        else:
            result.append(line)

    return '\n'.join(result)


def convert_github_callouts(markdown_text: str) -> str:
    """
    Convert GitHub-style callouts to admonition format.

    Converts:
        > [!NOTE] Title
        > content
        > more content

    To:
        !!! note "Title"
            content
            more content

    Args:
        markdown_text: Markdown content with GitHub callouts

    Returns:
        Markdown content with admonition-style callouts
    """
    def convert_callout(match):
        callout_type = match.group(1).lower()
        # Group(2) is the optional title (only if present)
        title = match.group(2).strip() if match.group(2) else callout_type.upper()
        content_lines = match.group(3).strip()

        # Remove leading '> ' from content lines
        content = re.sub(r'^>\s*', '', content_lines, flags=re.MULTILINE)
        # Indent content by 4 spaces for admonition
        content = '\n'.join('    ' + line if line else '' for line in content.split('\n'))

        return f'!!! {callout_type} "{title}"\n{content}'

    # Match GitHub callouts: > [!TYPE] optional title\n> content
    # Pattern: > [!TYPE] title\n  OR  > [!TYPE]\n
    pattern = r'>\s*\[!(NOTE|WARNING|IMPORTANT|TIP|CAUTION)\](?: ([^\n>]+?))?\s*\n((?:>.*\n?)+)'
    return re.sub(pattern, convert_callout, markdown_text, flags=re.MULTILINE | re.IGNORECASE)


def add_blank_lines_before_lists(markdown_text: str) -> str:
    """
    Add blank line before lists that immediately follow text (GitHub-style).

    This ensures lists are properly recognized by the markdown parser.

    Args:
        markdown_text: Markdown content

    Returns:
        Markdown content with blank lines before lists
    """
    return re.sub(r'([^\n])\n([-*+]|\d+\.)\s+', r'\1\n\n\2 ', markdown_text)


def preprocess_markdown(markdown_text: str) -> str:
    """
    Apply all markdown preprocessing steps.

    Args:
        markdown_text: Raw markdown content

    Returns:
        Preprocessed markdown content ready for conversion
    """
    # Step 1: Convert GitHub-style callouts to admonition format
    markdown_text = convert_github_callouts(markdown_text)

    # Step 2: Normalize list indentation (2-space → 4-space)
    markdown_text = normalize_list_indentation(markdown_text)

    # Step 3: Add blank line before lists
    markdown_text = add_blank_lines_before_lists(markdown_text)

    return markdown_text
