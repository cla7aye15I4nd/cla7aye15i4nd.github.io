#!/usr/bin/env python3
"""
Static blog generator for personal site.
Processes markdown files from blog/ folder and generates HTML pages.
"""

import argparse
from pathlib import Path

from blog_engine import BlogBuilder


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(
        description='Static blog generator for personal site'
    )
    parser.add_argument(
        'files',
        nargs='*',
        help='Specific markdown files to process (default: all in blog/)'
    )
    parser.add_argument(
        '--verbose', '-v',
        action='store_true',
        help='Verbose output'
    )
    parser.add_argument(
        '--clean',
        action='store_true',
        help='Remove generated HTML files'
    )

    args = parser.parse_args()

    # Set up paths
    source_dir = Path('blog')
    output_dir = Path('blog')
    template_dir = Path('templates')

    # Initialize builder
    builder = BlogBuilder(
        source_dir=source_dir,
        output_dir=output_dir,
        template_dir=template_dir
    )

    # Handle clean command
    if args.clean:
        count = builder.clean(verbose=args.verbose)
        if not args.verbose:
            print(f"Cleaned {count} HTML file(s)")
        return

    # Build blog
    result = builder.build(files=args.files, verbose=args.verbose)

    # Print summary
    if result.success_count > 0:
        print(f"✓ Successfully built {result.success_count} blog post(s)")

    if result.errors:
        print(f"✗ {result.error_count} error(s) occurred:")
        for error in result.errors:
            print(f"  - {error}")


if __name__ == '__main__':
    main()
