.PHONY: all build clean install help

# Python virtual environment directory
VENV := .venv
PYTHON := $(VENV)/bin/python3
PIP := $(VENV)/bin/pip

# Default target
all: build

# Create virtual environment if it doesn't exist
$(VENV):
	@echo "Creating virtual environment..."
	python3 -m venv $(VENV)
	@echo "Virtual environment created at $(VENV)"

# Install dependencies
install: $(VENV)
	@echo "Installing dependencies..."
	$(PIP) install -r requirements.txt
	@echo "Dependencies installed"

# Build blog (sets up env if needed)
build: install
	@echo "Building blog..."
	$(PYTHON) build_blog.py --verbose
	@echo "Blog built successfully!"

# Clean generated HTML files
clean:
	@echo "Cleaning generated files..."
	@if [ -f "$(PYTHON)" ]; then \
		$(PYTHON) build_blog.py --clean; \
	else \
		rm -f blog/*.html; \
		echo "Removed blog/*.html"; \
	fi
	@echo "Clean complete"

# Clean everything including virtual environment
clean-all: clean
	@echo "Removing virtual environment..."
	rm -rf $(VENV)
	@echo "All clean!"

# Help target
help:
	@echo "Blog Build System"
	@echo ""
	@echo "Available targets:"
	@echo "  make build      - Build the blog (sets up venv if needed)"
	@echo "  make install    - Install Python dependencies"
	@echo "  make clean      - Remove generated HTML files"
	@echo "  make clean-all  - Remove generated files and virtual environment"
	@echo "  make help       - Show this help message"
	@echo ""
	@echo "Quick start:"
	@echo "  make            - Build the blog (same as 'make build')"
