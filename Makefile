.PHONY: all install build serve clean cv typecheck lint fmt check help

UV := uv
RESUME_SOURCES := $(wildcard resume/*.tex resume/*.bib resume/*.cls resume/*.sty)

all: build

install:
	@$(UV) sync

build: install
	@$(UV) run site build

serve: install
	@$(UV) run site serve

cv: paper/resume.pdf

paper/resume.pdf: $(RESUME_SOURCES)
	@mkdir -p paper
	@cd resume && latexmk -pdf -interaction=nonstopmode -jobname=resume main.tex
	@mv resume/resume.pdf paper/resume.pdf
	@echo "built paper/resume.pdf"

clean:
	@rm -rf dist .mypy_cache .ruff_cache
	@cd resume && latexmk -C >/dev/null 2>&1 || true
	@find . -name '__pycache__' -type d -prune -exec rm -rf {} +

typecheck: install
	@$(UV) run mypy

lint: install
	@$(UV) run ruff check .

fmt: install
	@$(UV) run ruff format .
	@$(UV) run ruff check --fix .

check: typecheck lint build

help:
	@echo "Targets:"
	@echo "  install    Sync the uv environment"
	@echo "  build      Build the site into dist/"
	@echo "  serve      Run a local dev server with watch + rebuild"
	@echo "  cv         Build resume/main.tex -> paper/cv.pdf (requires latexmk)"
	@echo "  typecheck  Run mypy in strict mode"
	@echo "  lint       Run ruff checks"
	@echo "  fmt        Format with ruff and apply fixes"
	@echo "  check      Run typecheck, lint, and a strict build"
	@echo "  clean      Remove build artifacts and caches"
