# Nous CLI Makefile
# Usage: make <target> [TOPIC="your topic"] [REGION=us]
#
# Output: Always saves to reports/json/ and reports/md/
#
# Examples:
#   make snapshot TOPIC="AI regulation"
#   make snapshot-full TOPIC="renewable energy"

# Default values
TOPIC ?= "AI agents autonomous 2025"
REGION ?= us,ue,gb
MAX_URLS ?= 20
MAX_PER_SOURCE ?= 50
RELEVANCE ?= 6
IDEA_THRESHOLD ?= 6
LLM ?= groq/llama-3.1-8b-instant
TARGET_LANGS ?= de,fr,es

# Python command (suppress import warning)
PYTHON = PYTHONPATH=.. python -W ignore::RuntimeWarning -m nous.interface.cli

# ============================================================================
# SNAPSHOT COMMANDS - Full topic analysis
# ============================================================================

# Basic snapshot (default settings, markdown output)
snapshot:
	$(PYTHON) snapshot $(TOPIC)

# Snapshot with JSON output
snapshot-json:
	$(PYTHON) snapshot $(TOPIC) --format json

# Snapshot with text output
snapshot-text:
	$(PYTHON) snapshot $(TOPIC) --format text

# Verbose snapshot
snapshot-verbose:
	$(PYTHON) snapshot $(TOPIC) --verbose

# ============================================================================
# SNAPSHOT - Source Selection
# ============================================================================

# News sources only
snapshot-news:
	$(PYTHON) snapshot $(TOPIC) --sources news

# Academic sources only
snapshot-academic:
	$(PYTHON) snapshot $(TOPIC) --sources academic

# Social sources only (Reddit, HackerNews)
snapshot-social:
	$(PYTHON) snapshot $(TOPIC) --sources social

# Web search only (DuckDuckGo)
snapshot-web:
	$(PYTHON) snapshot $(TOPIC) --sources web

# News + Academic
snapshot-news-academic:
	$(PYTHON) snapshot $(TOPIC) --sources news,academic

# All sources
snapshot-all:
	$(PYTHON) snapshot $(TOPIC) --sources news,academic,social,web

# ============================================================================
# SNAPSHOT - URL Limits
# ============================================================================

# Quick snapshot (5 URLs)
snapshot-quick:
	$(PYTHON) snapshot $(TOPIC) --max-urls 5

# Small snapshot (10 URLs)
snapshot-small:
	$(PYTHON) snapshot $(TOPIC) --max-urls 10

# Medium snapshot (20 URLs - default)
snapshot-medium:
	$(PYTHON) snapshot $(TOPIC) --max-urls 20

# Large snapshot (50 URLs)
snapshot-large:
	$(PYTHON) snapshot $(TOPIC) --max-urls 50

# Extra large snapshot (100 URLs)
snapshot-xl:
	$(PYTHON) snapshot $(TOPIC) --max-urls 100

# Custom URL limits
snapshot-custom-urls:
	$(PYTHON) snapshot $(TOPIC) --max-urls $(MAX_URLS) --max-per-source $(MAX_PER_SOURCE)

# ============================================================================
# SNAPSHOT - Region/Geolocation
# ============================================================================

# US region
snapshot-us:
	$(PYTHON) snapshot $(TOPIC) --region us

# Germany
snapshot-de:
	$(PYTHON) snapshot $(TOPIC) --region de

# France
snapshot-fr:
	$(PYTHON) snapshot $(TOPIC) --region fr

# UK
snapshot-gb:
	$(PYTHON) snapshot $(TOPIC) --region gb

# Japan
snapshot-jp:
	$(PYTHON) snapshot $(TOPIC) --region jp

# Custom region
snapshot-region:
	$(PYTHON) snapshot $(TOPIC) --region $(REGION)

# Multi-region (US + Germany + UK)
snapshot-multi-region:
	$(PYTHON) snapshot $(TOPIC) --regions us,de,gb

# ============================================================================
# SNAPSHOT - Multi-Language
# ============================================================================

# Translate to German
snapshot-translate-de:
	$(PYTHON) snapshot $(TOPIC) --translate --target-langs de

# Translate to French
snapshot-translate-fr:
	$(PYTHON) snapshot $(TOPIC) --translate --target-langs fr

# Translate to Spanish
snapshot-translate-es:
	$(PYTHON) snapshot $(TOPIC) --translate --target-langs es

# Translate to multiple languages
snapshot-translate-multi:
	$(PYTHON) snapshot $(TOPIC) --translate --target-langs $(TARGET_LANGS)

# German region + German translation
snapshot-germany:
	$(PYTHON) snapshot $(TOPIC) --region de --translate --target-langs de

# French region + French translation
snapshot-france:
	$(PYTHON) snapshot $(TOPIC) --region fr --translate --target-langs fr

# ============================================================================
# SNAPSHOT - Query Augmentation
# ============================================================================

# No query augmentation (original query only)
snapshot-no-augment:
	$(PYTHON) snapshot $(TOPIC) --no-augment

# Custom query variations (1-5)
snapshot-variations-1:
	$(PYTHON) snapshot $(TOPIC) --query-variations 1

snapshot-variations-2:
	$(PYTHON) snapshot $(TOPIC) --query-variations 2

snapshot-variations-5:
	$(PYTHON) snapshot $(TOPIC) --query-variations 5

# ============================================================================
# SNAPSHOT - Filtering Options
# ============================================================================

# No URL filtering (keep all discovered URLs)
snapshot-no-filter-urls:
	$(PYTHON) snapshot $(TOPIC) --no-filter-urls

# No idea filtering (keep all extracted ideas)
snapshot-no-filter-ideas:
	$(PYTHON) snapshot $(TOPIC) --no-filter-ideas

# No filtering at all
snapshot-no-filter:
	$(PYTHON) snapshot $(TOPIC) --no-filter-urls --no-filter-ideas

# Strict relevance (threshold 8)
snapshot-strict:
	$(PYTHON) snapshot $(TOPIC) --relevance-threshold 8 --idea-threshold 8

# Loose relevance (threshold 4)
snapshot-loose:
	$(PYTHON) snapshot $(TOPIC) --relevance-threshold 4 --idea-threshold 4

# Custom thresholds
snapshot-threshold:
	$(PYTHON) snapshot $(TOPIC) --relevance-threshold $(RELEVANCE) --idea-threshold $(IDEA_THRESHOLD)

# ============================================================================
# SNAPSHOT - Analysis Options
# ============================================================================

# No summary generation
snapshot-no-summary:
	$(PYTHON) snapshot $(TOPIC) --no-summary

# No graph building
snapshot-no-graph:
	$(PYTHON) snapshot $(TOPIC) --no-graph

# Minimal analysis (no summary, no graph)
snapshot-minimal:
	$(PYTHON) snapshot $(TOPIC) --no-summary --no-graph

# Strict consensus detection (0.8 threshold)
snapshot-strict-consensus:
	$(PYTHON) snapshot $(TOPIC) --consensus-threshold 0.8

# Loose consensus detection (0.5 threshold)
snapshot-loose-consensus:
	$(PYTHON) snapshot $(TOPIC) --consensus-threshold 0.5

# ============================================================================
# SNAPSHOT - LLM Options
# ============================================================================

# Groq Llama 3.1 8B (default, fast)
snapshot-llm-fast:
	$(PYTHON) snapshot $(TOPIC) --llm groq/llama-3.1-8b-instant

# Groq Llama 3.1 70B (better quality)
snapshot-llm-quality:
	$(PYTHON) snapshot $(TOPIC) --llm groq/llama-3.1-70b-versatile

# Custom LLM
snapshot-llm:
	$(PYTHON) snapshot $(TOPIC) --llm $(LLM)

# ============================================================================
# SNAPSHOT - Combined Presets
# ============================================================================

# Fast analysis (quick, minimal filtering)
snapshot-fast:
	$(PYTHON) snapshot $(TOPIC) --max-urls 5 --no-augment --no-filter-urls --no-graph

# Deep analysis (thorough, strict filtering)
snapshot-deep:
	$(PYTHON) snapshot $(TOPIC) --max-urls 50 --sources news,academic,social,web \
		--relevance-threshold 7 --idea-threshold 7 --query-variations 5

# Research mode (academic focus, high quality)
snapshot-research:
	$(PYTHON) snapshot $(TOPIC) --sources academic --max-urls 30 \
		--relevance-threshold 7 --llm groq/llama-3.1-70b-versatile

# News monitoring (news only, fast)
snapshot-monitor:
	$(PYTHON) snapshot $(TOPIC) --sources news --max-urls 20 --no-graph

# International research (multi-region, multi-language)
snapshot-international:
	$(PYTHON) snapshot $(TOPIC) --regions us,de,gb,fr --translate --target-langs de,fr,es \
		--sources news,academic --max-urls 30

# Full pipeline (saves to reports/json/ and reports/md/)
snapshot-full:
	$(PYTHON) snapshot $(TOPIC) --sources news,academic,social,web \
		--max-urls 30 --query-variations 4 --relevance-threshold 6 --verbose

# ============================================================================
# UTILITY TARGETS
# ============================================================================

# Show help
help:
	$(PYTHON) --help

help-snapshot:
	$(PYTHON) snapshot --help

# List all available targets
list:
	@echo "SNAPSHOT COMMANDS:"
	@echo "  snapshot              - Basic snapshot (markdown output)"
	@echo "  snapshot-json         - Snapshot with JSON output"
	@echo "  snapshot-text         - Snapshot with text output"
	@echo "  snapshot-verbose      - Verbose snapshot"
	@echo ""
	@echo "SNAPSHOT - Sources:"
	@echo "  snapshot-news         - News sources only"
	@echo "  snapshot-academic     - Academic sources only"
	@echo "  snapshot-social       - Social sources only"
	@echo "  snapshot-web          - Web search only"
	@echo "  snapshot-all          - All sources"
	@echo ""
	@echo "SNAPSHOT - URL Limits:"
	@echo "  snapshot-quick        - 5 URLs"
	@echo "  snapshot-small        - 10 URLs"
	@echo "  snapshot-medium       - 20 URLs"
	@echo "  snapshot-large        - 50 URLs"
	@echo "  snapshot-xl           - 100 URLs"
	@echo ""
	@echo "SNAPSHOT - Regions:"
	@echo "  snapshot-us/de/fr/gb/jp - Region-specific"
	@echo "  snapshot-multi-region - Multi-region"
	@echo ""
	@echo "SNAPSHOT - Languages:"
	@echo "  snapshot-translate-de/fr/es - Single language translation"
	@echo "  snapshot-translate-multi    - Multi-language translation"
	@echo "  snapshot-germany/france     - Region + translation"
	@echo ""
	@echo "SNAPSHOT - Filtering:"
	@echo "  snapshot-no-filter-urls  - No URL filtering"
	@echo "  snapshot-no-filter-ideas - No idea filtering"
	@echo "  snapshot-no-filter       - No filtering at all"
	@echo "  snapshot-strict          - Strict relevance (8)"
	@echo "  snapshot-loose           - Loose relevance (4)"
	@echo ""
	@echo "SNAPSHOT - Analysis:"
	@echo "  snapshot-no-summary      - Skip summary"
	@echo "  snapshot-no-graph        - Skip graph"
	@echo "  snapshot-minimal         - No summary or graph"
	@echo ""
	@echo "SNAPSHOT - Presets:"
	@echo "  snapshot-fast            - Quick analysis"
	@echo "  snapshot-deep            - Thorough analysis"
	@echo "  snapshot-research        - Academic focus"
	@echo "  snapshot-monitor         - News monitoring"
	@echo "  snapshot-international   - Multi-region/language"
	@echo "  snapshot-full            - Full pipeline"
	@echo ""
	@echo "VARIABLES:"
	@echo "  TOPIC=\"your topic\"      - Topic to research"
	@echo "  REGION=us               - Region code"
	@echo "  MAX_URLS=20             - Max URLs to process"
	@echo "  RELEVANCE=6             - Relevance threshold (1-10)"

.PHONY: snapshot snapshot-json snapshot-text snapshot-verbose \
	snapshot-news snapshot-academic snapshot-social snapshot-web snapshot-news-academic snapshot-all \
	snapshot-quick snapshot-small snapshot-medium snapshot-large snapshot-xl snapshot-custom-urls \
	snapshot-us snapshot-de snapshot-fr snapshot-gb snapshot-jp snapshot-region snapshot-multi-region \
	snapshot-translate-de snapshot-translate-fr snapshot-translate-es snapshot-translate-multi \
	snapshot-germany snapshot-france \
	snapshot-no-augment snapshot-variations-1 snapshot-variations-2 snapshot-variations-5 \
	snapshot-no-filter-urls snapshot-no-filter-ideas snapshot-no-filter \
	snapshot-strict snapshot-loose snapshot-threshold \
	snapshot-no-summary snapshot-no-graph snapshot-minimal \
	snapshot-strict-consensus snapshot-loose-consensus \
	snapshot-llm-fast snapshot-llm-quality snapshot-llm \
	snapshot-fast snapshot-deep snapshot-research snapshot-monitor snapshot-international snapshot-full \
	help help-snapshot list
