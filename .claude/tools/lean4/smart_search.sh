#!/usr/bin/env bash
#
# smart_search.sh - Enhanced Lean theorem search with API integration
#
# Usage:
#   ./smart_search.sh <query> [--source=leansearch|loogle|mathlib|all]
#
# Searches for Lean theorems using multiple sources:
#   - leansearch: Natural language and semantic search (leansearch.net)
#   - loogle: Type-based search (loogle.lean-lang.org)
#   - mathlib: Local ripgrep/grep search (fast, no rate limits)
#   - all: Try all sources (respects rate limits)
#
# Rate limits:
#   - LeanSearch: ~3 requests per 30 seconds
#   - Loogle: ~3 requests per 30 seconds
#
# Examples:
#   ./smart_search.sh "If there exist injective maps from A to B and B to A, then there exists a bijection"
#   ./smart_search.sh "continuous" --source=mathlib
#   ./smart_search.sh "(?a -> ?b) -> List ?a -> List ?b" --source=loogle
#   ./smart_search.sh "Cauchy Schwarz" --source=all

set -euo pipefail

# Configuration
QUERY="${1:-}"
SOURCE="mathlib"  # Default to mathlib (no rate limits)
MATHLIB_PATH="${MATHLIB_PATH:-.lake/packages/mathlib}"

# Parse source option
for arg in "$@"; do
    if [[ "$arg" == --source=* ]]; then
        SOURCE="${arg#--source=}"
    fi
done

# Detect if ripgrep is available
if command -v rg &> /dev/null; then
    USE_RG=true
else
    USE_RG=false
fi

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m'

# Validate input
if [[ -z "$QUERY" ]]; then
    echo -e "${RED}Error: No query specified${NC}" >&2
    echo "Usage: $0 <query> [--source=leansearch|loogle|mathlib|all]" >&2
    exit 1
fi

# Check for curl
if [[ "$SOURCE" == "leansearch" || "$SOURCE" == "loogle" || "$SOURCE" == "all" ]]; then
    if ! command -v curl &> /dev/null; then
        echo -e "${RED}Error: curl is required for API searches${NC}" >&2
        echo "Install curl or use --source=mathlib" >&2
        exit 1
    fi
fi

# LeanSearch API
search_leansearch() {
    echo -e "${CYAN}━━━ LeanSearch (semantic search) ━━━${NC}"
    echo -e "${YELLOW}Query: $QUERY${NC}"
    echo

    # URL encode the query
    ENCODED=$(printf '%s' "$QUERY" | jq -sRr @uri)

    # Call API
    RESPONSE=$(curl -s "https://leansearch.net/api/search?query=$ENCODED&num_results=5" || echo "ERROR")

    if [[ "$RESPONSE" == "ERROR" || "$RESPONSE" == "" ]]; then
        echo -e "${RED}Error: LeanSearch API request failed${NC}"
        echo -e "${YELLOW}Note: Rate limit may be exceeded (3 req/30s)${NC}"
        return 1
    fi

    # Parse JSON response
    if command -v jq &> /dev/null; then
        echo "$RESPONSE" | jq -r '.results[] | "[\(.score | tonumber | round)] \(.name)\n  \(.type)\n  \(.module)\n"' || echo "$RESPONSE"
    else
        echo "$RESPONSE"
        echo
        echo -e "${YELLOW}Tip: Install jq for formatted output${NC}"
    fi
}

# Loogle API
search_loogle() {
    echo -e "${CYAN}━━━ Loogle (type-based search) ━━━${NC}"
    echo -e "${YELLOW}Query: $QUERY${NC}"
    echo

    # URL encode the query
    ENCODED=$(printf '%s' "$QUERY" | jq -sRr @uri)

    # Call API
    RESPONSE=$(curl -s "https://loogle.lean-lang.org/json?q=$ENCODED" || echo "ERROR")

    if [[ "$RESPONSE" == "ERROR" || "$RESPONSE" == "" ]]; then
        echo -e "${RED}Error: Loogle API request failed${NC}"
        echo -e "${YELLOW}Note: Rate limit may be exceeded (3 req/30s)${NC}"
        return 1
    fi

    # Parse JSON response
    if command -v jq &> /dev/null; then
        echo "$RESPONSE" | jq -r '.results[0:8][] | "\(.name)\n  Type: \(.type)\n  Module: \(.module)\n"' || echo "$RESPONSE"
    else
        echo "$RESPONSE"
        echo
        echo -e "${YELLOW}Tip: Install jq for formatted output${NC}"
    fi
}

# Local mathlib search
search_mathlib() {
    echo -e "${CYAN}━━━ Mathlib (local search) ━━━${NC}"
    echo -e "${YELLOW}Query: $QUERY${NC}"
    echo

    if [[ ! -d "$MATHLIB_PATH" ]]; then
        echo -e "${RED}Error: mathlib not found at $MATHLIB_PATH${NC}" >&2
        return 1
    fi

    echo -e "${GREEN}Searching declaration names:${NC}"
    if [[ "$USE_RG" == true ]]; then
        rg -t lean "^(theorem|lemma|def).*$QUERY" "$MATHLIB_PATH" -n --heading --color=always | head -30
    else
        find "$MATHLIB_PATH" -name "*.lean" -type f -exec grep -l "^\\(theorem\\|lemma\\|def\\).*$QUERY" {} \; | head -10 | while read -r file; do
            echo -e "${BLUE}File: ${NC}$file"
            grep -n "^\\(theorem\\|lemma\\|def\\).*$QUERY" "$file" | head -2
            echo
        done
    fi
}

# Execute search based on source
case "$SOURCE" in
    leansearch)
        search_leansearch
        ;;

    loogle)
        search_loogle
        ;;

    mathlib)
        search_mathlib
        ;;

    all)
        echo -e "${BLUE}Running multi-source search...${NC}"
        echo -e "${YELLOW}Note: API sources have rate limits (3 req/30s each)${NC}"
        echo

        # Try mathlib first (no rate limit)
        search_mathlib
        echo

        # Then try APIs with warnings
        echo -e "${YELLOW}Trying LeanSearch API (may hit rate limit)...${NC}"
        search_leansearch || true
        echo

        echo -e "${YELLOW}Trying Loogle API (may hit rate limit)...${NC}"
        search_loogle || true
        ;;

    *)
        echo -e "${RED}Error: Invalid source: $SOURCE${NC}" >&2
        echo "Valid sources: leansearch, loogle, mathlib, all" >&2
        exit 1
        ;;
esac

echo
echo -e "${YELLOW}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
echo -e "${YELLOW}Tips:${NC}"
echo "  • Import: import Mathlib.Path.To.File"
echo "  • Check: #check theoremName"
echo "  • Search patterns:"
echo "    - Natural language: \"continuous functions on compact spaces\""
echo "    - Type pattern: \"(?a -> ?b) -> List ?a -> List ?b\""
echo "    - Identifier: \"List.sum\" or \"continuous\""
