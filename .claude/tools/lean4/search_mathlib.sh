#!/usr/bin/env bash
#
# search_mathlib.sh - Find lemmas, theorems, and definitions in mathlib
#
# Usage:
#   ./search_mathlib.sh <query> [search-type]
#
# Search types:
#   name     - Search for declarations by name (default)
#   type     - Search for declarations by type signature
#   content  - Search file contents (slower but comprehensive)
#
# Examples:
#   ./search_mathlib.sh "continuous.*compact" name
#   ./search_mathlib.sh "integrable" content
#   ./search_mathlib.sh "MeasurableSpace" type

set -euo pipefail

# Configuration
MATHLIB_PATH="${MATHLIB_PATH:-.lake/packages/mathlib}"
SEARCH_TYPE="${2:-name}"
QUERY="$1"

# Detect if ripgrep is available (faster)
if command -v rg &> /dev/null; then
    USE_RG=true
else
    USE_RG=false
fi

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Verify mathlib exists
if [[ ! -d "$MATHLIB_PATH" ]]; then
    echo -e "${RED}Error: mathlib not found at $MATHLIB_PATH${NC}" >&2
    echo "Set MATHLIB_PATH environment variable or run from a Lean project root" >&2
    exit 1
fi

echo -e "${BLUE}Searching mathlib for: ${YELLOW}$QUERY${NC} (type: $SEARCH_TYPE)"
echo

case "$SEARCH_TYPE" in
    name)
        # Search for theorem/def/lemma names
        echo -e "${GREEN}Searching declaration names...${NC}"
        if [[ "$USE_RG" == true ]]; then
            rg -t lean "^(theorem|lemma|def|class|structure|inductive).*$QUERY" "$MATHLIB_PATH" -n --heading --color=always | head -60
        else
            find "$MATHLIB_PATH" -name "*.lean" -type f -exec grep -l "^\(theorem\|lemma\|def\|class\|structure\|inductive\).*$QUERY" {} \; | head -20 | while read -r file; do
                echo -e "${BLUE}File: ${NC}$file"
                grep -n "^\(theorem\|lemma\|def\|class\|structure\|inductive\).*$QUERY" "$file" | head -3
                echo
            done
        fi
        ;;

    type)
        # Search in type signatures
        echo -e "${GREEN}Searching type signatures...${NC}"
        if [[ "$USE_RG" == true ]]; then
            rg -t lean ": .*$QUERY" "$MATHLIB_PATH" -n --heading --color=always | head -60
        else
            find "$MATHLIB_PATH" -name "*.lean" -type f -exec grep -l ": .*$QUERY" {} \; | head -20 | while read -r file; do
                echo -e "${BLUE}File: ${NC}$file"
                grep -n "theorem\|lemma\|def" "$file" | grep "$QUERY" | head -3
                echo
            done
        fi
        ;;

    content)
        # Search file contents (comprehensive but slower)
        echo -e "${GREEN}Searching file contents...${NC}"
        if [[ "$USE_RG" == true ]]; then
            rg -t lean "$QUERY" "$MATHLIB_PATH" -n --heading --color=always | head -100
        else
            find "$MATHLIB_PATH" -name "*.lean" -type f -exec grep -l "$QUERY" {} \; | head -20 | while read -r file; do
                echo -e "${BLUE}File: ${NC}$file"
                grep -n "$QUERY" "$file" | head -5
                echo
            done
        fi
        ;;

    *)
        echo -e "${RED}Unknown search type: $SEARCH_TYPE${NC}" >&2
        echo "Valid types: name, type, content" >&2
        exit 1
        ;;
esac

echo -e "${YELLOW}Tip: Import the file with:${NC}"
echo -e "  import Mathlib.Path.To.File"
echo
echo -e "${YELLOW}Tip: Check declaration with:${NC}"
echo -e "  #check declarationName"
