#!/usr/bin/env bash
#
# check_axioms.sh - Check axioms used in Lean 4 theorems and lemmas
#
# Usage:
#   ./check_axioms.sh <file-or-directory> [--verbose]
#
# This script extracts all theorem/lemma declarations and generates a Lean file
# that checks axioms for each one. Standard mathlib axioms (propext, quot.sound, choice)
# are filtered out, highlighting only custom axioms or unexpected dependencies.
#
# LIMITATION: Only works for declarations that are part of the module's public API.
# Declarations in namespaces, sections, or marked 'private' cannot be checked via
# external import. For those, use #print axioms directly in your Lean files.
#
# Examples:
#   ./check_axioms.sh MyFile.lean
#   ./check_axioms.sh src/DeFinetti/ --verbose
#   ./check_axioms.sh . --verbose  # Check entire project

set -euo pipefail

# Configuration
TARGET="${1:-.}"
VERBOSE="${2:-}"
TEMP_FILE=$(mktemp)

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Standard acceptable axioms
STANDARD_AXIOMS="propext|quot.sound|Classical.choice|Quot.sound"

echo -e "${BLUE}Checking axioms in: ${YELLOW}$TARGET${NC}"
echo

# Find all Lean files
if [[ -f "$TARGET" ]]; then
    FILES=("$TARGET")
elif [[ -d "$TARGET" ]]; then
    mapfile -t FILES < <(find "$TARGET" -name "*.lean" -type f)
else
    echo -e "${RED}Error: $TARGET is not a file or directory${NC}" >&2
    exit 1
fi

# Extract declarations from each file
DECLARATIONS=()
for file in "${FILES[@]}"; do
    # Extract theorem and lemma names (using egrep for compatibility)
    while IFS= read -r line; do
        # Extract the declaration name from lines like "theorem name ..."
        decl=$(echo "$line" | sed -E 's/^(theorem|lemma|def) +([^ :(]+).*/\2/')
        if [[ -n "$decl" ]]; then
            DECLARATIONS+=("$file:$decl")
        fi
    done < <(grep -E '^(theorem|lemma|def) ' "$file" 2>/dev/null || true)
done

if [[ ${#DECLARATIONS[@]} -eq 0 ]]; then
    echo -e "${YELLOW}No theorems or lemmas found${NC}"
    exit 0
fi

echo -e "${GREEN}Found ${#DECLARATIONS[@]} declarations${NC}"
echo

# Generate temporary Lean file to check axioms
echo "-- Auto-generated axiom check file" > "$TEMP_FILE"
echo "" >> "$TEMP_FILE"

# Group by file for proper imports (bash 3.2 compatible)
SEEN_FILES=()
for entry in "${DECLARATIONS[@]}"; do
    file="${entry%%:*}"

    # Check if we've seen this file before
    already_seen=false
    for seen in ${SEEN_FILES[@]+"${SEEN_FILES[@]}"}; do
        if [[ "$seen" == "$file" ]]; then
            already_seen=true
            break
        fi
    done

    if [[ "$already_seen" == false ]]; then
        SEEN_FILES+=("$file")
        # Convert file path to module name
        module=$(echo "$file" | sed 's|^./||' | sed 's|/|.|g' | sed 's|\.lean$||')
        echo "import $module" >> "$TEMP_FILE"
    fi
done

echo "" >> "$TEMP_FILE"

# Add #print axioms commands
for entry in "${DECLARATIONS[@]}"; do
    decl="${entry##*:}"
    echo "#print axioms $decl" >> "$TEMP_FILE"
done

# Run Lean to check axioms
echo -e "${BLUE}Running axiom analysis...${NC}"
if OUTPUT=$(lake env lean "$TEMP_FILE" 2>&1); then
    # Parse output
    CURRENT_DECL=""
    HAS_CUSTOM=false

    while IFS= read -r line; do
        if [[ "$line" =~ ^([a-zA-Z0-9_]+)\ depends\ on\ axioms: ]]; then
            CURRENT_DECL="${BASH_REMATCH[1]}"
            if [[ "$VERBOSE" == "--verbose" ]]; then
                echo -e "${BLUE}$CURRENT_DECL:${NC}"
            fi
        elif [[ "$line" =~ ^([a-zA-Z0-9_.]+)$ ]]; then
            axiom="${BASH_REMATCH[1]}"
            if [[ ! "$axiom" =~ $STANDARD_AXIOMS ]]; then
                echo -e "${RED}⚠ $CURRENT_DECL uses non-standard axiom: $axiom${NC}"
                HAS_CUSTOM=true
            elif [[ "$VERBOSE" == "--verbose" ]]; then
                echo -e "  ${GREEN}✓${NC} $axiom (standard)"
            fi
        fi
    done <<< "$OUTPUT"

    if [[ "$HAS_CUSTOM" == false ]]; then
        echo -e "${GREEN}✓ All declarations use only standard axioms${NC}"
    fi
else
    echo -e "${RED}Error running Lean:${NC}" >&2
    echo "$OUTPUT" >&2
    rm -f "$TEMP_FILE"
    exit 1
fi

# Cleanup
rm -f "$TEMP_FILE"

echo
echo -e "${YELLOW}Standard axioms (acceptable):${NC}"
echo "  • propext (propositional extensionality)"
echo "  • quot.sound (quotient soundness)"
echo "  • Classical.choice (axiom of choice)"
echo
echo -e "${YELLOW}Tip: Any other axioms should have elimination plans${NC}"
