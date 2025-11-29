#!/usr/bin/env bash
#
# suggest_tactics.sh - Suggest Lean 4 tactics based on goal type
#
# Usage:
#   ./suggest_tactics.sh <file> <line> [column]
#   ./suggest_tactics.sh --goal "<goal-text>"
#
# Analyzes a proof goal and suggests relevant tactics to try.
#
# Two modes:
#   1. File mode: Extract goal from file at line/column
#   2. Direct mode: Analyze provided goal text
#
# Examples:
#   ./suggest_tactics.sh MyFile.lean 42
#   ./suggest_tactics.sh MyFile.lean 42 15
#   ./suggest_tactics.sh --goal "⊢ a = b"
#   ./suggest_tactics.sh --goal "⊢ ∀ n : ℕ, n + 0 = n"
#
# Features:
#   - Pattern matching on goal structure
#   - Domain-specific suggestions (measure theory, algebra, etc.)
#   - Tactic explanations and examples
#   - Works with or without MCP server

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
MAGENTA='\033[0;35m'
BOLD='\033[1m'
NC='\033[0m'

# Mode detection
MODE="file"
GOAL_TEXT=""

if [[ "${1:-}" == "--goal" ]]; then
    MODE="direct"
    GOAL_TEXT="${2:-}"
    if [[ -z "$GOAL_TEXT" ]]; then
        echo -e "${RED}Error: --goal requires goal text${NC}" >&2
        exit 1
    fi
else
    FILE="${1:-}"
    LINE="${2:-}"
    COLUMN="${3:-}"

    if [[ -z "$FILE" ]] || [[ -z "$LINE" ]]; then
        echo "Usage: $0 <file> <line> [column]" >&2
        echo "   or: $0 --goal \"<goal-text>\"" >&2
        exit 1
    fi

    if [[ ! -f "$FILE" ]]; then
        echo -e "${RED}Error: File '$FILE' not found${NC}" >&2
        exit 1
    fi
fi

# Function to get goal from file (requires lake env lean or MCP)
get_goal_from_file() {
    local file="$1"
    local line="$2"
    local column="${3:-1}"

    # Try using lake env lean to get goal state
    # This is a simplified approach - full implementation would use LSP
    echo -e "${YELLOW}Note: Goal extraction from file requires LSP integration${NC}" >&2
    echo -e "${YELLOW}For best results, use --goal with goal text from your editor${NC}" >&2

    # Extract surrounding code as fallback
    local context=$(sed -n "$((line-5)),$((line+5))p" "$file")
    echo -e "${BLUE}Context around line $line:${NC}" >&2
    echo "$context" >&2
    echo "" >&2

    # Prompt user to provide goal
    echo -e "${YELLOW}Please run this script with --goal and paste the goal:${NC}" >&2
    echo -e "${YELLOW}  $0 --goal \"⊢ your goal here\"${NC}" >&2
    exit 1
}

# Extract goal if in file mode
if [[ "$MODE" == "file" ]]; then
    get_goal_from_file "$FILE" "$LINE" "$COLUMN"
fi

# Analyze goal and suggest tactics
analyze_goal() {
    local goal="$1"

    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${CYAN}${BOLD}GOAL ANALYSIS${NC}"
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""
    echo -e "${BOLD}Goal:${NC} $goal"
    echo ""

    # Extract goal conclusion (after ⊢)
    local conclusion=""
    if [[ "$goal" =~ ⊢[[:space:]]*(.*) ]]; then
        conclusion="${BASH_REMATCH[1]}"
    else
        conclusion="$goal"
    fi

    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${CYAN}${BOLD}SUGGESTED TACTICS${NC}"
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""

    local suggestions_made=false

    # Pattern: Equality (a = b)
    if [[ "$conclusion" =~ [[:space:]]*([^[:space:]]+)[[:space:]]*=[[:space:]]*([^[:space:]]+) ]]; then
        suggestions_made=true
        echo -e "${GREEN}${BOLD}Detected: EQUALITY${NC} ${BLUE}(a = b)${NC}"
        echo ""
        echo -e "${YELLOW}Primary tactics:${NC}"
        echo "  • ${BOLD}rfl${NC} - If both sides are definitionally equal"
        echo "  • ${BOLD}simp${NC} or ${BOLD}simp only [...]${NC} - Simplify using simp lemmas"
        echo "  • ${BOLD}ring${NC} - For polynomial/ring equalities"
        echo "  • ${BOLD}field_simp${NC} - For field equalities with division"
        echo "  • ${BOLD}ext${NC} / ${BOLD}funext${NC} - For function equality (prove pointwise)"
        echo ""
        echo -e "${YELLOW}Rewriting:${NC}"
        echo "  • ${BOLD}rw [lemma]${NC} - Rewrite left-to-right"
        echo "  • ${BOLD}rw [← lemma]${NC} - Rewrite right-to-left"
        echo ""
    fi

    # Pattern: Universal quantifier (∀)
    if [[ "$conclusion" =~ ∀ ]]; then
        suggestions_made=true
        echo -e "${GREEN}${BOLD}Detected: UNIVERSAL QUANTIFIER${NC} ${BLUE}(∀ x, P x)${NC}"
        echo ""
        echo "  • ${BOLD}intro${NC} or ${BOLD}intros${NC} - Introduce variable(s)"
        echo "  • ${BOLD}intro x${NC} - Introduce with specific name"
        echo ""
    fi

    # Pattern: Existential quantifier (∃)
    if [[ "$conclusion" =~ ∃ ]]; then
        suggestions_made=true
        echo -e "${GREEN}${BOLD}Detected: EXISTENTIAL QUANTIFIER${NC} ${BLUE}(∃ x, P x)${NC}"
        echo ""
        echo "  • ${BOLD}use x${NC} - Provide witness"
        echo "  • ${BOLD}refine ⟨x, ?_⟩${NC} - Provide witness, leave proof as goal"
        echo "  • ${BOLD}constructor${NC} - Split into witness and proof goals"
        echo ""
    fi

    # Pattern: Implication (→)
    if [[ "$conclusion" =~ →|⇒ ]]; then
        suggestions_made=true
        echo -e "${GREEN}${BOLD}Detected: IMPLICATION${NC} ${BLUE}(P → Q)${NC}"
        echo ""
        echo "  • ${BOLD}intro h${NC} - Assume hypothesis"
        echo "  • ${BOLD}intros${NC} - Introduce multiple hypotheses"
        echo ""
    fi

    # Pattern: Conjunction (∧)
    if [[ "$conclusion" =~ ∧ ]]; then
        suggestions_made=true
        echo -e "${GREEN}${BOLD}Detected: CONJUNCTION${NC} ${BLUE}(P ∧ Q)${NC}"
        echo ""
        echo "  • ${BOLD}constructor${NC} - Split into two goals"
        echo "  • ${BOLD}refine ⟨?_, ?_⟩${NC} - Structured proof"
        echo "  • ${BOLD}exact ⟨proof1, proof2⟩${NC} - Direct proof (if you have both)"
        echo ""
    fi

    # Pattern: Disjunction (∨)
    if [[ "$conclusion" =~ ∨ ]]; then
        suggestions_made=true
        echo -e "${GREEN}${BOLD}Detected: DISJUNCTION${NC} ${BLUE}(P ∨ Q)${NC}"
        echo ""
        echo "  • ${BOLD}left${NC} - Prove left side"
        echo "  • ${BOLD}right${NC} - Prove right side"
        echo "  • ${BOLD}by_cases h : P${NC} - Split on decidable proposition"
        echo ""
    fi

    # Pattern: Inequality (<, ≤, >, ≥)
    if [[ "$conclusion" == *"<"* ]] || [[ "$conclusion" == *"≤"* ]] || [[ "$conclusion" == *">"* ]] || [[ "$conclusion" == *"≥"* ]]; then
        suggestions_made=true
        echo -e "${GREEN}${BOLD}Detected: INEQUALITY${NC} ${BLUE}(a < b, a ≤ b, etc.)${NC}"
        echo ""
        echo "  • ${BOLD}linarith${NC} - Linear arithmetic solver"
        echo "  • ${BOLD}omega${NC} - Integer linear arithmetic"
        echo "  • ${BOLD}positivity${NC} - Prove positivity"
        echo "  • ${BOLD}gcongr${NC} - Goal congruence (monotonicity)"
        echo "  • ${BOLD}calc${NC} - Chain of inequalities"
        echo ""
    fi

    # Domain: Measure theory
    if [[ "$conclusion" =~ (Measure|measure|Measurable|μ|∫|Integrable|AEMeasurable|MeasurableSet) ]]; then
        suggestions_made=true
        echo -e "${MAGENTA}${BOLD}Domain: MEASURE THEORY${NC}"
        echo ""
        echo "  • ${BOLD}measurability${NC} - Solve measurability goals"
        echo "  • ${BOLD}filter_upwards${NC} - Work with a.e. properties"
        echo "  • ${BOLD}ae_of_all${NC} - Lift pointwise to a.e."
        echo "  • ${BOLD}setIntegral_congr_ae${NC} - Integral equality via a.e. equality"
        echo ""
    fi

    # Domain: Probability
    if [[ "$conclusion" =~ (IsProbabilityMeasure|probability|condExp) ]]; then
        suggestions_made=true
        echo -e "${MAGENTA}${BOLD}Domain: PROBABILITY THEORY${NC}"
        echo ""
        echo "  • ${BOLD}haveI : IsProbabilityMeasure μ := ...${NC} - Provide instance"
        echo "  • ${BOLD}apply condExp_unique${NC} - Conditional expectation uniqueness"
        echo "  • ${BOLD}measurability${NC} - Check measurability"
        echo ""
    fi

    # Domain: Topology/Analysis
    if [[ "$conclusion" =~ (Continuous|continuous|IsOpen|IsClosed|Tendsto|Filter) ]]; then
        suggestions_made=true
        echo -e "${MAGENTA}${BOLD}Domain: TOPOLOGY/ANALYSIS${NC}"
        echo ""
        echo "  • ${BOLD}continuity${NC} - Prove continuity goals"
        echo "  • ${BOLD}fun_prop${NC} - Function property automation"
        echo "  • ${BOLD}apply Continuous.comp${NC} - Composition of continuous functions"
        echo ""
    fi

    # Domain: Algebra
    if [[ "$conclusion" =~ (Group|Ring|Field|Monoid|comm|mul|add) ]]; then
        suggestions_made=true
        echo -e "${MAGENTA}${BOLD}Domain: ALGEBRA${NC}"
        echo ""
        echo "  • ${BOLD}ring${NC} - Ring equality"
        echo "  • ${BOLD}field_simp${NC} - Simplify field expressions"
        echo "  • ${BOLD}group${NC} - Group equality"
        echo "  • ${BOLD}abel${NC} - Abelian group equality"
        echo ""
    fi

    # General tactics
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${CYAN}${BOLD}GENERAL TACTICS (always worth trying)${NC}"
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""
    echo -e "${YELLOW}Automation:${NC}"
    echo "  • ${BOLD}simp${NC} / ${BOLD}simp only [...]${NC} - Simplification"
    echo "  • ${BOLD}aesop${NC} - Automated proof search"
    echo "  • ${BOLD}decide${NC} - Decision procedure (for decidable goals)"
    echo ""
    echo -e "${YELLOW}Structuring:${NC}"
    echo "  • ${BOLD}have h : ... := ...${NC} - Introduce intermediate result"
    echo "  • ${BOLD}suffices h : ... by ...${NC} - Backwards reasoning"
    echo "  • ${BOLD}refine ?_${NC} - Placeholder for goal refinement"
    echo ""
    echo -e "${YELLOW}Hypothesis work:${NC}"
    echo "  • ${BOLD}rcases h with ⟨x, hx⟩${NC} - Destructure ∃ or ∧"
    echo "  • ${BOLD}obtain ⟨x, hx⟩ := h${NC} - Destructure and name"
    echo "  • ${BOLD}cases h${NC} - Case split on h"
    echo ""
    echo -e "${YELLOW}Application:${NC}"
    echo "  • ${BOLD}apply lemma${NC} - Apply lemma, leaving subgoals"
    echo "  • ${BOLD}exact term${NC} - Provide exact proof term"
    echo "  • ${BOLD}assumption${NC} - Use existing hypothesis"
    echo ""

    if [[ "$suggestions_made" == false ]]; then
        echo -e "${YELLOW}No specific patterns detected.${NC}"
        echo "The general tactics above are your best starting point."
        echo ""
    fi

    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${CYAN}${BOLD}WORKFLOW TIPS${NC}"
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo ""
    echo "1. ${BOLD}Try automation first${NC}: simp, aesop, ring, linarith"
    echo "2. ${BOLD}Introduce/destruct${NC}: intro, rcases, cases"
    echo "3. ${BOLD}Break it down${NC}: have, suffices, intermediate lemmas"
    echo "4. ${BOLD}Search mathlib${NC}: Use smart_search.sh or #check"
    echo "5. ${BOLD}Check types${NC}: Use #check to understand terms"
    echo ""
}

# Run analysis
analyze_goal "$GOAL_TEXT"
