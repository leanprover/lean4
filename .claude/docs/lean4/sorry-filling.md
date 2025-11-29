# Sorry Filling Reference

Quick reference for filling Lean 4 sorries systematically.

## Core Workflow

1. **Understand Context** - Read surrounding code, identify goal type
2. **Search Mathlib FIRST** - 90% of proofs already exist
3. **Generate Candidates** - 2-3 proof approaches
4. **Test Before Applying** - Use `lake build` or LSP multi_attempt
5. **Apply Working Solution** - Shortest working proof wins

## Search Strategies

**By name pattern:**
```bash
bash .claude/tools/lean4/search_mathlib.sh "continuous compact" name
```

**Multi-source smart search:**
```bash
bash .claude/tools/lean4/smart_search.sh "property description" --source=leansearch
```

**Get tactic suggestions:**
```bash
bash .claude/tools/lean4/suggest_tactics.sh --goal "∀ x : ℕ, x + 0 = x"
```

## Common Sorry Types

### Type 1: "Forgot to search mathlib" (60%)
**Solution:** Search thoroughly, apply existing lemma

### Type 2: "Just needs right tactic" (20%)
**Solution:** Try `rfl`, `simp`, `ring`, or domain automation

### Type 3: "Missing intermediate step" (15%)
**Solution:** Add `have` with connecting lemma

### Type 4: "Complex structural proof" (4%)
**Solution:** Break into sub-sorries with clear strategy

### Type 5: "Actually needs new lemma" (1%)
**Solution:** Extract as helper lemma, prove separately

## Proof Candidate Generation

**Always generate 2-3 approaches:**

**Candidate A - Direct:**
```lean
exact lemma_from_mathlib arg1 arg2
```

**Candidate B - Tactics:**
```lean
intro x
have h1 := lemma_1 x
simp [h1]
apply lemma_2
```

**Candidate C - Automation:**
```lean
simp [lemma_1, lemma_2, *]
```

## Tactic Suggestions by Goal Pattern

| Goal Pattern | Primary Tactic | Reason |
|--------------|----------------|---------|
| `⊢ a = b` | `rfl`, `simp`, `ring` | Equality |
| `⊢ ∀ x, P x` | `intro x` | Universal |
| `⊢ ∃ x, P x` | `use [term]` | Existential |
| `⊢ A → B` | `intro h` | Implication |
| `⊢ A ∧ B` | `constructor` | Conjunction |
| `⊢ A ∨ B` | `left`/`right` | Disjunction |
| `⊢ a ≤ b` | `linarith`, `omega` | Inequality |

## Testing Candidates

**With LSP server (preferred):**
```lean
mcp__lean-lsp__lean_multi_attempt(
  file = "path/to/file.lean",
  line = line_number,
  tactics = [
    "candidate_A_code",
    "candidate_B_code",
    "candidate_C_code"
  ]
)
```

**Without LSP:**
- Apply candidate
- Run `lake build`
- If fails, try next candidate

## Common Errors

**Type mismatch:**
- Add coercion: `(x : ℝ)` or `↑x`
- Try different lemma form
- Check implicit arguments

**Tactic failure:**
- Add specific lemmas: `simp [lemma1, lemma2]`
- Try manual steps instead of automation
- Check hypothesis availability

**Import missing:**
- Add import detected from search results
- Use `#check LemmaName` to verify

## Best Practices

✅ **Do:**
- Search mathlib exhaustively before proving
- Test all candidates if possible
- Use shortest working proof
- Verify with `lake build`
- Add necessary imports

❌ **Don't:**
- Skip mathlib search
- Apply without testing
- Use overly complex proofs when simple ones work
- Forget imports
- Leave sorries undocumented if you can't fill them

## When to Escalate

**Give up and escalate if:**
- All 3 candidates fail with same error
- Goal requires domain knowledge you don't have
- Needs multi-file refactoring
- Missing foundational lemmas
- Time spent > 15 minutes on single sorry

**Escalation options:**
- Break into smaller sub-sorries
- Extract as helper lemma
- Document as TODO with strategy
- Dispatch lean4-sorry-filler-deep subagent (if available)

## Output Size Limits

**For fast pass (Haiku agents):**
- Max 3 candidates per sorry
- Each diff ≤80 lines
- Total output ≤900 tokens
- If 0/3 compile, STOP and recommend escalation
