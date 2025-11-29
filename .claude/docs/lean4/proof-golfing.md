# Proof Golfing: Simplifying Proofs After Compilation

## TLDR

**Core principle:** First make it compile, then make it clean.

**When to use:** After `lake build` succeeds on stable files. Expected 30-40% reduction with proper safety filtering.

**When NOT to use:** Active development, already-optimized code (mathlib-quality), or missing verification tools (93% false positive rate without them).

**Critical:** MUST verify let binding usage before inlining. Bindings used ≥3 times should NOT be inlined (would increase code size).

## Quick Reference: Pattern Priority

**TLDR:** Apply patterns top-to-bottom. ⭐⭐⭐⭐⭐ = instant wins (zero/low risk, high ROI). ⭐⭐⭐⭐ = quick with testing. ⭐⭐⭐ = good but situational. ⭐⭐ = diminishing returns.

**Benefits:** Directness (term > tactic), Clarity (readability), Conciseness (shorter), Simplicity (less complex), Performance (faster), Safety (prevents errors), Reusability (eliminates duplication), Quality (linting).

| Pattern | Savings | Risk | Priority | Benefit | Notes |
|---------|---------|------|----------|---------|-------|
| **Linter-guided simp cleanup** | **2 lines** | **Zero** | **⭐⭐⭐⭐⭐** | **Performance** | **Remove unused simp args** |
| **`by rfl` → `rfl`** | **1 line** | **Zero** | **⭐⭐⭐⭐⭐** | **Directness** | **Term mode for theorems** |
| **`rw; simp_rw` → `rw; simpa`** | **1 line** | **Zero** | **⭐⭐⭐⭐⭐** | **Simplicity** | **Binder-aware simplification** |
| **Eta-reduction `fun x => f x` → `f`** | **Tokens** | **Zero** | **⭐⭐⭐⭐⭐** | **Simplicity** | **Remove redundant lambda** |
| **`.mpr` over `rwa` for trivial** | **1 line** | **Zero** | **⭐⭐⭐⭐⭐** | **Directness** | **Direct term application** |
| `rw; exact` → `rwa` | 50% | Zero | ⭐⭐⭐⭐⭐ | Directness | Always safe, instant |
| `ext + rfl` → `rfl` | 67% | Low | ⭐⭐⭐⭐⭐ | Directness | Test first, revert if fails |
| **intro-dsimp-exact → lambda** | **75%** | **Low** | **⭐⭐⭐⭐⭐** | **Directness** | **Tactic → term mode** |
| **Extract repeated tactic patterns to helpers** | **40%** | **Low** | **⭐⭐⭐⭐⭐** | **Reusability** | **Single helper for pattern** |
| let+have+exact inline | 60-80% | HIGH | ⭐⭐⭐⭐⭐ | Conciseness | MUST verify usage ≤2x |
| **Transport ▸ for rewrites** | **1-2 lines** | **Zero** | **⭐⭐⭐⭐⭐** | **Conciseness** | **Term-mode rewrite** |
| **Single-use `have` inline (general)** | **30-50%** | **Low** | **⭐⭐⭐⭐** | **Clarity** | **Beyond calc blocks** |
| **Inline single-use definitions** | **3-4 lines** | **Low** | **⭐⭐⭐⭐** | **Clarity** | **Used exactly once** |
| **Multi-pattern match** | **7 lines** | **Low** | **⭐⭐⭐⭐** | **Simplicity** | **`\| 0 \| 1 \| 2 => ...`** |
| **Successor pattern (n+k)** | **25 lines** | **Low** | **⭐⭐⭐⭐** | **Clarity** | **`\| n+3 =>` for ranges** |
| **Remove redundant `show` wrappers** | **50-75%** | **Low** | **⭐⭐⭐⭐** | **Simplicity** | **`simp` handles it** |
| **Convert-based helper inlining** | **30-40%** | **Medium** | **⭐⭐⭐⭐** | **Directness** | **`convert ... using N`** |
| Redundant `ext` before `simp` | 50% | Medium | ⭐⭐⭐⭐ | Simplicity | Not all ext is redundant |
| `congr; ext; rw` → `simp only` | 67% | Medium | ⭐⭐⭐⭐ | Simplicity | simp is smarter than you think |
| **`simpa using` → `exact`** | **1 token** | **Zero** | **⭐⭐⭐** | **Clarity** | **When `simp` does nothing** |
| **Unused lambda variables cleanup** | **0 lines** | **Zero** | **⭐⭐⭐** | **Quality** | **Eliminates linter warnings** |
| **Inline omega for trivial arithmetic** | **2 lines** | **Zero** | **⭐⭐⭐** | **Conciseness** | **`by omega` inline** |
| **Symmetric cases with `<;>`** | **11 lines** | **Low** | **⭐⭐⭐** | **Conciseness** | **`rcases ... <;>` when identical** |
| **match after ext** | **3 lines** | **Low** | **⭐⭐⭐** | **Clarity** | **Direct match vs cases** |
| **calc with rfl for definitions** | **Clarity** | **Zero** | **⭐⭐⭐** | **Performance** | **Faster than proof search** |
| **refine with ?_ for term construction** | **Structure** | **Low** | **⭐⭐⭐** | **Clarity** | **Explicit construction** |
| **Named arguments in obtain** | **0 lines** | **Zero** | **⭐⭐⭐** | **Safety** | **Prevents type errors** |
| Smart `ext` (nested) | 50% | Low | ⭐⭐⭐ | Simplicity | ext handles multiple layers |
| `simp` closes goals directly | 67% | Low | ⭐⭐⭐ | Simplicity | Remove explicit `exact` |
| have-calc single-use inline | 50% | Low | ⭐⭐⭐ | Clarity | Only if used once in calc |
| **Remove duplicate inline comments** | **Lines** | **Zero** | **⭐⭐** | **Clarity** | **If docstring is complete** |
| ext-simp chain combination | Variable | Medium | ⭐⭐ | Conciseness | Only when saves ≥2 lines |
| Arithmetic with automation | 30-50% | Medium | ⭐⭐ | Simplicity | Direct lemmas often better |

**New patterns in bold** - discovered from real-world optimization sessions.

**ROI Strategy:** Do ⭐⭐⭐⭐⭐ first (instant wins), then ⭐⭐⭐⭐ (quick with testing), skip ⭐-⭐⭐ if time-limited.

## Critical Safety Warnings

### The 93% False Positive Problem

**Key finding:** Without proper analysis, 93% of "optimization opportunities" are false positives that make code WORSE.

**The Multiple-Use Heuristic:**
- Bindings used 1-2 times: Safe to inline
- Bindings used 3-4 times: 40% worth optimizing (check carefully)
- Bindings used 5+ times: NEVER inline (would increase size 2-4×)

**Example - DON'T optimize:**
```lean
let μ_map := Measure.map (fun ω i => X (k i) ω) μ  -- 20 tokens
-- Used 7 times in proof
-- Current: 20 + (2 × 7) = 34 tokens
-- Inlined: 20 × 7 = 140 tokens (4× WORSE!)
```

### When NOT to Optimize

**Skip if ANY of these:**
- ❌ Let binding used ≥3 times
- ❌ Complex proof with case analysis
- ❌ Semantic naming aids understanding
- ❌ Would create deeply nested lambdas (>2 levels)
- ❌ Readability Cost = (nesting depth) × (complexity) × (repetition) > 5

### Saturation Indicators

**Stop when:**
- ✋ Optimization success rate < 20%
- ✋ Time per optimization > 15 minutes
- ✋ Most patterns are false positives
- ✋ Debating whether 2-token savings is worth it

**Benchmark:** Well-maintained codebases reach saturation after ~20-25 optimizations.

## High-Priority Patterns (⭐⭐⭐⭐⭐)

### Pattern -1: Linter-Guided simp Cleanup (Performance)

```lean
-- Before (linter warns: unused)
simp only [decide_eq_false_iff_not, decide_eq_true_eq]
-- After
simp only [decide_eq_true_eq]
```

Remove unused `simp` arguments flagged by linter. Zero risk (compiler-verified), faster elaboration. Trust the linter - always safe to remove.

### Pattern 0: `by rfl` → `rfl` (Directness)

```lean
-- Before
theorem tiling_count : allTilings.length = 11 := by rfl
-- After
theorem tiling_count : allTilings.length = 11 := rfl

-- Before
theorem count : a = 9 ∧ b = 2 := by constructor <;> rfl
-- After
theorem count : a = 9 ∧ b = 2 := ⟨rfl, rfl⟩
```

Term mode for definitional equalities. Use `⟨_, _⟩` instead of `constructor <;> rfl`. Zero risk.

### Pattern 1: `rw; exact` → `rwa`

```lean
-- Before
rw [h1, h2] at h; exact h
-- After
rwa [h1, h2] at h
```

Standard mathlib idiom. `rwa` = "rewrite and assumption". Zero risk, always works.

### Pattern 2: `ext + rfl` → `rfl`

```lean
-- Before
have h : f = g := by ext x; rfl
-- After
have h : f = g := rfl
```

When terms are definitionally equal, `rfl` suffices. Low risk - test with build, revert if fails. Not all `ext + rfl` simplify!

### Pattern 2A: `rw; simp_rw` → `rw; simpa` (Simplicity)

```lean
-- Before
have h := this.interior_compl
rw [compl_iInter] at h
simp_rw [compl_compl] at h
exact h
-- After
have h := this.interior_compl
rw [compl_iInter] at h
simpa [compl_compl] using h
```

Use `simpa` for binder-aware simplification. `simpa` penetrates binders (inside unions/intersections) that `rw` cannot. Zero risk.

### Pattern 2B: Eta-Reduction (Simplicity)

```lean
-- Before
eq_empty_iff_forall_notMem.mpr (fun x hx => hU_sub_int hx)
-- After
eq_empty_iff_forall_notMem.mpr hU_sub_int
```

Pattern: `fun x => f x` is just `f`. Lean's eta-reduction eliminates unnecessary lambda abstraction. Zero risk.

### Pattern 2C: Direct `.mpr`/`.mp` (Directness)

```lean
-- Before
have h : U.Nonempty := by rwa [nonempty_iff_ne_empty]
-- After
have h : U.Nonempty := nonempty_iff_ne_empty.mpr h_ne
```

When `rwa` does trivial work (just `.mp` or `.mpr`), use direct term application. Zero risk.

### Pattern 2D: `intro-dsimp-exact` → Lambda (Directness)

```lean
-- Before
have h : ∀ i : Fin m, p (ι i) := by intro i; dsimp [p, ι]; exact i.isLt
-- After
have h : ∀ i : Fin m, p (ι i) := fun i => i.isLt
```

Convert `intro x; dsimp; exact term` to direct lambda. 75% reduction. Low risk if proof body is just field access/unfolding.

### Pattern 2B: Extract Repeated Patterns to Helpers (Reusability)

```lean
-- Before (duplication)
have hf' : ∀ x ∈ Ioo a b, HasDerivAt f (deriv f x) x := by intro x hx; exact ...
have hg' : ∀ x ∈ Ioo a b, HasDerivAt g (deriv g x) x := by intro x hx; exact ...

-- After (single helper)
have toHasDerivAt {h : ℝ → ℝ} (hd : DifferentiableOn ℝ h (Ioo a b)) :
    ∀ x ∈ Ioo a b, HasDerivAt h (deriv h x) x := fun x hx => ...
have hf' := toHasDerivAt hfd
have hg' := toHasDerivAt hgd
```

Convert repeated tactic proofs to single reusable helper. 40% reduction when pattern appears 2+ times. **Extract when:** used 3+ times (always), OR used 2 times + complex (>3 lines), OR used 1 time but needed for clarity. Low risk.

### Pattern 3: let+have+exact Inline (Conciseness)

```lean
-- Before
lemma foo := by
  let k' := fun i => (k i).val
  have hk' : StrictMono k' := by ...
  exact hX m k' hk'
-- After
lemma foo := by exact hX m (fun i => (k i).val) (fun i j hij => ...)
```

**⚠️ HIGH RISK:** 60-80% reduction but 93% false positive rate! MUST verify let used ≤2 times (use `analyze_let_usage.py`). Skip if let used ≥3 times (would increase size 2-4×).

### Pattern 3A: Single-Use `have` Inline (Clarity)

```lean
-- Before
have h_meas : Measurable f := measurable_pi_lambda _ ...
rw [← Measure.map_map hproj h_meas]
-- After
rw [← Measure.map_map hproj (measurable_pi_lambda _ ...)]
```

Inline `have` used once if term < 40 chars and no semantic value. 30-50% reduction. **Prime candidates: non-descriptive names like `h`, `this1`, `this2` vs descriptive names like `h_int_open`**. Skip if name aids understanding or used ≥2 times.

### Pattern 3B: Transport Operator ▸ (Conciseness)

```lean
-- Before
theorem count : ValidData.card = 11 := by rw [h_eq, all_card]
-- After
theorem count : ValidData.card = 11 := h_eq ▸ all_card
```

Pattern: `(eq : a = b) ▸ (proof_of_P_b) : P_a`. Read as "transport proof along equality". Zero risk. Use for simple rewrite-then-apply in term mode.

## Medium-Priority Patterns (⭐⭐⭐⭐)

### Pattern 4: Redundant `ext` Before `simp` (Simplicity)

```lean
-- Before
have h : (⟨i.val, ...⟩ : Fin n) = ι i := by apply Fin.ext; simp [ι]
-- After
have h : (⟨i.val, ...⟩ : Fin n) = ι i := by simp [ι]
```

For Fin/Prod/Subtype, `simp` handles extensionality automatically. 50% reduction. Medium risk - not all ext is redundant, test!

### Pattern 5: `congr; ext; rw` → `simp only` (Simplicity)

```lean
-- Before
lemma foo : Measure.map (fun ω i => X (k₁ i) ω) μ = ... := by congr 1; ext ω i; rw [h]
-- After
lemma foo : Measure.map (fun ω i => X (k₁ i) ω) μ = ... := by simp only [h]
```

`simp` handles congruence and extensionality automatically. 67% reduction. Try simp before manual structural reasoning!

### Pattern 5A: Remove Redundant `show` Wrappers (Simplicity)

```lean
-- Before
rw [show X = Y by simp, other]; simp [...]
-- After
simp [...]
```

Remove `show X by simp` wrappers when simp can handle the equality directly in context. 50-75% reduction. Low risk - test with build.

### Pattern 5B: Convert-Based Helper Inlining (Directness)

```lean
-- Before
have hfun : f = g := by ext x; simp [...]
simpa [hfun] using main_proof
-- After
convert main_proof using 2; ext x; simp [...]
```

Inline helper equality used once with `convert ... using N`. 30-40% reduction. Medium risk - may need trial-error for right `using` level.

### Pattern 5C: Inline Single-Use Definitions (Clarity)

```lean
-- Before (2 defs)
def allData := allTilings.map Tiling.data
def All := allData.toFinset
-- After (1 def)
def All := (allTilings.map Tiling.data).toFinset
```

Inline definitions used exactly once with no independent semantic value. 3-4 lines saved, single source of truth for docs. Low risk.

### Pattern 6: Smart `ext` (Simplicity)

```lean
-- Before
apply Subtype.ext; apply Fin.ext; simp [ι]
-- After
ext; simp [ι]
```

`ext` handles multiple nested extensionality layers automatically. 50% reduction.

### Pattern 7: `simp` Closes Goals Directly (Simplicity)

```lean
-- Before
have h : a < b := by simp [defs]; exact lemma
-- After
have h : a < b := by simp [defs]
```

Skip explicit `exact` when simp makes goal trivial or knows the lemma. 67% reduction.

## Medium-Priority Patterns (⭐⭐⭐)

### Pattern 7A: `simpa using` → `exact` (Clarity)

```lean
-- Before
simpa using h
-- After
exact h
```

When `simpa` does no simplification, use `exact`. Zero risk. Try replacing `simpa using h` with `exact h` - if it works, simp was doing nothing.

### Pattern 7B: Unused Lambda Variable Cleanup (Quality)

```lean
-- Before (linter warns)
fun i j hij => proof_not_using_i_or_j
-- After
fun _ _ hij => proof_not_using_i_or_j
```

Replace unused lambda parameters with `_`. Zero risk, eliminates linter noise.

### Pattern 7C: calc with rfl for Definitions (Performance)

```lean
-- Before
have eq : (f b - f a) * g' = (g b - g a) * f' := by simpa [Δf, Δg, ...] using h
-- After (calc with rfl for definitional steps)
calc (f b - f a) * g'
    = Δf * g' := rfl
  _ = Δg * f' := by simpa [Δf, Δg, ...] using h
  _ = (g b - g a) * f' := rfl
```

Use `rfl` for definitional unfolding steps in calc chains - faster than proof search. Zero risk (fails at compile if not definitional).

### Pattern 7D: refine with ?_ (Clarity)

```lean
-- Before
have eq : ... := by ...
exact ⟨c, hc, f', g', hf', hg', eq⟩
-- After
refine ⟨c, hc, f', g', hf', hg', ?_⟩
calc ... -- proof inline
```

Use `refine ... ?_` for term construction with one remaining proof. Low risk, makes "building term with one piece left" explicit.

### Pattern 7E: Named Arguments in obtain (Safety)

```lean
-- Before (type error!)
obtain ⟨c, hc, h⟩ := lemma hab hfc (toHasDerivAt hfd) ...
-- After (self-documenting)
obtain ⟨c, hc, h⟩ := lemma (f := f) (hab := hab) (hfc := hfc) (hff' := toHasDerivAt hfd) ...
```

Use named arguments for complex `obtain` with implicit parameters. Zero risk, prevents positional argument confusion.

### Pattern 8: have-calc Inline (Clarity)

```lean
-- Before
have h : sqrt x < sqrt y := Real.sqrt_lt_sqrt hn hlt
calc sqrt x < sqrt y := h
-- After
calc sqrt x < sqrt y := Real.sqrt_lt_sqrt hn hlt
```

Inline `have` used once in calc if term < 40 chars and no descriptive value. ~50% reduction. Skip if used multiple times or name aids understanding.

### Pattern 9: Inline Constructor Branches (Conciseness)

```lean
-- Before
constructor; · intro k hk; exact hX m k hk; · intro ν hν; have h := ...; exact h.symm
-- After
constructor; · intro k hk; exact hX m k hk; · intro ν hν; exact (...).symm
```

Inline simple constructor branches with semicolons. 30-57% reduction. Keep readable - don't over-inline complex branches.

### Pattern 10: Direct Lemma Over Automation (Simplicity)

```lean
-- Before (fails!)
by omega  -- Error: counterexample with Fin coercions
-- After (works!)
Nat.add_lt_add_left hij k
```

Use direct mathlib lemmas (≤5 tokens) over automation when available. Often shorter AND more reliable. Omega struggles with Fin coercions.

### Pattern 11: Multi-Pattern Match (Simplicity)

```lean
-- Before (nested cases)
cases n with | zero => contra | succ n' => cases n' with | zero => linarith | succ n'' => ...
-- After (flat match)
match n with | 0 | 1 | 2 => omega | _+3 => rfl
```

Replace nested cases with flat match using `| 0 | 1 | 2 =>` for small finite cases (≤5). ~7 lines saved. Low risk.

### Pattern 12: Successor Pattern (n+k) (Clarity)

```lean
-- Before (deeply nested i, i', i'', i''')
cases i with | zero => ... | succ i' => cases i' with | zero => ... | succ i'' => ...
-- After (direct offset)
match i with | 0 => omega | 1 | 2 => rfl | n+3 => [proof using n+3]
```

Use `| n+k =>` for "n ≥ k" range cases. ~25 lines saved, clearer arithmetic. Pattern means "match values ≥ k, bind remainder as n".

### Pattern 13: Symmetric Cases with `<;>` (Conciseness)

```lean
-- Before (duplicate structure)
cases h with | inl => rw [h]; intro; have := ...; omega | inr => rw [h]; intro; have := ...; omega
-- After
rcases h with rfl | rfl <;> (intro h; have : n + 3 ≤ _ := Nat.le_of_dvd (by norm_num) h; omega)
```

Use `rcases ... <;>` when both branches structurally identical. Use `_` for differing values. ~11 lines saved. Keep readable.

### Pattern 14: Inline omega (Conciseness)

```lean
-- Before
have : 2 < n + 3 := by omega; have : a (n + 3) = 0 := hzero _ this; exact this
-- After
exact hzero _ (by omega)
```

Inline trivial arithmetic with `by omega` when used once as argument. ~2 lines saved. Zero risk (fails at compile if omega can't solve).

### Pattern 15: match After ext (Clarity)

```lean
-- Before
ext n; cases n with | zero => exact ha0 | succ n' => cases n' with | zero => ... | succ n'' => ...
-- After
ext n; match n with | 0 => exact ha0 | 1 => exact a1_2 | n+2 => exact hzero _ (by omega)
```

Use `match` after `ext` instead of nested `cases`. ~3 lines saved. Combines well with successor patterns. Low risk.

## Systematic Workflow

### Phase 0: Pre-Optimization Audit (2 min)

Before applying patterns: (1) Remove commented code and unused lemmas, (2) Fix linter warnings, (3) Run `lake build` for clean baseline. This cleanup often accounts for 60%+ of available savings.

### Phase 1: Pattern Discovery (5 min)

Use systematic search, not sequential reading:

```bash
# 1. Find let+have+exact (HIGHEST value)
grep -A 10 "let .*:=" file.lean | grep -B 8 "exact"

# 2. Find by-exact wrappers
grep -B 1 "exact" file.lean | grep "by$"

# 3. Find ext+simp patterns
grep -n "ext.*simp" file.lean

# 4. Find rw+exact (for rwa)
grep -A 1 "rw \[" file.lean | grep "exact"
```

**Expected:** 10-15 targets per file

### Phase 2: Safety Verification (CRITICAL)

For each let+have+exact pattern:

1. Count let binding uses (or use `analyze_let_usage.py`)
2. If used ≥3 times → SKIP (false positive)
3. If used ≤2 times → Proceed with optimization

**Other patterns:** Verify compilation test will catch issues.

### Phase 3: Apply with Testing (5 min per pattern)

1. Apply optimization
2. Run `lake build`
3. If fails: revert immediately, move to next
4. If succeeds: continue

**Strategy:** Apply 3-5 optimizations, then batch test.

### Phase 4: Check Saturation

After 5-10 optimizations, check indicators:
- Success rate < 20% → Stop
- Time per optimization > 15 min → Stop
- Mostly false positives → Stop

**Recommendation:** Declare victory at saturation.

## Documentation Quality Patterns (⭐⭐)

### Pattern 11: Remove Duplicate Inline Comments

When comprehensive docstrings exist above a proof, inline comments that restate the same information are redundant.

```lean
-- Before (with comprehensive docstring above)
/-- Computes measure by factoring through permutation then identity,
    applying the product formula twice. -/
calc Measure.map ...
    -- Factor as permutation composed with identity
    = ... := by rw [...]
    _ -- Apply product formula for identity
    = ... := by rw [...]

-- After (docstring is the single source of truth)
/-- Computes measure by factoring through permutation then identity,
    applying the product formula twice. -/
calc Measure.map ...
    = ... := by rw [...]
    _ = ... := by rw [...]
```

**When to apply:**
- Comprehensive docstring already explains the proof strategy
- Inline comments duplicate information from docstring
- Comments don't add new insights beyond docstring
- Goal is single source of truth for documentation

**When NOT to apply:**
- Inline comments provide details NOT in docstring
- Comments explain non-obvious steps
- No docstring exists (then comments are valuable!)
- Comments mark TODO or highlight subtleties

**Principle:** Single source of truth for documentation. Comprehensive docstrings document strategy; code documents details only if non-obvious.

**When:** Inline comments restate comprehensive docstring
**Risk:** Zero if docstring is complete
**Savings:** Lines + visual clarity

## Anti-Patterns

### Don't Use Semicolons Just to Combine Lines

```lean
-- ❌ Bad (no savings)
intro x; exact proof  -- Semicolon is a token!

-- ✅ Good (when saves ≥2 lines AND sequential)
ext x; simp [...]; use y; simp  -- Sequential operations
```

**When semicolons ARE worth it:**
- ✅ Sequential operations (ext → simp → use)
- ✅ Saves ≥2 lines
- ✅ Simple steps

### Don't Over-Inline

If inlining creates unreadable proof, keep intermediate steps:

```lean
-- ❌ Bad - unreadable
exact combine (obscure nested lambdas spanning 100+ chars)

-- ✅ Good - clear intent
have h1 : A := ...
have h2 : B := ...
exact combine h1 h2
```

### Don't Remove Helpful Names

```lean
-- ❌ Bad
have : ... := by ...  -- 10 lines
have : ... := by ...  -- uses first anonymous have

-- ✅ Good
have h_key_property : ... := by ...
have h_conclusion : ... := by ...  -- uses h_key_property
```

## Failed Optimizations (Learning)

### Not All `ext` Calls Are Redundant

```lean
-- Original (works)
ext x; simp [prefixCylinder]

-- Attempted (FAILS!)
simp [prefixCylinder]  -- simp alone didn't make progress
```

**Lesson:** Sometimes simp needs goal decomposed first. Always test.

### omega with Fin Coercions

```lean
-- Attempted (FAILS with counterexample!)
by omega

-- Correct (works)
Nat.add_lt_add_left hij k
```

**Lesson:** omega struggles with Fin coercions. Direct lemmas more reliable.

## Appendix

### Token Counting Quick Reference

```lean
// ~1 token each
let, have, exact, intro, by, fun

// ~2 tokens each
:=, =>, (fun x => ...), StrictMono

// ~5-10 tokens
let x : Type := definition
have h : Property := by proof
```

**Rule of thumb:**
- Each line ≈ 8-12 tokens
- Each have + proof ≈ 15-20 tokens
- Each inline lambda ≈ 5-8 tokens

### Saturation Metrics

**Session-by-session data:**
- Session 1-2: 60% of patterns worth optimizing
- Session 3: 20% worth optimizing
- Session 4: 6% worth optimizing (diminishing returns)

**Time efficiency:**
- First 15 optimizations: ~2 min each
- Next 7 optimizations: ~5 min each
- Last 3 optimizations: ~18 min each

**Point of diminishing returns:** Success rate < 20% and time > 15 min per optimization.

### Real-World Benchmarks

**Cumulative across sessions:**
- 23 proofs optimized
- ~108 lines removed
- ~34% token reduction average
- ~68% reduction per optimized proof
- 100% compilation success (with multi-candidate approach)

**Technique effectiveness:**
1. let+have+exact: 50% of all savings, 60-80% per instance
2. Smart ext: 50% reduction, no clarity loss
3. ext-simp chains: Saves ≥2 lines when natural
4. rwa: Instant wins, zero risk
5. ext+rfl → rfl: High value when works

### Related References

- [tactics-reference.md](tactics-reference.md) - Tactic catalog
- [domain-patterns.md](domain-patterns.md) - Domain-specific patterns
- [mathlib-style.md](mathlib-style.md) - Style conventions
