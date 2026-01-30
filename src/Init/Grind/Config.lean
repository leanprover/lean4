/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Core
public section
namespace Lean.Grind
/--
The configuration for `grind`.
Passed to `grind` using, for example, the `grind (config := { matchEqs := true })` syntax.
-/
structure Config where
  /-- If `trace` is `true`, `grind` records used E-matching theorems and case-splits. -/
  trace : Bool := false
  /-- If `lax` is `true`, `grind` will silently ignore any parameters referring to non-existent theorems
  or for which no patterns can be generated. -/
  lax : Bool := false
  /-- If `suggestions` is `true`, `grind` will invoke the currently configured library suggestion engine on the current goal,
  and add attempt to use the resulting suggestions as additional parameters to the `grind` tactic. -/
  suggestions : Bool := false
  /-- If `locals` is `true`, `grind` will add all definitions from the current file. -/
  locals : Bool := false
  /-- Maximum number of case-splits in a proof search branch. It does not include splits performed during normalization. -/
  splits : Nat := 9
  /-- Maximum number of E-matching (aka heuristic theorem instantiation) rounds before each case split. -/
  ematch : Nat := 5
  /--
  Maximum term generation.
  The input goal terms have generation 0. When we instantiate a theorem using a term from generation `n`,
  the new terms have generation `n+1`. Thus, this parameter limits the length of an instantiation chain. -/
  gen : Nat := 8
  /-- Maximum number of theorem instances generated using E-matching in a proof search tree branch. -/
  instances : Nat := 1000
  /-- If `matchEqs` is `true`, `grind` uses `match`-equations as E-matching theorems. -/
  matchEqs : Bool := true
  /-- If `splitMatch` is `true`, `grind` performs case-splitting on `match`-expressions during the search. -/
  splitMatch : Bool := true
  /-- If `splitIte` is `true`, `grind` performs case-splitting on `if-then-else` expressions during the search. -/
  splitIte : Bool := true
  /--
  If `splitIndPred` is `true`, `grind` performs case-splitting on inductive predicates.
  Otherwise, it performs case-splitting only on types marked with `[grind cases]` attribute. -/
  splitIndPred : Bool := false
  /--
  If `splitImp` is `true`, then given an implication `p → q` or `(h : p) → q h`, `grind` splits on `p`
  if the implication is true. Otherwise, it will split only if `p` is an arithmetic predicate.
  -/
  splitImp : Bool := false
  /-- Maximum number of heartbeats (in thousands) the canonicalizer can spend per definitional equality test. -/
  canonHeartbeats : Nat := 1000
  /-- If `ext` is `true`, `grind` uses extensionality theorems that have been marked with `[grind ext]`. -/
  ext : Bool := true
  /-- If `extAll` is `true`, `grind` uses any extensionality theorems available in the environment. -/
  extAll : Bool := false
  /--
  If `etaStruct` is `true`, then for each term `t : S` such that `S` is a structure,
  and is tagged with `[grind ext]`, `grind` adds the equation `t = ⟨t.1, ..., t.n⟩`
  which holds by reflexivity. Moreover, the extensionality theorem for `S` is not used.
  -/
  etaStruct : Bool := true
  /--
  If `funext` is `true`, `grind` creates new opportunities for applying function extensionality by case-splitting
  on equalities between lambda expressions.
  -/
  funext : Bool := true
  /-- TODO -/
  lookahead : Bool := true
  /-- If `verbose` is `false`, additional diagnostics information is not collected. -/
  verbose : Bool := true
  /-- If `clean` is `true`, `grind` uses `expose_names` and only generates accessible names. -/
  clean : Bool := true
  /--
  If `qlia` is `true`, `grind` may generate counterexamples for integer constraints
  using rational numbers, and ignoring divisibility constraints.
  This approach is cheaper but incomplete. -/
  qlia : Bool := false
  /--
  If `mbtc` is `true`, `grind` will use model-based theory combination for creating new case splits.
  See paper "Model-based Theory Combination" for details.
  -/
  mbtc : Bool := true
  /--
  When set to `true` (default: `true`), local definitions are unfolded during normalization and internalization.
  In other words, given a local context with an entry `x : t := e`, the free variable `x` is reduced to `e`.
  Note that this behavior is also available in `simp`, but there its default is `false` because `simp` is not
  always used as a terminal tactic, and it important to preserve the abstractions introduced by users.
  Additionally, in `grind` we observed that `zetaDelta` is particularly important when combined with function induction.
  In such scenarios, the same let-expressions can be introduced by function induction and also by unfolding the
  corresponding definition. We want to avoid a situation in which `zetaDelta` is not applied to let-declarations
  introduced by function induction while `zeta` unfolds the definition, causing a mismatch.
  Finally, note that congruence closure is less effective on terms containing many binders such as
  `lambda` and `let` expressions.
  -/
  zetaDelta := true
  /--
  When `true` (default: `true`), performs zeta reduction of let expressions during normalization.
  That is, `let x := v; e[x]` reduces to `e[v]`. See also `zetaDelta`.
  -/
  zeta := true
  /--
  When `true` (default: `true`), uses procedure for handling equalities over commutative rings.
  This solver also support commutative semirings, fields, and normalizer non-commutative rings and
  semirings.
  -/
  ring := true
  /--
  Maximum number of steps performed by the `ring` solver.
  A step is counted whenever one polynomial is used to simplify another.
  For example, given `x^2 + 1` and `x^2 * y^3 + x * y`, the first can be
  used to simplify the second to `-1 * y^3 + x * y`.
  -/
  ringSteps := 10000
  /--
  When `true` (default: `true`), uses procedure for handling linear arithmetic for `IntModule`, and
  `CommRing`.
  -/
  linarith := true
  /--
  When `true` (default: `true`), uses procedure for handling linear integer arithmetic for `Int` and `Nat`.
  -/
  lia := true
  /--
  When `true` (default: `true`), uses procedure for handling associative (and commutative) operators.
  -/
  ac := true
  /--
  Maximum number of steps performed by the `ac` solver.
  A step is counted whenever one AC equation is used to simplify another.
  For example, given `ma x z = w` and `max x (max y z) = x`, the first can be
  used to simplify the second to `max w y = x`.
  -/
  acSteps := 1000
  /--
  Maximum exponent eagerly evaluated while computing bounds for `ToInt` and
  the characteristic of a ring.
  -/
  exp : Nat := 2^20
  /--
  When `true` (default: `true`), automatically creates an auxiliary theorem to store the proof.
  -/
  abstractProof := true
  /--
  When `true` (default: `true`), enables the procedure for handling injective functions.
  In this mode, `grind` takes into account theorems such as:
  ```
  @[grind inj] theorem double_inj : Function.Injective double
  ```
  -/
  inj := true
  /--
  When `true` (default: `true`), enables the procedure for handling orders that implement
  at least `Std.IsPreorder`
  -/
  order := true
  /--
  Minimum number of instantiations to trigger summary report in `#grind_lint`.
  Remark: this option is only relevant for the `#grind_lint` command.
  -/
  min : Nat := 10
  /--
  Minimum number of instantiations to trigger detailed report in `#grind_lint`.
  Remark: this option is only relevant for the `#grind_lint` command.
  -/
  detailed : Nat := 50
  /--
  When `trace := true`, uses `sorry` to close unsolved branches.
  -/
  useSorry := true
  /--
  When `true`, it reverts all hypotheses during the preprocessing step,
  and then reintroduces them while simplifying and applying eager `cases`.
  -/
  revert := false
  /--
  When `true`, it enables **function-valued congruence closure**.
  `grind` treats equalities of partially applied functions as first-class equalities
  and propagates them through further applications.
  Given an application `f a₁ a₂ … aₙ`, when `funCC := true` *and* function equality is enabled for `f`,
  `grind` generates and tracks equalities for all partial applications:
  - `f a₁`
  - `f a₁ a₂`
  - `…`
  - `f a₁ a₂ … aₙ`

  This allows equalities such as `f a₁ = g` to propagate to
  `f a₁ a₂ = g a₂`.

  **When is function equality enabled for a symbol?**
  Function equality is automatically enabled in the following cases:
  1. **`f` is not a constant.** (For example, a lambda expression, a local variable, or a function parameter.)
  2. **`f` is a structure field projection**, *provided the structure is not a `class`.*
  3. **`f` is a constant marked with the attribute:** `@[grind funCC]`

  If none of the above conditions apply, function equality is disabled for `f`, and congruence
  closure behaves almost like it does in SMT solvers for first-order logic.
  Here is an example, `grind` can solve when `funCC := true`
  ```
  example (a b : Nat) (g : Nat → Nat) (f : Nat → Nat → Nat) (h : f a = g) :
    f a b = g b := by
  grind
  ```
  -/
  funCC := true
  /--
  When `true`, use reducible transparency when trying to close goals.
  In this setting, only declarations marked with `@[reducible]` are unfolded during
  definitional equality tests.

  This option does not affect the canonicalizer or how theorem patterns are internalized;
  reducible declarations are always unfolded in those contexts.
  -/
  reducible := true
  deriving Inhabited, BEq

/--
Configuration for interactive mode.
We disable `clean := false`.
-/
structure ConfigInteractive extends Config where
  clean := false

/--
A minimal configuration, with ematching and splitting disabled, and all solver modules turned off.
`grind` will not do anything in this configuration,
which can be used a starting point for minimal configurations.
-/
-- This is a `structure` rather than `def` so we can use `declare_config_elab`.
structure NoopConfig extends Config where
  -- Disable splitting
  splits := 0
  -- We don't override the various `splitMatch` / `splitIte` settings separately.

  -- Disable e-matching
  ematch := 0
  -- We don't override `matchEqs` separately.

  -- Disable extensionality
  ext       := false
  extAll    := false
  etaStruct := false
  funext    := false

  -- Disable all solver modules
  ring      := false
  linarith  := false
  lia       := false
  ac        := false

/--
A `grind` configuration that only uses `cutsat` and splitting.

Note: `cutsat` benefits from some amount of instantiation, e.g. `Nat.max_def`.
We don't currently have a mechanism to enable only a small set of lemmas.
-/
-- This is a `structure` rather than `def` so we can use `declare_config_elab`.
structure CutsatConfig extends NoopConfig where
  lia := true
  -- Allow the default number of splits.
  splits := ({} : Config).splits

/--
A `grind` configuration that only uses `ring`.
-/
-- This is a `structure` rather than `def` so we can use `declare_config_elab`.
structure GrobnerConfig extends NoopConfig where
  ring := true

end Lean.Grind
