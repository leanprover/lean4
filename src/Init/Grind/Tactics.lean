/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Tactics

namespace Lean.Grind
/--
Gadget for representing generalization steps `h : x = val` in patterns
This gadget is used to represent patterns in theorems that have been generalized to reduce the
number of casts introduced during E-matching based instantiation.

For example, consider the theorem
```
Option.pbind_some {α1 : Type u_1} {a : α1} {α2 : Type u_2}
    {f : (a_1 : α1) → some a = some a_1 → Option α2}
    : (some a).pbind f = f a rfl
```
Now, suppose we have a goal containing the term `c.pbind g` and the equivalence class
`{c, some b}`. The E-matching module generates the instance
```
(some b).pbind (cast ⋯ g)
```
The `cast` is necessary because `g`'s type contains `c` instead of `some b.
This `cast` problematic because we don't have a systematic way of pushing casts over functions
to its arguments. Moreover, heterogeneous equality is not effective because the following theorem
is not provable in DTT:
```
theorem hcongr (h₁ : f ≍ g) (h₂ : a ≍ b)  : f a ≍ g b := ...
```
The standard solution is to generalize the theorem above and write it as
```
theorem Option.pbind_some'
        {α1 : Type u_1} {a : α1} {α2 : Type u_2}
        {x : Option α1}
        {f : (a_1 : α1) → x = some a_1 → Option α2}
        (h : x = some a)
        : x.pbind f = f a h := by
  subst h
  apply Option.pbind_some
```
Internally, we use this gadget to mark the E-matching pattern as
```
(genPattern h x (some a)).pbind f
```
This pattern is matched in the same way we match `(some a).pbind f`, but it saves the proof
for the actual term to the `some`-application in `f`, and the actual term in `x`.

In the example above, `c.pbind g` also matches the pattern `(genPattern h x (some a)).pbind f`,
and stores `c` in `x`, `b` in `a`, and the proof that `c = some b` in `h`.
-/
def genPattern {α : Sort u} (_h : Prop) (x : α) (_val : α) : α := x

/-- Similar to `genPattern` but for the heterogeneous case -/
def genHEqPattern {α β : Sort u} (_h : Prop) (x : α) (_val : β) : α := x
end Lean.Grind

namespace Lean.Parser
/--
Reset all `grind` attributes. This command is intended for testing purposes only and should not be used in applications.
-/
syntax (name := resetGrindAttrs) "reset_grind_attrs%" : command

namespace Attr
syntax grindGen    := &"gen "
syntax grindEq     := "= " (grindGen)?
syntax grindEqBoth := atomic("_" "=" "_ ") (grindGen)?
syntax grindEqRhs  := atomic("=" "_ ") (grindGen)?
syntax grindEqBwd  := atomic("←" "= ") <|> atomic("<-" "= ")
syntax grindBwd    := ("← " <|> "<- ") (grindGen)?
syntax grindFwd    := "→ " <|> "-> "
syntax grindRL     := "⇐ " <|> "<= "
syntax grindLR     := "⇒ " <|> "=> "
syntax grindUsr    := &"usr "
syntax grindCases  := &"cases "
syntax grindCasesEager := atomic(&"cases" &"eager ")
syntax grindIntro  := &"intro "
syntax grindExt    := &"ext "
syntax grindMod :=
    grindEqBoth <|> grindEqRhs <|> grindEq <|> grindEqBwd <|> grindBwd
    <|> grindFwd <|> grindRL <|> grindLR <|> grindUsr <|> grindCasesEager
    <|> grindCases <|> grindIntro <|> grindExt <|> grindGen
syntax (name := grind) "grind" (grindMod)? : attr
syntax (name := grind?) "grind?" (grindMod)? : attr
end Attr
end Lean.Parser

namespace Lean.Grind
/--
The configuration for `grind`.
Passed to `grind` using, for example, the `grind (config := { matchEqs := true })` syntax.
-/
structure Config where
  /-- If `trace` is `true`, `grind` records used E-matching theorems and case-splits. -/
  trace : Bool := false
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
  -/
  ring := true
  ringSteps := 10000
  /--
  When `true` (default: `false`), the commutative ring procedure in `grind` constructs stepwise
  proof terms, instead of a single-step Nullstellensatz certificate
  -/
  ringNull := false
  /--
  When `true` (default: `true`), uses procedure for handling linear arithmetic for `IntModule`, and
  `CommRing`.
  -/
  linarith := true
  /--
  When `true` (default: `true`), uses procedure for handling linear integer arithmetic for `Int` and `Nat`.
  -/
  cutsat := true
  deriving Inhabited, BEq

end Lean.Grind

namespace Lean.Parser.Tactic

/-!
`grind` tactic and related tactics.
-/

syntax grindErase := "-" ident
syntax grindLemma := (Attr.grindMod)? ident
syntax grindParam := grindErase <|> grindLemma

syntax (name := grind)
  "grind" optConfig (&" only")?
  (" [" withoutPosition(grindParam,*) "]")?
  ("on_failure " term)? : tactic


syntax (name := grindTrace)
  "grind?" optConfig (&" only")?
  (" [" withoutPosition(grindParam,*) "]")?
  ("on_failure " term)? : tactic

end Lean.Parser.Tactic
