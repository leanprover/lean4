/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Tactics
public section
namespace Lean.Parser.Sym.Simp

/-!
# Simproc and Discharger DSLs for `Sym.simp`

## Simproc DSL (`sym_simproc`)

A syntax category for specifying `pre` and `post` simproc chains in `Sym.simp` variants.

### Primitives
- `ground` — evaluates ground (fully concrete) terms
- `telescope` — simplifies telescope binders (have-values, arrow hypotheses) but not the final body
- `rewrite setName [with discharger]` — rewrites using a named theorem set
- `rewrite [thm₁, thm₂, ...] [with discharger]` — rewrites using inline theorems
- `self` — recursive simplification (calls the full simplifier)
- `none` — identity (no simplification)

### Combinators
- `a >> b` — apply `a`, then apply `b` to the result (andThen)
- `a <|> b` — try `a`, if no progress try `b` (orElse)

## Discharger DSL (`sym_discharger`)

A syntax category for specifying dischargers used in the `with` clause of `rewrite`.
Dischargers attempt to prove side conditions of conditional rewrite rules.

### Primitives
- `self` — recursive simplifier discharge (`dischargeSimpSelf`)
- `none` — no discharge, only unconditional rewrites apply (`dischargeNone`)
-/

declare_syntax_cat sym_simproc (behavior := both)
declare_syntax_cat sym_discharger (behavior := both)

-- Simproc primitives

/-- Evaluate ground (fully concrete) terms. -/
syntax (name := ground) "ground" : sym_simproc

/-- Simplify telescope binders but not the final body. -/
syntax (name := telescope) "telescope" : sym_simproc

/-- Simplify control-flow expressions (`if-then-else`, `match`, `cond`, `dite`).
Visits only conditions and discriminants. Intended as a `pre` simproc. -/
syntax (name := control) "control" : sym_simproc

/-- Simplify arrow telescopes (`p₁ → p₂ → ... → q`) without entering binders.
Simplifies each `pᵢ` and `q` individually. Intended as a `pre` simproc. -/
syntax (name := arrowTelescope) "arrow_telescope" : sym_simproc

/-- Rewrite using a named theorem set. Optionally specify a discharger for conditional rewrites. -/
syntax (name := rewriteSet) "rewrite" ident (" with " sym_discharger)? : sym_simproc

/-- Rewrite using inline theorems. Optionally specify a discharger for conditional rewrites. -/
syntax (name := rewriteInline) "rewrite" " [" ident,* "]" (" with " sym_discharger)? : sym_simproc

/-- Recursive simplification (calls the full simplifier). -/
syntax (name := self) "self" : sym_simproc

/-- Identity simproc (no simplification). -/
syntax (name := none) "none" : sym_simproc

-- Simproc combinators

/-- Apply `a`, then apply `b` to the result. -/
syntax:60 (name := andThen) sym_simproc:61 " >> " sym_simproc:60 : sym_simproc

/-- Try `a`, if no progress try `b`. -/
syntax:20 (name := orElse) sym_simproc:21 " <|> " sym_simproc:20 : sym_simproc

/-- Parenthesized simproc expression. -/
syntax (name := simprocParen) "(" sym_simproc ")" : sym_simproc

-- Discharger primitives

/-- Recursive simplifier discharge. Calls the full simplifier to prove side conditions. -/
syntax (name := dischSelf) "self" : sym_discharger

/-- No discharge. Only unconditional rewrites will apply. -/
syntax (name := dischNone) "none" : sym_discharger

/-- Parenthesized discharger expression. -/
syntax (name := dischParen) "(" sym_discharger ")" : sym_discharger

end Lean.Parser.Sym.Simp

/-!
## `register_sym_simp` command

Declares a named `Sym.simp` variant with `pre`/`post` simproc chains and optional config overrides.

```
register_sym_simp myVariant where
  pre  := telescope
  post := ground >> rewrite mySet with self
```
-/

namespace Lean.Parser.Command

declare_syntax_cat sym_simp_field (behavior := both)

/-- Pre-processing simproc chain. -/
syntax (name := symSimpFieldPre) "pre" " := " sym_simproc : sym_simp_field

/-- Post-processing simproc chain. -/
syntax (name := symSimpFieldPost) "post" " := " sym_simproc : sym_simp_field

/-- Maximum number of simplification steps. -/
syntax (name := symSimpFieldMaxSteps) "maxSteps" " := " num : sym_simp_field

/-- Maximum depth of recursive discharge attempts. -/
syntax (name := symSimpFieldMaxDischargeDepth) "maxDischargeDepth" " := " num : sym_simp_field

/--
Register a named `Sym.simp` variant.

```
register_sym_simp myVariant where
  pre  := telescope
  post := ground >> rewrite [thm1, thm2] with self
  maxSteps := 50000
```
-/
syntax (name := registerSymSimp) "register_sym_simp" ident "where"
  (colGt sym_simp_field)* : command

end Lean.Parser.Command