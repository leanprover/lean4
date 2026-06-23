/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Tactics
public section
namespace Lean.Parser.Sym.DSimp

/-!
# DSimproc DSL for `Sym.dsimp`

A syntax category for specifying `pre` and `post` dsimproc chains in `Sym.dsimp` variants.

## Primitives
- `ground` — evaluates ground (fully concrete) terms
- `beta` — beta reduction
- `zeta` - zeta reduction
- `zeta_delta [ids]` - zeta delta reduction
- `proj` - reduce projections
- `match` - reduce match-expressions

## Combinators
- `a >> b` — apply `a`, then apply `b` to the result (andThen)
- `a <|> b` — try `a`, if no progress try `b` (orElse)
-/

declare_syntax_cat sym_dsimproc (behavior := both)

-- Simproc primitives

/-- Do nothing -/
syntax (name := none) "none" : sym_dsimproc

/-- Evaluate ground (fully concrete) terms. -/
syntax (name := ground) "ground" : sym_dsimproc

/-- Beta reduction -/
syntax (name := beta) "beta" : sym_dsimproc

/-- zeta reduction. That is, expands let-expressions. -/
syntax (name := zeta) "zeta" : sym_dsimproc

/-- zeta delta reduction. That is, expands all let-declarations. -/
syntax (name := zetaDelta) "zeta_delta" : sym_dsimproc

/-- Projection reduction. -/
syntax (name := proj) "proj" : sym_dsimproc

/-- `match`-expression reduction. -/
syntax (name := reduceMatch) "match" : sym_dsimproc

-- DSimproc combinators

/-- Apply `a`, then apply `b` to the result. -/
syntax:60 (name := andThen) sym_dsimproc:61 " >> " sym_dsimproc:60 : sym_dsimproc

/-- Try `a`, if no progress try `b`. -/
syntax:20 (name := orElse) sym_dsimproc:21 " <|> " sym_dsimproc:20 : sym_dsimproc

/-- Parenthesized dsimproc expression. -/
syntax (name := dsimprocParen) "(" sym_dsimproc ")" : sym_dsimproc

end Lean.Parser.Sym.DSimp

/-!
## `register_sym_dsimp` command

Declares a named `Sym.dsimp` variant with `pre`/`post` simproc chains and optional config overrides.

```
register_sym_dsimp myVariant where
  pre  := match
  post := ground >> zeta_delta
```
-/

namespace Lean.Parser.Command

declare_syntax_cat sym_dsimp_field (behavior := both)

/-- Pre-processing simproc chain. -/
syntax (name := symDSimpFieldPre) "pre" " := " sym_dsimproc : sym_dsimp_field

/-- Post-processing simproc chain. -/
syntax (name := symDSimpFieldPost) "post" " := " sym_dsimproc : sym_dsimp_field

/-- Maximum number of simplification steps. -/
syntax (name := symDSimpFieldMaxSteps) "maxSteps" " := " num : sym_dsimp_field

/--
Register a named `Sym.dsimp` variant.

```
register_sym_dsimp myVariant where
  pre  := match
  post := ground >> zeta_delta
  maxSteps := 50000
```
-/
syntax (name := registerSymDSimp) "register_sym_dsimp" ident "where"
  (colGt sym_dsimp_field)* : command

end Lean.Parser.Command
