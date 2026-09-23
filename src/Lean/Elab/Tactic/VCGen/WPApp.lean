/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Meta.Sym.SymM
public import Lean.Meta.Sym.AlphaShareBuilder
import Std.WP.Basic

/-!
`WPApp`: metadata for a goal whose right-hand side is a `wp` application, with `isWPApp?` to
recognize one.
-/

open Lean Meta Sym

namespace Lean.Elab.Tactic.VCGen

/--
Common metadata for a goal whose right-hand side is a weakest-precondition application
`pre ⊑ wp Prog Value Pred EPosts instAL instEAL instWP prog post eposts s₁ ... sₙ`.
-/
public structure WPApp where
  /-- The whole `wp` application, including the excess state arguments. -/
  expr : Expr
  /-- The `wp` function head, separated from its explicit core arguments. -/
  head : Expr
  /-- The ordered core arguments of the `wp` application:
  `#[Prog, Value, Pred, EPosts, instAL, instEAL, instWP, prog, post, eposts]`. -/
  args : Array Expr
  /-- Extra arguments applied after `wp … prog post eposts`, usually concrete state arguments. -/
  excessArgs : Array Expr

namespace WPApp

/-- Program type argument of `wp` (e.g. `m α` or a non-monadic program type). -/
public def Prog (info : WPApp) : Expr := info.args[0]!
/-- The monad of an `m α`-shaped program type, obtained by dropping the value type `α`. For a
non-monadic program type the type itself is returned. -/
public def M (info : WPApp) : Expr :=
  if info.args[0]!.isApp then info.args[0]!.appFn! else info.args[0]!
/-- Result/value type argument of `wp`. -/
public def Value (info : WPApp) : Expr := info.args[1]!
/-- Predicate/lattice type argument of `wp`. -/
public def Pred (info : WPApp) : Expr := info.args[2]!
/-- Exception postcondition type argument of `wp`. -/
public def EPosts (info : WPApp) : Expr := info.args[3]!
/-- `Assertion Pred` instance argument of `wp`. -/
public def instAL (info : WPApp) : Expr := info.args[4]!
/-- `Assertion EPosts` instance argument of `wp`. -/
public def instEAL (info : WPApp) : Expr := info.args[5]!
/-- `WP` instance argument of `wp`. -/
public def instWP (info : WPApp) : Expr := info.args[6]!
/-- Program expression classified by VCGen. -/
public def prog (info : WPApp) : Expr := info.args[7]!
/-- Postcondition argument of `wp`. -/
public def post (info : WPApp) : Expr := info.args[8]!
/-- Exception postcondition argument of `wp`. -/
public def eposts (info : WPApp) : Expr := info.args[9]!

/-- The `wp` application itself, before the excess state arguments apply. -/
public def wp (info : WPApp) : Expr := info.expr.stripArgsN info.excessArgs.size

end WPApp

/-- The `wp` metadata of `rhs`, or `none` when `rhs` is not a `wp` application. -/
public def isWPApp? (rhs : Expr) : Option WPApp :=
  rhs.withApp fun head args =>
    if head.isConstOf ``Std.WP.wp && args.size ≥ 10 then
      some { expr := rhs, head, args := args.take 10, excessArgs := args.drop 10 }
    else
      none

end Lean.Elab.Tactic.VCGen
