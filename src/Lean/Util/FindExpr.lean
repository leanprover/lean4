/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr

namespace Lean
namespace Expr

@[extern "lean_find_expr"]
opaque findImpl? (p : @& (Expr → Bool)) (e : @& Expr) : Option Expr

@[inline] def find? (p : Expr → Bool) (e : Expr) : Option Expr := findImpl? p e

/-- Return true if `e` occurs in `t` -/
def occurs (e : Expr) (t : Expr) : Bool :=
  (t.find? fun s => s == e).isSome

/--
  Return type for `findExt?` function argument.
-/
inductive FindStep where
  /-- Found desired subterm -/ | found
  /-- Search subterms -/ | visit
  /-- Do not search subterms -/ | done

@[extern "lean_find_ext_expr"]
opaque findExtImpl? (p : @& (Expr → FindStep)) (e : @& Expr) : Option Expr

/--
  Similar to `find?`, but `p` can return `FindStep.done` to interrupt the search on subterms.
  Remark: Differently from `find?`, we do not invoke `p` for partial applications of an application. -/
@[inline] def findExt? (p : Expr → FindStep) (e : Expr) : Option Expr := findExtImpl? p e

end Expr
end Lean
