/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Daniel Selsam, Wojciech Nawrocki
-/
import Lean.Meta.Basic
import Std.Data.RBMap

namespace Lean

/-- A position of a subexpression in an expression.

See docstring of `SubExpr` for more detail.-/
abbrev SubExpr.Pos := Nat

/-- An expression and the position of a subexpression within this expression.

Subexpressions are encoded as the current subexpression `e` and a
position `p : Pos` denoting `e`'s position with respect to the root expression.

We use a simple encoding scheme for expression positions `Pos`:
every `Expr` constructor has at most 3 direct expression children. Considering an expression's type
to be one extra child as well, we can injectively map a path of `childIdxs` to a natural number
by computing the value of the 4-ary representation `1 :: childIdxs`, since n-ary representations
without leading zeros are unique. Note that `pos` is initialized to `1` (case `childIdxs == []`).-/
structure SubExpr where
  expr : Expr
  pos  : SubExpr.Pos
  deriving Inhabited

namespace SubExpr

abbrev maxChildren : Pos := 4
def mkRoot (e : Expr) : SubExpr := ⟨e, 1⟩

end SubExpr

end Lean
