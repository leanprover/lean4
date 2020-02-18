/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Expr
import Init.Lean.Util.ReplaceExpr

namespace Lean
namespace Meta
/-
  Some tactics substitute hypotheses with new ones and/or terms.
  We track these substitutions using `FVarSubst`.
  It is just a mapping from the original FVarId (internal) name
  to an expression. The new expression should be well-formed with
  respect to the new goal. -/
structure FVarSubst :=
(map : NameMap Expr := {})

namespace FVarSubst

def insert (s : FVarSubst) (fvarId : FVarId) (e : Expr) : FVarSubst :=
{ map := s.map.insert fvarId e }

def contains (s : FVarSubst) (fvarId : FVarId) : Bool :=
s.map.contains fvarId

/-- Given `e`, for each `(x => v)` in `s` replace `x` with `v` in `e` -/
def apply (s : FVarSubst) (e : Expr) : Expr :=
if s.map.isEmpty then e
else if !e.hasFVar then e
else e.replace $ fun e => match e with
  | Expr.fvar fvarId _ => s.map.find? fvarId
  | _                  => none

/--
  Extend substitution `newS` by applying `newS` to entries `(x => v)` to `oldS`,
  and then merging the resulting entry `(x => newS.apply v)` to `newS`.

  Remark: the entries in `newS` have precedence over the ones in `oldS`. -/
def compose (newS oldS : FVarSubst) : FVarSubst :=
if newS.map.isEmpty then oldS
else if oldS.map.isEmpty then newS
else oldS.map.fold (fun m fvarId e => if m.map.contains fvarId then m else m.insert fvarId (m.apply e)) newS

end FVarSubst
end Meta
end Lean
