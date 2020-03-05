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
  Some tactics substitute hypotheses with new ones.
  We track these substitutions using `FVarSubst`.
  It is just a mapping from the original FVarId (internal) name
  to the new one. The new free variable should be defined in the new goal. -/
structure FVarSubst :=
(map : NameMap FVarId := {})

namespace FVarSubst

def empty : FVarSubst := {}

def insert (s : FVarSubst) (fvarId : FVarId) (fvarIdNew : FVarId) : FVarSubst :=
{ map := s.map.insert fvarId fvarIdNew }

def contains (s : FVarSubst) (fvarId : FVarId) : Bool :=
s.map.contains fvarId

def erase (s : FVarSubst) (fvarId : FVarId) : FVarSubst :=
{ map := s.map.erase fvarId }

def get (s : FVarSubst) (fvarId : FVarId) : FVarId :=
match s.map.find? fvarId with
| none         => fvarId -- it has not been replaced
| some fvarId' => fvarId'

/-- Given `e`, for each `(x => v)` in `s` replace `x` with `v` in `e` -/
def apply (s : FVarSubst) (e : Expr) : Expr :=
if s.map.isEmpty then e
else if !e.hasFVar then e
else e.replace $ fun e => match e with
  | Expr.fvar fvarId _ => match s.map.find? fvarId with
    | none         => e
    | some fvarId' => mkFVar fvarId'
  | _                  => none

/--
  Extend substitution `newS` by applying `newS` to entries `(x => v)` to `oldS`,
  and then merging the resulting entry `(x => newS.apply v)` to `newS`.

  Remark: the entries in `newS` have precedence over the ones in `oldS`. -/
def compose (newS oldS : FVarSubst) : FVarSubst :=
if newS.map.isEmpty then oldS
else if oldS.map.isEmpty then newS
else oldS.map.fold
  (fun m fvarId fvarId' =>
    match m.map.find? fvarId with
    | some _ => m -- newS already has a substitution for fvarId
    | none   =>
      match m.map.find? fvarId' with
      | none          => m.insert fvarId fvarId'
      | some fvarId'' => m.insert fvarId fvarId'')
  newS

end FVarSubst
end Meta
end Lean
