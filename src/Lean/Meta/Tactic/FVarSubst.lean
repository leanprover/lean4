/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Data.AssocList
import Lean.Expr
import Lean.LocalContext
import Lean.Util.ReplaceExpr

namespace Lean.Meta
/--
  Some tactics substitute hypotheses with expressions.
  We track these substitutions using `FVarSubst`.
  It is just a mapping from the original FVarId (internal) name
  to an expression. The free variables occurring in the expression must
  be defined in the new goal. -/
structure FVarSubst where
  map : AssocList FVarId Expr := {}
  deriving Inhabited

namespace FVarSubst

def empty : FVarSubst := {}

def isEmpty (s : FVarSubst) : Bool :=
  s.map.isEmpty

def contains (s : FVarSubst) (fvarId : FVarId) : Bool :=
  s.map.contains fvarId

/-- Add entry `fvarId |-> v` to `s` if `s` does not contain an entry for `fvarId`. -/
def insert (s : FVarSubst) (fvarId : FVarId) (v : Expr) : FVarSubst :=
  if s.contains fvarId then s
  else
    let map := s.map.mapVal fun e => e.replaceFVarId fvarId v;
    { map := map.insert fvarId v }

def erase (s : FVarSubst) (fvarId : FVarId) : FVarSubst :=
  { map := s.map.erase fvarId }

def find? (s : FVarSubst) (fvarId : FVarId) : Option Expr :=
  s.map.find? fvarId

def get (s : FVarSubst) (fvarId : FVarId) : Expr :=
  match s.map.find? fvarId with
  | none   => mkFVar fvarId -- it has not been replaced
  | some v => v

/-- Given `e`, for each `(x => v)` in `s` replace `x` with `v` in `e` -/
def apply (s : FVarSubst) (e : Expr) : Expr :=
  if s.map.isEmpty then e
  else if !e.hasFVar then e
  else e.replace fun e => match e with
    | Expr.fvar fvarId => match s.map.find? fvarId with
      | none   => e
      | some v => v
    | _ => none

def domain (s : FVarSubst) : List FVarId :=
  s.map.foldl (init := []) fun r k _ => k :: r

def any (p : FVarId → Expr → Bool) (s : FVarSubst) : Bool :=
  s.map.any p

end FVarSubst
end Meta

def LocalDecl.applyFVarSubst (s : Meta.FVarSubst) : LocalDecl → LocalDecl
  | LocalDecl.cdecl i id n t bi k   => LocalDecl.cdecl i id n (s.apply t) bi k
  | LocalDecl.ldecl i id n t v nd k => LocalDecl.ldecl i id n (s.apply t) (s.apply v) nd k

abbrev Expr.applyFVarSubst (s : Meta.FVarSubst) (e : Expr) : Expr :=
  s.apply e

end Lean
