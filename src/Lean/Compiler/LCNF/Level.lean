/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.CollectLevelParams
import Lean.Compiler.LCNF.Basic

namespace Lean.Compiler.LCNF

/-!
# Universe level utilities for the code generator
-/

namespace NormLevelParam

/-!
## Universe level parameter normalizer

The specializer creates "keys" for a function specialization. The key is an expression
containing the function being specialized and the argument values used for the specialization.
The key does not contain free variables, and function parameter names are irrelevant due to alpha
equivalence. The universe level normalizer ensures the universe parameter names are irrelevant
when comparing keys.
-/

/-- State for the universe level normalizer monad. -/
structure State where
  /-- Counter for generating new (normalized) universe parameter names. -/
  nextIdx    : Nat := 1
  /-- Mapping from existing universe parameter names to the new ones. -/
  map        : HashMap Name Level := {}
  /-- Parameters that have been normalized. -/
  paramNames : Array Name := #[]

/-- Monad for the universe level normalizer -/
abbrev M := StateM State

/--
Normalize universe level parameter names in the given universe level.
-/
partial def normLevel (u : Level) : M Level := do
  if !u.hasParam then
    return u
  else match u with
    | .zero     => return u
    | .succ v   => return u.updateSucc! (← normLevel v)
    | .max v w  => return u.updateMax! (← normLevel v) (← normLevel w)
    | .imax v w => return u.updateIMax! (← normLevel v) (← normLevel w)
    | .mvar _   => unreachable!
    | .param n  => match (← get).map.find? n with
      | some u => return u
      | none   =>
        let u := Level.param <| (`u).appendIndexAfter (← get).nextIdx
        modify fun { nextIdx, map, paramNames } =>
          { nextIdx := nextIdx + 1, map := map.insert n u, paramNames := paramNames.push n }
        return u

/--
Normalize universe level parameter names in the given expression.
-/
partial def normExpr (e : Expr) : M Expr := do
  if !e.hasLevelParam then
    return e
  else match e with
    | .const _ us      => return e.updateConst! (← us.mapM normLevel)
    | .sort u          => return e.updateSort! (← normLevel u)
    | .app f a         => return e.updateApp! (← normExpr f) (← normExpr a)
    | .letE _ t v b _  => return e.updateLet! (← normExpr t) (← normExpr v) (← normExpr b)
    | .forallE _ d b _ => return e.updateForallE! (← normExpr d) (← normExpr b)
    | .lam _ d b _     => return e.updateLambdaE! (← normExpr d) (← normExpr b)
    | .mdata _ b       => return e.updateMData! (← normExpr b)
    | .proj _ _ b      => return e.updateProj! (← normExpr b)
    | .mvar _          => unreachable!
    | _                => return e

end NormLevelParam

/--
Normalize universe level parameter names in the given expression.
The function also returns the list of universe level parameter names that have been normalized.
-/
def normLevelParams (e : Expr) : Expr × List Name :=
  let (e, s) := NormLevelParam.normExpr e |>.run {}
  (e, s.paramNames.toList)

namespace CollectLevelParams
/-!
## Universe level collector

This module extends support for `Code`. See `Lean.Util.CollectLevelParams.lean`

In the code specializer, we create new auxiliary declarations and the
universe level parameter collector is used to setup the new auxiliary declarations.

See `Decl.setLevelParams`.
-/
open Lean.CollectLevelParams

abbrev visitType (type : Expr) : Visitor :=
  visitExpr type

def visitArg (arg : Arg) : Visitor :=
  match arg with
  | .erased | .fvar .. => id
  | .type e => visitType e

def visitArgs (args : Array Arg) : Visitor :=
  fun s => args.foldl (init := s) fun s arg => visitArg arg s

def visitLetValue (e : LetValue) : Visitor :=
  match e with
  | .erased | .value .. | .proj .. => id
  | .const _ us args => visitLevels us ∘ visitArgs args
  | .fvar _ args => visitArgs args

def visitParam (p : Param) : Visitor :=
  visitType p.type

def visitParams (ps : Array Param) : Visitor :=
  fun s => ps.foldl (init := s) fun s p => visitParam p s

mutual
  partial def visitAlt (alt : Alt) : Visitor :=
    match alt with
    | .default k => visitCode k
    | .alt _ ps k => visitCode k ∘ visitParams ps

  partial def visitAlts (alts : Array Alt) : Visitor :=
    fun s => alts.foldl (init := s) fun s alt => visitAlt alt s

  partial def visitCode : Code → Visitor
    | .let decl k => visitCode k ∘ visitLetValue decl.value ∘ visitType decl.type
    | .fun decl k | .jp decl k => visitCode k ∘ visitCode decl.value ∘ visitParams decl.params ∘ visitType decl.type
    | .cases c => visitAlts c.alts ∘ visitType c.resultType
    | .unreach type => visitType type
    | .return _ => id
    | .jmp _ args => visitArgs args
end

end CollectLevelParams

open Lean.CollectLevelParams
open CollectLevelParams

/--
Collect universe level parameters collecting in the type, parameters, and value, and then
set `decl.levelParams` with the resulting value.
-/
def Decl.setLevelParams (decl : Decl) : Decl :=
  let levelParams := (visitCode decl.value ∘ visitParams decl.params ∘ visitType decl.type) {} |>.params.toList
  { decl with levelParams }

end Lean.Compiler.LCNF
