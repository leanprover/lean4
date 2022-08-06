/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.InferType

namespace Lean.Compiler

structure CompilerM.State where
  lctx     : LocalContext
  letFVars : Array Expr := #[]

abbrev CompilerM := StateRefT CompilerM.State CoreM

@[inline] def liftMetaM (x : MetaM α) : CompilerM α := do
  x.run' { lctx := (← get).lctx }

def inferType (e : Expr) : CompilerM Expr := liftMetaM <| Meta.inferType e

def whnf (e : Expr) : CompilerM Expr := liftMetaM <| Meta.whnf e

def isProp (e : Expr) : CompilerM Bool := liftMetaM <| Meta.isProp e

def isTypeFormerType (e : Expr) : CompilerM Bool := liftMetaM <| Meta.isTypeFormerType e

def mkLocalDecl (binderName : Name) (type : Expr) (bi := BinderInfo.default) : CompilerM Expr := do
  let fvarId ← mkFreshFVarId
  modify fun s => { s with lctx := s.lctx.mkLocalDecl fvarId binderName type bi }
  return .fvar fvarId

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) (nonDep : Bool) : CompilerM Expr := do
  let fvarId ← mkFreshFVarId
  let x := .fvar fvarId
  modify fun s => { s with lctx := s.lctx.mkLetDecl fvarId binderName type value nonDep, letFVars := s.letFVars.push x }
  return x

def visitLambda (e : Expr) : CompilerM (Array Expr × Expr) :=
  go e #[]
where
  go (e : Expr) (fvars : Array Expr) := do
    if let .lam binderName type body binderInfo := e then
      let type := type.instantiateRev fvars
      let fvar ← mkLocalDecl binderName type binderInfo
      go body (fvars.push fvar)
    else
      return (fvars, e.instantiateRev fvars)

def withNewScopeImp (x : CompilerM α) : CompilerM α := do
  let s ← get
  modify fun s => { s with letFVars := #[] }
  try x finally set s

def withNewScope [MonadFunctorT CompilerM m] (x : m α) : m α :=
  monadMap (m := CompilerM) withNewScopeImp x

class VisitLet (m : Type → Type) where
  visitLet : Expr → (Expr → m Expr) → m Expr

export VisitLet (visitLet)

def visitLetImp (e : Expr) (f : Expr → CompilerM Expr) : CompilerM Expr :=
  go e #[]
where
  go (e : Expr) (fvars : Array Expr) : CompilerM Expr := do
    if let .letE binderName type value body nonDep := e then
      let type := type.instantiateRev fvars
      let value := value.instantiateRev fvars
      let value ← f value
      let fvar ← mkLetDecl binderName type value nonDep
      go body (fvars.push fvar)
    else
      return e.instantiateRev fvars

instance : VisitLet CompilerM where
  visitLet := visitLetImp

instance [VisitLet m] : VisitLet (ReaderT ρ m) where
  visitLet e f ctx := visitLet e (f · ctx)

instance [VisitLet m] : VisitLet (StateRefT' ω σ m) := inferInstanceAs (VisitLet (ReaderT _ _))

def mkLetUsingScope (e : Expr) : CompilerM Expr :=
  return (← get).lctx.mkLambda (← get).letFVars e

def mkLambda (xs : Array Expr) (e : Expr) : CompilerM Expr :=
  return (← get).lctx.mkLambda xs e

end Lean.Compiler