/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExpr
import Lean.Compiler.InferType

namespace Lean.Compiler

structure CompilerM.State where
  lctx     : LocalContext := {}
  letFVars : Array Expr := #[]
  /-- Next auxiliary variable suffix -/
  nextIdx : Nat := 1

abbrev CompilerM := StateRefT CompilerM.State CoreM

instance : AddMessageContext CompilerM where
  addMessageContext msgData := do
    let env ← getEnv
    let lctx := (← get).lctx
    let opts ← getOptions
    return MessageData.withContext { env, lctx, opts, mctx := {} } msgData

instance : MonadInferType CompilerM where
  inferType e := do InferType.inferType e { lctx := (← get).lctx }

def mkLocalDecl (binderName : Name) (type : Expr) (bi := BinderInfo.default) : CompilerM Expr := do
  let fvarId ← mkFreshFVarId
  modify fun s => { s with lctx := s.lctx.mkLocalDecl fvarId binderName type bi }
  return .fvar fvarId

def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) (nonDep : Bool) : CompilerM Expr := do
  let fvarId ← mkFreshFVarId
  let x := .fvar fvarId
  modify fun s => { s with lctx := s.lctx.mkLetDecl fvarId binderName type value nonDep, letFVars := s.letFVars.push x }
  return x

def mkAuxLetDecl (e : Expr) (prefixName := `_x) : CompilerM Expr := do
  if e.isFVar then
    return e
  else
    try
      mkLetDecl (.num prefixName (← get).nextIdx) (← inferType e) e (nonDep := false)
    finally
      modify fun s => { s with nextIdx := s.nextIdx + 1 }

def mkJpDecl (e : Expr) : CompilerM Expr := do
  mkAuxLetDecl e `_jp

def getMaxLetVarIdx (e : Expr) : CoreM Nat := do
  let maxRef ← IO.mkRef 0
  e.forEach fun
    | .letE (.num `_x i) ..
    | .letE (.num `_jp i) .. => maxRef.modify (Nat.max · i)
    | _ => pure ()
  maxRef.get

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
  let saved ← get
  modify fun s => { s with letFVars := #[] }
  try x
  finally
    let saved := { saved with nextIdx := (← get).nextIdx }
    set saved

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

def mkLetUsingScope (e : Expr) : CompilerM Expr := do
  let e ← if e.isLambda then
    /-
    In LCNF, terminal expression in a `let`-block must not be a lambda.
    -/
    mkAuxLetDecl e
  else
    pure e
  return (← get).lctx.mkLambda (← get).letFVars e

def mkLambda (xs : Array Expr) (e : Expr) : CompilerM Expr :=
  return (← get).lctx.mkLambda xs e

end Lean.Compiler