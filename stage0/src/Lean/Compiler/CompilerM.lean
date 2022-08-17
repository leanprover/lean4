/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExpr
import Lean.Meta.Transform
import Lean.Compiler.InferType

namespace Lean.Compiler

/--
The state managed by the `CompilerM` `Monad`.
-/
structure CompilerM.State where
  /--
  A `LocalContext` to store local declarations from let binders
  and other constructs in as we move through `Expr`s.
  -/
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

/--
Add a new local declaration with the given arguments to the `LocalContext` of `CompilerM`.
Returns the free variable representing the new declaration.
-/
def mkLocalDecl (binderName : Name) (type : Expr) (bi := BinderInfo.default) : CompilerM Expr := do
  let fvarId ← mkFreshFVarId
  modify fun s => { s with lctx := s.lctx.mkLocalDecl fvarId binderName type bi }
  return .fvar fvarId

/--
Add a new let declaration with the given arguments to the `LocalContext` of `CompilerM`.
Returns the free variable representing the new declaration.
-/
def mkLetDecl (binderName : Name) (type : Expr) (value : Expr) (nonDep : Bool) : CompilerM Expr := do
  let fvarId ← mkFreshFVarId
  let x := .fvar fvarId
  modify fun s => { s with lctx := s.lctx.mkLetDecl fvarId binderName type value nonDep, letFVars := s.letFVars.push x }
  return x

/--
Look for a declaration with the given `FvarId` in the `LocalContext` of `CompilerM`.
-/
def findDecl? (fvarId : FVarId) : CompilerM (Option LocalDecl) := do
  let lctx := (← get).lctx
  return lctx.find? fvarId

/--
Whether a given local declaration is a join point.
-/
def _root_.Lean.LocalDecl.isJp (decl : LocalDecl) : Bool :=
  decl.userName.getPrefix == `_jp

/--
Create a new auxiliary let declaration with value `e` The name of the
declaration is guaranteed to be unique.
Returns the free variable representing the new declaration.
-/
def mkAuxLetDecl (e : Expr) (prefixName := `_x) : CompilerM Expr := do
  if e.isFVar then
    return e
  else
    try
      mkLetDecl (.num prefixName (← get).nextIdx) (← inferType e) e (nonDep := false)
    finally
      modify fun s => { s with nextIdx := s.nextIdx + 1 }

/--
Create an auxiliary let declaration with value `e`, that is a join point.
recognizable by the _jp name prefix.
Returns the free variable representing the new declaration.
-/
def mkJpDecl (e : Expr) : CompilerM Expr := do
  mkAuxLetDecl e `_jp

/--
Compute the maximum auxiliary let variable index that is used within `e`.
-/
def getMaxLetVarIdx (e : Expr) : IO Nat := do
  let maxRef ← IO.mkRef 0
  e.forEach fun
    | .letE (.num (.str .anonymous s) i) .. =>
      if s.get 0 == '_' then maxRef.modify (Nat.max · i) else pure ()
    | _ => pure ()
  maxRef.get

/--
Make sure all let-declarations have unique user-facing names.
We use this method when we want to retrieve candidates for code trasnformations. Examples:
let-declarations that are safe to unfold without producing code blowup, and join point detection.

Remark: user-facing names provided by users are preserved. We keep them as the prefix
of the new unique names.
-/
def ensureUniqueLetVarNames (e : Expr) : CoreM Expr :=
  let pre (e : Expr) : StateRefT Nat CoreM TransformStep := do
    match e with
    | .letE binderName type value body nonDep =>
      let idx ← modifyGet fun s => (s, s+1)
      let binderName' := match binderName with
        | .num p _ => .num p idx
        | _ => .num binderName idx
      return .visit <| .letE binderName' type value body nonDep
    | _ => return .visit e
  Core.transform e pre |>.run' 1

/--
Move through all consecutive lambda abstractions at the top level of `e`.
Returning the body of the last one we find with all bound variables
instantiated as new free variables.
Returns a tuple consisting of:
1. An `Array` of all the newly created free variables
2. The (fully instantiated) body of the last lambda binder that was visited
-/
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

/--
Given an expression representing a `match` return a tuple consisting of:
1. The motive
2. The discriminators
3. The expressions inside of the match arms
-/
def visitMatch (cases : Expr) (casesInfo : CasesInfo) : CompilerM (Expr × Array Expr × Array Expr) := do
  let args := cases.getAppArgs
  let motive := args.get! casesInfo.motivePos

  let mut discrs := #[]
  for i in casesInfo.discrsRange do
    discrs := discrs.push args[i]!

  let mut arms := #[]
  for i in casesInfo.altsRange do
    arms := arms.push (←visitLambda args[i]!).snd
  return (motive, discrs, arms)

def withNewScopeImp (x : CompilerM α) : CompilerM α := do
  let saved ← get
  modify fun s => { s with letFVars := #[] }
  try x
  finally
    let saved := { saved with nextIdx := (← get).nextIdx }
    set saved

def withNewScope [MonadFunctorT CompilerM m] (x : m α) : m α :=
  monadMap (m := CompilerM) withNewScopeImp x

/--
A typeclass for `Monad`s that are able to perform a visit operation for
let binders. That is move through a chain of consecutive let binders
and returning the body of the final one.
-/
class VisitLet (m : Type → Type) where
  /--
  Move through consecutive top level let binders in the first argument,
  applying the function in the second argument to the values before the
  the local declarations for the binders are created. The final return
  value is the body of the last let binder in the chain.
  -/
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

/--
Shorthand for `LocalContext.mkLambda` with the `LocalContext` of `CompilerM`.
-/
def mkLambda (xs : Array Expr) (e : Expr) : CompilerM Expr :=
  return (← get).lctx.mkLambda xs e

/--
Given a join point `jp` of the form `fun y => body`, if `jp` is simple (see `isSimpleLCNF`), just return it
Otherwise, create `let jp := fun y => body` declaration and return `jp`.
-/
def mkJpDeclIfNotSimple (jp : Expr) : CompilerM Expr := do
  if (← isSimpleLCNF jp.bindingBody!) then
    -- Join point is too simple, we eagerly inline it.
    return jp
  else
    mkJpDecl jp

/--
Create "jump" to join point `jp` with value `e`.
Remarks:
- If `e` is unreachable, then result is unreachable
- Add `cast` if `e`'s type is not compatible with the type expected by `jp`. It avoids `cast` on `cast`.
- If creates an auxiliary let-declaration if `e` is not a free variable.
-/
def mkJump (jp : Expr) (e : Expr) : CompilerM Expr := do
  let .forallE _ d b _ ← inferType jp | unreachable!
  let mkJpApp (x : Expr) := mkApp jp x |>.headBeta
  if isLcUnreachable e then
    mkLcUnreachable b
  else if compatibleTypes (← inferType e) d then
    let x ← mkAuxLetDecl e
    return mkJpApp x
  else if let some x := isLcCast? e then
    let x ← mkAuxLetDecl (← mkLcCast x d)
    return mkJpApp x
  else
    let x ← mkAuxLetDecl e
    let x ← mkAuxLetDecl (← mkLcCast x d)
    return mkJpApp x

def mkOptJump (jp? : Option Expr) (e : Expr) : CompilerM Expr := do
  let some jp := jp? | return e
  mkJump jp e

end Lean.Compiler
