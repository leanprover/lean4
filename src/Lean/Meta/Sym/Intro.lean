/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.IsClass
import Lean.Meta.Sym.AlphaShareBuilder
namespace Lean.Meta.Sym
open Internal
/--
Efficient `intro` for symbolic simulation.
-/
def introCore (mvarId : MVarId) (max : Nat) (names : Array Name) : SymM (Array FVarId × MVarId) := do
  if max == 0 then return (#[], mvarId)
  let env ← getEnv
  let mvarDecl ← mvarId.getDecl
  /-
  Helper function for constructing a value to assign to `mvarId`. We don't need max sharing here.
  -/
  let rec mkValueLoop (i : Nat) (type : Expr) (body : Expr) : Expr :=
    if i >= max then
      body
    else match type with
      | .mdata _ type => mkValueLoop i type body
      | .forallE name domain type bi =>
         mkLambda name bi domain (mkValueLoop (i+1) type body)
      | .letE name valType value type c =>
        mkLet name valType value (mkValueLoop (i+1) type body) c
      | _ => body
  /-
  Constructs `e #(n-1) ... #0`. This is helper function for constructing a value to assign to `mvarId`.
  -/
  let rec mkAppBVars (e : Expr) (n : Nat) : Expr :=
    match n with
    | 0 => e
    | n+1 => mkAppBVars (mkApp e (mkBVar n)) n
  /-
  Constructs a value to assign to `mvarId` using `mkValueLoop` and `mkAppBVars`.
  -/
  let mkValueAndAssign (fvars : Array Expr) (mvarId' : MVarId) : MetaM Unit := do
    let auxMVar ← mkFreshExprMVarAt mvarDecl.lctx mvarDecl.localInstances mvarDecl.type .syntheticOpaque
    let val := mkAppBVars auxMVar fvars.size
    let val := mkValueLoop 0 mvarDecl.type val
    assignDelayedMVar auxMVar.mvarId! fvars mvarId'
    mvarId.assign val
  let finalize (lctx : LocalContext) (localInsts : LocalInstances) (fvars : Array Expr) (type : Expr) : SymM (Array Expr × MVarId) := do
    let type ← instantiateRevS type fvars
    let mvar' ← mkFreshExprMVarAt lctx localInsts type .syntheticOpaque mvarDecl.userName
    let mvarId' := mvar'.mvarId!
    mkValueAndAssign fvars mvarId'
    return (fvars, mvarId')
  let mkName (binderName : Name) (i : Nat) : MetaM Name := do
    if h : i < names.size then
      return names[i]
    else
      mkFreshUserName binderName
  let updateLocalInsts (localInsts : LocalInstances) (fvar : Expr) (type : Expr) : LocalInstances :=
    if let some className := isClass? env type then
      localInsts.push { fvar, className }
    else
      localInsts
  let rec visit (i : Nat) (lctx : LocalContext) (localInsts : LocalInstances) (fvars : Array Expr) (type : Expr) : SymM (Array Expr × MVarId) := do
    if i >= max then
      finalize lctx localInsts fvars type
    else match type with
    | .mdata _ type => visit i lctx localInsts fvars type
    | .forallE n type body bi =>
      let type       ← instantiateRevS type fvars
      let fvarId     ← mkFreshFVarId
      let lctx       := lctx.mkLocalDecl fvarId (← mkName n i) type bi
      let fvar       ← mkFVarS fvarId
      let fvars      := fvars.push fvar
      let localInsts := updateLocalInsts localInsts fvar type
      visit (i+1) lctx localInsts fvars body
    | .letE n type value body nondep =>
      let type       ← instantiateRevS type fvars
      let value      ← instantiateRevS value fvars
      let fvarId     ← mkFreshFVarId
      /-
      We have both dependent and non-dependent `let` expressions result in dependent `ldecl`s.
      This is fine here since we never revert them in the Sym framework.
      **Note**: If `type` is a proposition we could use a `cdecl`.
      -/
      let lctx       := lctx.mkLetDecl fvarId (← mkName n i) type value
      let fvar       ← mkFVarS fvarId
      let fvars      := fvars.push fvar
      let localInsts := updateLocalInsts localInsts fvar type
      visit (i+1) lctx localInsts fvars body
    | _ => finalize lctx localInsts fvars type
  let (fvars, mvarId') ← visit 0 mvarDecl.lctx mvarDecl.localInstances #[] mvarDecl.type
  return (fvars.map (·.fvarId!), mvarId')

def hugeNat := 1000000

/--
Introduces leading binders (universal quantifiers and let-expressions) from the goal's target type.

If `names` is non-empty, introduces (at most) `names.size` binders using the provided names.
If `names` is empty, introduces all leading binders using inaccessible names.

Returns the introduced free variable Ids and the updated goal.

Throws an error if the target type does not have a leading binder.
-/
public def intros (mvarId : MVarId) (names : Array Name := #[]) : SymM (Array FVarId × MVarId) := do
  let result ← if names.isEmpty then
    introCore mvarId hugeNat #[]
  else
    introCore mvarId  names.size names
  if result.1.isEmpty then
    throwError "`intros` failed, binder expected"
  return result

/--
Introduces a single binder from the goal's target type with the given name.

Returns the introduced free variable ID and the updated goal.
Throws an error if the target type does not have a leading binder.
-/
public def intro (mvarId : MVarId) (name : Name) : SymM (FVarId × MVarId) := do
  let (fvarIds, goal') ← introCore mvarId 1 #[name]
  if h : 0 < fvarIds.size then
    return (fvarIds[0], goal')
  else
    throwError "`intro` failed, binder expected"

/--
Introduces exactly `num` binders from the goal's target type.

Returns the introduced free variable IDs and the updated goal.
Throws an error if the target type has fewer than `num` leading binders.
-/
public def introN (mvarId : MVarId) (num : Nat) : SymM (Array FVarId × MVarId) := do
  let result ← introCore mvarId num #[]
  unless result.1.size == num do
    throwError "`introN` failed, insufficient number of binders"
  return result

end Lean.Meta.Sym
