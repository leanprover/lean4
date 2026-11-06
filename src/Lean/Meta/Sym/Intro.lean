/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Tactic.Intro
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.IsClass
import Lean.Meta.Sym.AlphaShareBuilder
import Lean.Meta.Sym.InstantiateMVarsS
namespace Lean.Meta.Sym
open Lean.Meta.Sym.Internal

/-- The constructor application `C.mk ps` if `type` is `C ps` for an inductive type `C` with one
constructor, no fields, no indices and no recursion, such as `PUnit` or `True`. The kernel
identifies every value of `C ps` with `C.mk ps`: by eta for structures with no fields, and by proof
irrelevance for `Prop`. -/
def unitLikeValue? (type : Expr) : SymM (Option Expr) :=
  matchConstNonRecStructure type.getAppFn (fun _ => return none) fun info us ctor => do
    unless ctor.numFields == 0 && type.getAppNumArgs == info.numParams do return none
    return some (← mkAppNS (← mkConstS ctor.name us) type.getAppArgs)
/--
Efficient `intro` for symbolic simulation.

Binders without a name in `names` are named after their binder name. If `hygienic` is `true`, those
names are made inaccessible (fresh macro scopes); otherwise they are accessible names unused in the
(incrementally built) local context.

If the binders end at an assigned metavariable, e.g., `⊢ ?a` with `?a := p → q`, the binders of its
value are introduced too.

A `∀` binder whose type `d` has the value `c := unitLikeValue? d` introduces no local declaration,
and the new goal mentions `c` in place of the binder. The target `∀ (n : Nat) (u : PUnit), B n u`
leaves the goal `B n PUnit.unit` with the local `n`, assigned by `fun n u => ?g`.
`B n PUnit.unit` and `B n u` are definitionally equal by `unitLikeValue?`.
-/
partial def introCore (mvarId : MVarId) (max : Nat) (names : Array Name) (hygienic : Bool) :
    SymM (Array FVarId × MVarId) := do
  if max == 0 then return (#[], mvarId)
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
  Constructs `e #iₖ ... #i₁` for the binders of `subst` that are free variables, where `#i` is the
  de Bruijn index of the binder in the lambdas of `mkValueLoop`. This is helper function for
  constructing a value to assign to `mvarId`.
  -/
  let mkAppBVars (e : Expr) (subst : Array Expr) : Expr := Id.run do
    let mut e := e
    for h : j in [:subst.size] do
      if subst[j].isFVar then
        e := mkApp e (mkBVar (subst.size - 1 - j))
    return e
  /-
  Constructs a value to assign to `mvarId` using `mkValueLoop` and `mkAppBVars`.
  -/
  let mkValueAndAssign (subst fvars : Array Expr) (mvarId' : MVarId) : MetaM Unit := do
    if fvars.isEmpty then
      mvarId.assign (mkValueLoop 0 mvarDecl.type (mkMVar mvarId'))
      return
    let auxMVar ← mkFreshExprMVarAt mvarDecl.lctx mvarDecl.localInstances mvarDecl.type .syntheticOpaque
    let val := mkAppBVars auxMVar subst
    let val := mkValueLoop 0 mvarDecl.type val
    assignDelayedMVar auxMVar.mvarId! fvars mvarId'
    mvarId.assign val
  /-
  `subst` holds, for each binder introduced so far, its free variable or its `unitLikeValue?`.
  -/
  let finalize (lctx : LocalContext) (localInsts : LocalInstances) (subst : Array Expr) (type : Expr) : SymM (Array Expr × MVarId) := do
    if subst.isEmpty then
      return (#[], mvarId)
    let type ← instantiateRevS type subst
    let mvar' ← mkFreshExprMVarAt lctx localInsts type .syntheticOpaque mvarDecl.userName
    let mvarId' := mvar'.mvarId!
    let fvars := subst.filter (·.isFVar)
    mkValueAndAssign subst fvars mvarId'
    return (fvars, mvarId')
  let mkName (lctx : LocalContext) (binderName : Name) (i : Nat) : MetaM Name := do
    if h : i < names.size then
      return names[i]
    else
      mkFreshBinderNameForTacticCore lctx binderName hygienic
  let updateLocalInsts (localInsts : LocalInstances) (fvar : Expr) (type : Expr) : MetaM LocalInstances := do
    if let some className ← isClass? type then
      return localInsts.push { fvar, className }
    else
      return localInsts
  let rec visit (i : Nat) (lctx : LocalContext) (localInsts : LocalInstances) (fvars : Array Expr) (type : Expr) : SymM (Array Expr × MVarId) := do
    if i >= max then
      finalize lctx localInsts fvars type
    else match type with
    | .mdata _ type => visit i lctx localInsts fvars type
    | .forallE n type body bi =>
      let type ← instantiateRevS type fvars
      if let some c ← unitLikeValue? type then
        visit (i+1) lctx localInsts (fvars.push c) body
      else
        let fvarId     ← mkFreshFVarId
        let userName   ← mkName lctx n i
        let lctx       := lctx.mkLocalDecl fvarId userName type bi (.ofBinderName userName)
        let fvar       ← mkFVarS fvarId
        let fvars      := fvars.push fvar
        let localInsts ← updateLocalInsts localInsts fvar type
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
      let userName   ← mkName lctx n i
      let lctx       := lctx.mkLetDecl fvarId userName type value (kind := .ofBinderName userName)
      let fvar       ← mkFVarS fvarId
      let fvars      := fvars.push fvar
      let localInsts ← updateLocalInsts localInsts fvar type
      visit (i+1) lctx localInsts fvars body
    | _ =>
      if type.getAppFn.isMVar then
        let type ← instantiateRevS type fvars
        if let some type ← instantiateAssignedMVarHeadS? type then
          -- Introduces the remaining binders from the value of the metavariable.
          let mvarId ← if fvars.isEmpty then
            mvarId.setType type
            pure mvarId
          else
            pure (← finalize lctx localInsts fvars type).2
          let (fvars', mvarId) ←
            introCore mvarId (max - i) (names.extract i names.size) hygienic
          return (fvars.filter (·.isFVar) ++ fvars'.map mkFVar, mvarId)
      finalize lctx localInsts fvars type
  let (fvars, mvarId') ← visit 0 mvarDecl.lctx mvarDecl.localInstances #[] mvarDecl.type
  return (fvars.map (·.fvarId!), mvarId')

def hugeNat := 1000000

public inductive IntrosResult where
  | failed
  | goal (newDecls : Array FVarId) (mvarId : MVarId)

/--
Introduces leading binders (universal quantifiers and let-expressions) from the goal's target type.

If `names` is non-empty, introduces (at most) `names.size` binders using the provided names.
If `names` is empty, introduces all leading binders using names derived from the binder names;
`hygienic` then controls whether those names are inaccessible (see `introCore`). A binder over
a unit-like type such as `PUnit` or `True` introduces no local (see `introCore`).

Returns `.goal newDecls mvarId` with new introduced free variable Ids and the updated goal.
Returns `.failed` if no binder was introduced.
-/
public def intros (mvarId : MVarId) (names : Array Name := #[]) (hygienic : Bool := true) :
    SymM IntrosResult := do
  let result ← if names.isEmpty then
    introCore mvarId hugeNat #[] hygienic
  else
    introCore mvarId names.size names hygienic
  if result.1.isEmpty && result.2 == mvarId then
    return .failed
  return .goal result.1 result.2

/--
Introduces exactly `num` binders from the goal's target type.

Returns `.goal newDecls mvarId` if successful where `newDecls` are the introduced free variable IDs,
`mvarId` the updated goal.
Returns `.failed` if it was not possible to introduce `num` new local declarations.
-/
public def introN (mvarId : MVarId) (num : Nat) (hygienic : Bool := true) : SymM IntrosResult := do
  let result ← introCore mvarId num #[] hygienic
  unless result.1.size == num do
    return .failed
  return .goal result.1 result.2

end Lean.Meta.Sym
