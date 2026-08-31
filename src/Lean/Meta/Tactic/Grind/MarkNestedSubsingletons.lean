/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Init.Grind.Util
import Lean.Meta.Sym.Util
import Lean.Meta.Tactic.Grind.Util
public section
namespace Lean.Meta.Grind

private abbrev M := StateRefT (Std.HashMap ExprPtr Expr) GrindM

def isMarkedSubsingletonConst (e : Expr) : Bool := Id.run do
  let .const declName _ := e | false
  return declName == ``Grind.nestedProof || declName == ``Grind.nestedDecidable

def isMarkedSubsingletonApp (e : Expr) : Bool :=
  /-
  Remark: we must check `e`s arity because we may have over-applied `Grind.nestedProof` applications.
  These over-applied applications have to be re-marked. Here is an example from test `grind_over_applied_nestedProof.lean`
  ```
  ‹∀ (a : Option α), x = some a → ∀ (a_2 : α), a = some a_2 → p a_2› val (join_pmap_eq_pmap_join._proof_1_2 val h_1))
  ```
  -/
  isMarkedSubsingletonConst e.getAppFn && e.getAppNumArgs == 2

/-- Returns `some p` if `e` is of the form `Decidable p` -/
private def isDecidable (e : Expr) : MetaM (Option Expr) := do
  match_expr (← whnfCore e) with
  | Decidable p => return some p
  | _ => return none

/-- Result of `isProofOrDecidableQuick`. -/
private inductive QuickResult where
  | no | proof | decidable | undef

/--
Classifies a term from its (syntactically known) type `rt`:
- `.decidable` if `rt` is a `Decidable`-application,
- `.proof` if `rt` is definitely a proposition,
- `.no` if `rt` is definitely neither a proposition nor reducible by `whnfCore` to a
  `Decidable`-application: sorts, dependent arrows, and applications headed by an inductive type,
- `.undef` otherwise.

`rt` may contain loose bound variables referring to instantiated binders; all checks only
inspect the head symbols, so they are not affected (`isPropQuick` returns `.undef` on them).
-/
private def classifyResultType (rt : Expr) : MetaM QuickResult := do
  if rt.isAppOf ``Decidable then
    return .decidable
  match (← isPropQuick rt) with
  | .true  => return .proof
  | .undef => return .undef
  | .false =>
    match rt with
    | .sort .. | .forallE .. => return .no
    | _ =>
      let .const declName _ := rt.getAppFn | return .undef
      if (← getConstInfo declName) matches .inductInfo .. then
        return .no
      else
        return .undef

/--
Given the type `headType` of the head of an application with arguments `args`, peels
`args.size` binders and classifies the resulting type using `classifyResultType`.
When the resulting type is one of the peeled binder variables (e.g., the polymorphic
result `γ` of `HAdd.hAdd`), it is resolved using the corresponding argument, which is
the actual result type.
-/
private def classifyArrow (headType : Expr) (args : Array Expr) : MetaM QuickResult :=
  go headType 0
where
  go (type : Expr) (i : Nat) : MetaM QuickResult := do
    if i == args.size then
      match type with
      | .bvar idx =>
        -- de Bruijn variable `idx` refers to the peeled binder instantiated by `args[i - 1 - idx]`
        if h : idx < i ∧ i - 1 - idx < args.size then
          classifyResultType args[i - 1 - idx]
        else
          return .undef
      | _ => classifyResultType type
    else
      match type with
      | .forallE _ _ b _ => go b (i+1)
      | .mdata _ b => go b i
      | _ => return .undef

/--
An "approximate" classifier for whether `e` is a proof, a `Decidable` instance, definitely
neither, or unknown. It follows the approximation strategy of `Lean.Meta.isProofQuick`,
extended with the `Decidable` case needed by `markNestedSubsingletons`.
The definite answers agree with the `isProp (← inferType e)` / `isDecidable (← inferType e)`
checks performed by `isProofOrDecidable`; `.undef` falls back to them.
-/
private partial def isProofOrDecidableQuick (e : Expr) : MetaM QuickResult := do
  match e with
  | .lit .. | .sort .. | .forallE .. => return .no
  | .bvar .. | .mvar .. | .proj .. => return .undef
  | .mdata _ b => isProofOrDecidableQuick b
  | .letE _ _ _ b _ => isProofOrDecidableQuick b
  | .lam _ _ b _ =>
    -- The type of a lambda is a dependent arrow: never a `Decidable`-application, and a
    -- proposition iff the type of the body is one.
    match (← isProofOrDecidableQuick b) with
    | .proof => return .proof
    | .undef => return .undef
    | _ => return .no
  | .fvar fvarId => classifyResultType (← fvarId.getType)
  | .const declName lvls => classifyResultType ((← getConstInfo declName).instantiateTypeLevelParams lvls)
  | .app .. =>
    match e.getAppFn with
    | .const declName lvls => classifyArrow ((← getConstInfo declName).instantiateTypeLevelParams lvls) e.getAppArgs
    | .fvar fvarId => classifyArrow (← fvarId.getType) e.getAppArgs
    | _ => return .undef

private inductive ProofOrDecidableResult where
  | no
  | proof (type : Expr)
  | decidable (p : Expr)

/--
Returns whether `e` is a proof (together with its type), a `Decidable` instance (together
with the decided proposition), or neither. Uses `isProofOrDecidableQuick` to avoid the
`inferType` call in the common case where `e` is definitely neither.
-/
private def isProofOrDecidable (e : Expr) : MetaM ProofOrDecidableResult := do
  match (← isProofOrDecidableQuick e) with
  | .no => return .no
  | .proof => return .proof (← inferType e)
  | .decidable | .undef =>
    let type ← inferType e
    if (← Meta.isProp type) then
      return .proof type
    else if let some p ← isDecidable type then
      return .decidable p
    else
      return .no

/--
Wrap nested proofs and decidable instances in `e` with `Lean.Grind.nestedProof` and `Lean.Grind.nestedDecidable`-applications.
Recall that the congruence closure module has special support for them.
-/
-- TODO: consider other subsingletons in the future? We decided to not support them to avoid the overhead of
-- synthesizing `Subsingleton` instances.
partial def markNestedSubsingletons (e : Expr) : GrindM Expr := do profileitM Exception "grind mark subsingleton" (← getOptions) do
  visit e |>.run' {}
where
  visit (e : Expr) : M Expr := do
    if isMarkedSubsingletonApp e then
      return e -- `e` is already marked
    -- check whether result is cached
    if let some r := (← get).get? { expr := e } then
      return r
    -- check whether `e` is a proof or a `Decidable` instance
    match (← isProofOrDecidable e) with
    | .proof type =>
      let e' := mkApp2 (mkConst ``Grind.nestedProof) (← preprocess type) e
      modify fun s => s.insert { expr := e } e'
      return e'
    | .decidable p =>
      let e' := mkApp2 (mkConst ``Grind.nestedDecidable) (← preprocess p) e
      modify fun s => s.insert { expr := e } e'
      return e'
    | .no => pure ()
    /-
    Remark: we have to process `Expr.proj` since we only
    fold projections later during term internalization
    Remark: let-expressions are zeta-reduced.
    Remark: We used to not go inside binders because `grind` does not process them, but
    some of the proofs nested in binders may be exposed for other preprocessing steps later.
    So, we decided to mark all of them.
    -/
    unless e.isApp || e.isForall || e.isLambda || e.isProj || e.isMData do
      return e
    let e' ← match e with
      | .app .. => e.withApp fun f args => do
        let mut modified := false
        let mut args := args.toVector
        for h : i in *...args.size do
          let arg := args[i]
          let arg' ← visit arg
          unless isSameExpr arg arg' do
            args := args.set i arg'
            modified := true
        if modified then
          pure <| mkAppN f args.toArray
        else
          pure e
      | .proj _ _ b =>
        pure <| e.updateProj! (← visit b)
      | .mdata _ b =>
        pure <| e.updateMData! (← visit b)
      | .forallE .. => visitForall e
      | .lam .. => visitLambda e
      | _ => unreachable!
    modify fun s => s.insert { expr := e } e'
    return e'

  visitLambda (root : Expr) : M Expr := do
    let rec loop (e : Expr) (fvars : Array Expr := #[]) (modified := false) : M Expr := do
      match e with
      | .lam n d b c =>
        let d := d.instantiateRev fvars
        let d' ← visit d
        withLocalDecl n c d' fun x =>
          loop b (fvars.push x) (modified || !isSameExpr d d')
      | e =>
        let e := e.instantiateRev fvars
        let e' ← visit e
        if modified || !isSameExpr e e' then
          mkLambdaFVars fvars e'
        else
          return root
    loop root

  visitForall (root : Expr) : M Expr := do
    let rec loop (e : Expr) (fvars : Array Expr := #[]) (modified := false) : M Expr := do
      match e with
      | .forallE n d b c =>
        let d := d.instantiateRev fvars
        let d' ← visit d
        withLocalDecl n c d' fun x =>
          loop b (fvars.push x) (modified || !isSameExpr d d')
      | e =>
        let e := e.instantiateRev fvars
        let e' ← visit e
        if modified || !isSameExpr e e' then
          mkForallFVars fvars e'
        else
          return root
    loop root

  preprocess (e : Expr) : M Expr := do
    /-
    **Note**: We must use `instantiateMVars` here because this function is called using the result of `inferType`.
    -/
    let e ← instantiateMVars e
    /-
    We must unfold reducible constants occurring in `prop` because the congruence closure
    module in `grind` assumes they have been expanded.
    See `grind_mark_nested_proofs_bug.lean` for an example.
    TODO: We may have to normalize `prop` too.
    -/
    /- We must also apply beta-reduction to improve the effectiveness of the congruence closure procedure. -/
    let e ← Core.betaReduce e
    let e ← Sym.unfoldReducible e
    /- We must mask proofs occurring in `prop` too. -/
    let e ← visit e
    let e ← eraseIrrelevantMData e
    /- We must fold kernel projections like it is done in the preprocessor. -/
    let e ← foldProjs e
    Sym.normalizeLevels e

private def markNestedProof (e : Expr) : M Expr := do
  let prop ← inferType e
  let prop ← markNestedSubsingletons.preprocess prop
  return mkApp2 (mkConst ``Grind.nestedProof) prop e

/--
Given a proof `e`, mark it with `Lean.Grind.nestedProof`
-/
def markProof (e : Expr) : GrindM Expr := do
  if e.isAppOf ``Grind.nestedProof then
    return e -- `e` is already marked
  else
    markNestedProof e |>.run' {}

end Lean.Meta.Grind
