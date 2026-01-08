/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.AppBuilder
import Lean.ExtraModUses
import Lean.ProjFns
import Lean.Meta.Transform
import Lean.Meta.WHNF
public section
namespace Lean.Meta
/--
Tags declarations to be unfolded during coercion elaboration.

This is mostly used to hide coercion implementation details and show the coerced result instead of
an application of auxiliary definitions (e.g. `CoeT.coe`, `Coe.coe`). This attribute only works on
reducible functions and instance projections.
-/
@[builtin_doc]
builtin_initialize coeDeclAttr : TagAttribute ←
  registerTagAttribute `coe_decl "auxiliary definition used to implement coercion (unfolded during elaboration)"

/--
Return true iff `declName` is one of the auxiliary definitions/projections used to implement
coercions.
-/
def isCoeDecl (env : Environment) (declName : Name) : Bool :=
  coeDeclAttr.hasTag env declName

/-- Recurse through projection functions (e.g. `(f a b c).fst.snd` => `f`) -/
private partial def recProjTarget (e : Expr) (nm : Name := e.getAppFn.constName!) : MetaM Name := do
  let some info ← getProjectionFnInfo? nm | return nm
  let target := e.getArgD info.numParams (.sort .zero)
  if target.getAppFn.isConst then
    recProjTarget target
  else
    return nm

/--
Expands coercions occurring in `e` and return the result together with a list of applied
`Coe` instances.
-/
partial def expandCoe (e : Expr) : MetaM (Expr × List Name) := StateT.run (s := ([] : List Name)) do
  withReducibleAndInstances do
    transform e fun e => do
      let f := e.getAppFn
      if f.isConst then
        let declName := f.constName!
        if isCoeDecl (← getEnv) declName then
          /-
          Unfolding an instance projection corresponds to unfolding the target of the projection
          (and then reducing the projection). Thus we can recursively visit projections before
          recording the declaration. We shouldn't need to record any other arguments because they
          should still appear after unfolding (unless there are unused variables in the instances).
          -/
          recordExtraModUseFromDecl (isMeta := false) (← recProjTarget e)
          if let some e' ← unfoldDefinition? e then
            /-
            If the unfolded coercion is an application of `Coe.coe` and its third argument is
            an application of a constant, record this constant's name.
            -/
            if declName = ``Coe.coe then
              if let some inst := e.getAppArgs[2]? then
                let g := inst.getAppFn
                if g.isConst then
                  let instName := g.constName!
                  StateT.set (instName :: (← StateT.get))
            return .visit e'.headBeta
      return .continue

register_builtin_option autoLift : Bool := {
  defValue := true
  descr    := "Insert monadic lifts (i.e., `liftM` and coercions) when needed."
}

/-- Coerces `expr` to `expectedType` using `CoeT`. -/
def coerceSimpleRecordingNames? (expr expectedType : Expr) : MetaM (LOption (Expr × List Name)) := do
  let eType ← inferType expr
  let u ← getLevel eType
  let v ← getLevel expectedType
  let coeTInstType := mkAppN (mkConst ``CoeT [u, v]) #[eType, expr, expectedType]
  match ← trySynthInstance coeTInstType with
  | .some inst =>
    let result ← expandCoe (mkAppN (mkConst ``CoeT.coe [u, v]) #[eType, expr, expectedType, inst])
    unless ← isDefEq (← inferType result.1) expectedType do
      throwError "Could not coerce{indentExpr expr}\nto{indentExpr expectedType}\ncoerced expression has wrong type:{indentExpr result.1}"
    return .some result
  | .undef => return .undef
  | .none => return .none

/-- Coerces `expr` to `expectedType` using `CoeT`. -/
def coerceSimple? (expr expectedType : Expr) : MetaM (LOption Expr) := do
  match ← coerceSimpleRecordingNames? expr expectedType with
  | .some (result, _) => return .some result
  | .none => return .none
  | .undef => return .undef

/-- Coerces `expr` to a function type. -/
def coerceToFunction? (expr : Expr) : MetaM (Option Expr) := do
  -- constructing expression manually because mkAppM wouldn't assign universe mvars
  let α ← inferType expr
  let u ← getLevel α
  let v ← mkFreshLevelMVar
  let γ ← mkFreshExprMVar (← mkArrow α (mkSort v))
  let .some inst ← trySynthInstance (mkApp2 (.const ``CoeFun [u,v]) α γ) | return none
  let (expanded, _) ← expandCoe (mkApp4 (.const ``CoeFun.coe [u,v]) α γ inst expr)
  unless (← whnf (← inferType expanded)).isForall do
    throwError m!"Failed to coerce{indentExpr expr}\nto a function: After applying `CoeFun.coe`, result is still not a function{indentExpr expanded}"
      ++ .hint' m!"This is often due to incorrect `CoeFun` instances; the synthesized instance was{indentExpr inst}"
  return expanded

/-- Coerces `expr` to a type. -/
def coerceToSort? (expr : Expr) : MetaM (Option Expr) := do
  -- constructing expression manually because mkAppM wouldn't assign universe mvars
  let α ← inferType expr
  let u ← getLevel α
  let v ← mkFreshLevelMVar
  let β ← mkFreshExprMVar (mkSort v)
  let .some inst ← trySynthInstance (mkApp2 (.const ``CoeSort [u,v]) α β) | return none
  let (expanded, _) ← expandCoe (mkApp4 (.const ``CoeSort.coe [u,v]) α β inst expr)
  unless (← whnf (← inferType expanded)).isSort do
    throwError m!"Failed to coerce{indentExpr expr}\nto a type: After applying `CoeSort.coe`, result is still not a type{indentExpr expanded}"
      ++ .hint' m!"This is often due to incorrect `CoeSort` instances; the synthesized instance was{indentExpr inst}"
  return expanded

/-- Return `some (m, α)` if `type` can be reduced to an application of the form `m α` using `[reducible]` transparency. -/
def isTypeApp? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← withReducible <| whnf type
  match type with
  | .app m α => return some ((← instantiateMVars m), (← instantiateMVars α))
  | _        => return none

/--
Return `true` if `type` is of the form `m α` where `m` is a `Monad`.
Note that we reduce `type` using transparency `[reducible]`.
-/
def isMonadApp (type : Expr) : MetaM Bool := do
  let some (m, _) ← isTypeApp? type | return false
  return (← isMonad? m).isSome

/--
Try coercions and monad lifts to make sure `e` has type `expectedType`.

If `expectedType` is of the form `n β`, we try monad lifts and other extensions.

Extensions for monads.

1. Try to unify `n` and `m`. If it succeeds, then we use
  ```
  coeM {m : Type u → Type v} {α β : Type u} [∀ a, CoeT α a β] [Monad m] (x : m α) : m β
  ```
  `n` must be a `Monad` to use this one.

2. If there is monad lift from `m` to `n` and we can unify `α` and `β`, we use
  ```
  liftM : ∀ {m : Type u_1 → Type u_2} {n : Type u_1 → Type u_3} [self : MonadLiftT m n] {α : Type u_1}, m α → n α
  ```
  Note that `n` may not be a `Monad` in this case. This happens quite a bit in code such as
  ```
  def g (x : Nat) : IO Nat := do
    IO.println x
    pure x

  def f {m} [MonadLiftT IO m] : m Nat :=
    g 10

  ```

3. If there is a monad lift from `m` to `n` and a coercion from `α` to `β`, we use
  ```
  liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u} [MonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β
  ```

Note that approach 3 does not subsume 1 because it is only applicable if there is a coercion from `α` to `β` for all values in `α`.
This is not the case for example for `pure $ x > 0` when the expected type is `IO Bool`. The given type is `IO Prop`, and
we only have a coercion from decidable propositions.  Approach 1 works because it constructs the coercion `CoeT (m Prop) (pure $ x > 0) (m Bool)`
using the instance `pureCoeDepProp`.

Note that, approach 2 is more powerful than `tryCoe`.
Recall that type class resolution never assigns metavariables created by other modules.
Now, consider the following scenario
```lean
def g (x : Nat) : IO Nat := ...
deg h (x : Nat) : StateT Nat IO Nat := do
v ← g x;
IO.Println v;
...
```
Let's assume there is no other occurrence of `v` in `h`.
Thus, we have that the expected of `g x` is `StateT Nat IO ?α`,
and the given type is `IO Nat`. So, even if we add a coercion.
```
instance {α m n} [MonadLiftT m n] {α} : Coe (m α) (n α) := ...
```
It is not applicable because TC would have to assign `?α := Nat`.
On the other hand, TC can easily solve `[MonadLiftT IO (StateT Nat IO)]`
since this goal does not contain any metavariables. And then, we
convert `g x` into `liftM $ g x`.
-/
def coerceMonadLift? (e expectedType : Expr) : MetaM (Option Expr) := do
  let expectedType ← instantiateMVars expectedType
  let eType ← instantiateMVars (← inferType e)
  let some (n, β) ← isTypeApp? expectedType | return none
  let some (m, α) ← isTypeApp? eType | return none
  -- Need to save and restore the state in case `m` and `n` are defeq but not monads to prevent this procedure from having side effects.
  let saved ← saveState
  if (← isDefEq m n) then
    let some monadInst ← isMonad? n | restoreState saved; return none
    try
      let (result, _) ← expandCoe (← mkAppOptM ``Lean.Internal.coeM #[m, α, β, none, monadInst, e])
      pure result
    catch _ => restoreState saved; return none
  else if autoLift.get (← getOptions) then
    try
      -- Construct lift from `m` to `n`
      -- Note: we cannot use mkAppM here because mkAppM does not assign universe metavariables,
      -- but we need to make sure that the domains of `m` and `n` have the same level.
      let .forallE _ (.sort um₁) (.sort um₂) _ ← whnf (← inferType m) | return none
      let .forallE _ (.sort un₁) (.sort un₂) _ ← whnf (← inferType n) | return none
      let u ← decLevel um₁
      let .true ← isLevelDefEq u (← decLevel un₁) | return none
      let v ← decLevel um₂
      let w ← decLevel un₂
      let monadLiftType := mkAppN (.const ``MonadLiftT [u, v, w]) #[m, n]
      let .some monadLiftVal ← trySynthInstance monadLiftType | return none
      let u_1 ← getDecLevel α
      let u_2 ← getDecLevel eType
      let u_3 ← getDecLevel expectedType
      let eNew := mkAppN (Lean.mkConst ``liftM [u_1, u_2, u_3]) #[m, n, monadLiftVal, α, e]
      let eNewType ← inferType eNew
      if (← isDefEq expectedType eNewType) then
        return some eNew -- approach 2 worked
      else
        let some monadInst ← isMonad? n | return none
        let u ← getLevel α
        let v ← getLevel β
        let coeTInstType := Lean.mkForall `a BinderInfo.default α <| mkAppN (mkConst ``CoeT [u, v]) #[α, mkBVar 0, β]
        let .some coeTInstVal ← trySynthInstance coeTInstType | return none
        let (eNew, _) ← expandCoe (mkAppN (Lean.mkConst ``Lean.Internal.liftCoeM [u_1, u_2, u_3]) #[m, n, α, β, monadLiftVal, coeTInstVal, monadInst, e])
        let eNewType ← inferType eNew
        unless (← isDefEq expectedType eNewType) do return none
        return some eNew -- approach 3 worked
    catch _ =>
      /- If `m` is not a monad, then we try to use `tryCoe?`. -/
      return none
  else
    return none

/--
Coerces `expr` to the type `expectedType`.
Returns `.some (coerced, appliedCoeDecls)` on successful coercion,
`.none` if the expression cannot by coerced to that type,
or `.undef` if we need more metavariable assignments.

`appliedCoeDecls` is a list of names representing the names of the `Coe` instances that were
applied.
-/
def coerceCollectingNames? (expr expectedType : Expr) : MetaM (LOption (Expr × List Name)) := do
  if let some lifted ← coerceMonadLift? expr expectedType then
    return .some (lifted, [])
  if (← whnfR expectedType).isForall then
    if let some fn ← coerceToFunction? expr then
      if ← isDefEq (← inferType fn) expectedType then
        return .some (fn, [])
  coerceSimpleRecordingNames? expr expectedType

/--
Coerces `expr` to the type `expectedType`.
Returns `.some coerced` on successful coercion,
`.none` if the expression cannot by coerced to that type,
or `.undef` if we need more metavariable assignments.
-/
def coerce? (expr expectedType : Expr) : MetaM (LOption Expr) := do
  match ← coerceCollectingNames? expr expectedType with
  | .some (result, _) => return .some result
  | .none => return .none
  | .undef => return .undef

end Lean.Meta
