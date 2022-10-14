/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.WHNF
import Lean.Meta.Transform
import Lean.Meta.SynthInstance
import Lean.Meta.AppBuilder

namespace Lean.Meta

/--
  Return true iff `declName` is one of the auxiliary definitions/projections
  used to implement coercions.
-/
def isCoeDecl (declName : Name) : Bool :=
  declName == ``Coe.coe || declName == ``CoeTC.coe || declName == ``CoeHead.coe ||
  declName == ``CoeTail.coe || declName == ``CoeHTCT.coe || declName == ``CoeDep.coe ||
  declName == ``CoeT.coe || declName == ``CoeFun.coe || declName == ``CoeSort.coe ||
  declName == ``Lean.Internal.liftCoeM || declName == ``Lean.Internal.coeM

/-- Expand coercions occurring in `e` -/
partial def expandCoe (e : Expr) : MetaM Expr :=
  withReducibleAndInstances do
    transform e fun e => do
      let f := e.getAppFn
      if f.isConst then
        let declName := f.constName!
        if isCoeDecl declName then
          if let some e ← unfoldDefinition? e then
            return .visit e.headBeta
      return .continue

register_builtin_option maxCoeSize : Nat := {
  defValue := 16
  descr    := "maximum number of instances used to construct an automatic coercion"
}

register_builtin_option autoLift : Bool := {
  defValue := true
  descr    := "insert monadic lifts (i.e., `liftM` and coercions) when needed"
}

def trySynthInstanceForCoe (cls : Expr) : MetaM (LOption Expr) := do
  trySynthInstance cls (some (maxCoeSize.get (← getOptions)))

/-- Coerces `expr` to `expectedType` using `CoeT`. -/
def coerceSimple? (expr expectedType : Expr) : MetaM (LOption Expr) := do
  let eType ← inferType expr
  let u ← getLevel eType
  let v ← getLevel expectedType
  let coeTInstType := mkAppN (mkConst ``CoeT [u, v]) #[eType, expr, expectedType]
  match ← trySynthInstanceForCoe coeTInstType with
  | .some inst =>
    let result ← expandCoe (mkAppN (mkConst ``CoeT.coe [u, v]) #[eType, expr, expectedType, inst])
    unless ← isDefEq (← inferType result) expectedType do
      throwError "could not coerce{indentExpr expr}\nto{indentExpr expectedType}\ncoerced expression has wrong type:{indentExpr result}"
    return .some result
  | .undef => return .undef
  | .none => return .none

/-- Coerces `expr` to a function type. -/
def coerceToFunction? (expr : Expr) : MetaM (Option Expr) := do
  let result ← try mkAppM ``CoeFun.coe #[expr] catch _ => return none
  let expanded ← expandCoe result
  unless (← whnf (← inferType expanded)).isForall do
    throwError "failed to coerce{indentExpr expr}\nto a function, after applying `CoeFun.coe`, result is still not a function{indentExpr expanded}\nthis is often due to incorrect `CoeFun` instances, the synthesized instance was{indentExpr result.appFn!.appArg!}"
  return expanded

/-- Coerces `expr` to a type. -/
def coerceToSort? (expr : Expr) : MetaM (Option Expr) := do
  let result ← try mkAppM ``CoeSort.coe #[expr] catch _ => return none
  let expanded ← expandCoe result
  unless (← whnf (← inferType expanded)).isSort do
    throwError "failed to coerce{indentExpr expr}\nto a type, after applying `CoeSort.coe`, result is still not a type{indentExpr expanded}\nthis is often due to incorrect `CoeSort` instances, the synthesized instance was{indentExpr result.appFn!.appArg!}"
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
  if (← isDefEq m n) then
    let some monadInst ← isMonad? n | return none
    try expandCoe (← mkAppOptM ``Lean.Internal.coeM #[m, α, β, none, monadInst, e]) catch _ => return none
  else if autoLift.get (← getOptions) then
    try
      -- Construct lift from `m` to `n`
      let monadLiftType ← mkAppM ``MonadLiftT #[m, n]
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
        let eNew ← expandCoe (mkAppN (Lean.mkConst ``Lean.Internal.liftCoeM [u_1, u_2, u_3]) #[m, n, α, β, monadLiftVal, coeTInstVal, monadInst, e])
        let eNewType ← inferType eNew
        unless (← isDefEq expectedType eNewType) do return none
        return some eNew -- approach 3 worked
    catch _ =>
      /- If `m` is not a monad, then we try to use `tryCoe?`. -/
      return none
  else
    return none

/-- Coerces `expr` to the type `expectedType`.
Returns `.some coerced` on successful coercion,
`.none` if the expression cannot by coerced to that type,
or `.undef` if we need more metavariable assignments. -/
def coerce? (expr expectedType : Expr) : MetaM (LOption Expr) := do
  if let some lifted ← coerceMonadLift? expr expectedType then
    return .some lifted
  if (← whnfR expectedType).isForall then
    if let some fn ← coerceToFunction? expr then
      if ← isDefEq (← inferType fn) expectedType then
        return .some fn
  coerceSimple? expr expectedType

end Lean.Meta
