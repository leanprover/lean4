/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind
import Init.Simproc
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Grind.PropagatorAttr

namespace Lean.Meta.Grind
/-!
Support for `match`-expressions with overlapping patterns.
Recall that when a `match`-expression has overlapping patterns, some of its equation theorems are
conditional. Let's consider the following example
```
inductive S where
  | mk1 (n : Nat)
  | mk2 (n : Nat) (s : S)
  | mk3 (n : Bool)
  | mk4 (s1 s2 : S)

def f (x y : S) :=
  match x, y with
  | .mk1 a, c => a + 2
  | a, .mk2 1 (.mk4 b c) => 3
  | .mk3 a, .mk4 b c => 4
  | a, b => 5
```

The `match`-expression in this example has 4 equations. The second and fourth are conditional.
```
f.match_1.eq_2
  (motive : S → S → Sort u) (a b c : S)
  (h_1 : (a : Nat) → (c : S) → motive (S.mk1 a) c)
  (h_2 : (a b c : S) → motive a (S.mk2 1 (b.mk4 c)))
  (h_3 : (a : Bool) → (b c : S) → motive (S.mk3 a) (b.mk4 c))
  (h_4 : (a b : S) → motive a b) :
  (∀ (a_1 : Nat),  a = S.mk1 a_1 → False) → -- <<< Condition stating it is not the first case
  f.match_1 motive a (S.mk2 1 (b.mk4 c)) h_1 h_2 h_3 h_4 = h_2 a b c

f.match_1.eq_4
  (motive : S → S → Sort u) (a b : S)
  (h_1 : (a : Nat) → (c : S) → motive (S.mk1 a) c)
  (h_2 : (a b c : S) → motive a (S.mk2 1 (b.mk4 c)))
  (h_3 : (a : Bool) → (b c : S) → motive (S.mk3 a) (b.mk4 c))
  (h_4 : (a b : S) → motive a b) :
  (∀ (a_1 : Nat), a = S.mk1 a_1 → False) →  -- <<< Condition stating it is not the first case
  (∀ (b_1 c : S), b = S.mk2 1 (b_1.mk4 c) → False) →  -- <<< Condition stating it is not the second case
  (∀ (a_1 : Bool) (b_1 c : S), a = S.mk3 a_1 → b = b_1.mk4 c → False) → -- -- <<< Condition stating it is not the third case
  f.match_1 motive a b h_1 h_2 h_3 h_4 = h_4 a b
```
In the two equational theorems above, we have the following conditions.
```
- `(∀ (a_1 : Nat),  a = S.mk1 a_1 → False)`
- `(∀ (b_1 c : S), b = S.mk2 1 (b_1.mk4 c) → False)`
- `(∀ (a_1 : Bool) (b_1 c : S), a = S.mk3 a_1 → b = b_1.mk4 c → False)`
```
When instantiating the equations (and `match`-splitter), we wrap the conditions with the gadget `Grind.MatchCond`.
This gadget is used for implementing truth-value propagation. See the propagator `propagateMatchCond` below.
For example, given a condition `C` of the form `Grind.MatchCond (∀ (a : Nat),  t = S.mk1 a → False)`,
if `t` is merged with an equivalence class containing `S.mk2 n s`, then `C` is asseted to `true` by `propagateMatchCond`.

This module also provides auxiliary functions for detecting congruences between `match`-expression conditions.
See function `collectMatchCondLhssAndAbstract`.

Remark: This note highlights that the representation used for encoding `match`-expressions with
overlapping patterns is far from ideal for the `grind` module which operates with equivalence classes
and does not perform substitutions like `simp`.  While modifying how `match`-expressions are encoded in Lean
would require major refactoring and affect many modules, this issue is important to acknowledge.
A different representation could simplify `grind`, but it could add extra complexity to other modules.
-/

/--
Returns `Grind.MatchCond e`.
Recall that `Grind.MatchCond` is an identity function,
but the following simproc is used to prevent the term `e` from being simplified,
and we have special support for propagating is truth value.
-/
def markAsMatchCond (e : Expr) : Expr :=
  mkApp (mkConst ``Grind.MatchCond) e

builtin_dsimproc_decl reduceMatchCond (Grind.MatchCond _) := fun e => do
  let_expr Grind.MatchCond _ ← e | return .continue
  return .done e

/-- Adds `reduceMatchCond` to `s` -/
def addMatchCond (s : Simprocs) : CoreM Simprocs := do
  s.add ``reduceMatchCond (post := false)

/--
Returns `some (α?, lhs, rhs)` if `e` is of the form
- `Eq _ lhs rhs` (`?α := none`), or
- `HEq α lhs _ rhs` (`α? := some α`)
-/
private def isEqHEq? (e : Expr) : Option (Option Expr × Expr × Expr) :=
  match_expr e with
  | Eq _ lhs rhs => some (none, lhs, rhs)
  | HEq α lhs _ rhs => some (some α, lhs, rhs)
  | _ => none

/--
Given `e` a `match`-expression condition, returns the left-hand side
of the ground equations, and its type if it is the left-hand side of
a heterogeneous equality.
-/
private def collectMatchCondLhss (e : Expr) : Array (Expr × Option Expr) := Id.run do
  let mut r := #[]
  let mut e := e
  repeat
    let .forallE _ d b _ := e | return r
    if let some (α?, lhs, _) := isEqHEq? d then
      unless lhs.hasLooseBVars do
        r := r.push (lhs, α?)
    e := b
  return r

/--
Replaces the left-hand side of an equality (or heterogeneous equality) `e` with `lhsNew`.
-/
private def replaceLhs? (e : Expr) (lhsNew : Expr) (ty? : Option Expr) : Option Expr :=
  match_expr e with
  | f@Eq α lhs rhs => if lhs.hasLooseBVars then none else some (mkApp3 f α lhsNew rhs)
  | f@HEq _ lhs β rhs => if lhs.hasLooseBVars then none else some (mkApp4 f ty?.get! lhsNew β rhs)
  | _ => none

/--
Given `e` a `match`-expression condition, returns the left-hand side
of the ground equations, **and** function application that abstracts the left-hand sides.
As an example, assume we have a `match`-expression condition `C₁` of the form
```
Grind.MatchCond (∀ y₁ y₂ y₃, t = .mk₁ y₁ → s = .mk₂ y₂ y₃ → False)
```
then the result returned by this function is
```
(#[t, s], (fun x₁ x₂ => (∀ y₁ y₂ y₃, x₁ = .mk₁ y₁ → x₂ = .mk₂ y₂ y₃ → False)) t s)
```
Note that the returned expression is definitionally equal to `C₁`.
We use this expression to detect whether two different `match`-expression conditions are
congruent.
For example, suppose we also have the `match`-expression `C₂` of the form
```
Grind.MatchCond (∀ y₁ y₂ y₃, a = .mk₁ y₁ → b = .mk₂ y₂ y₃ → False)
```
This function would return
```
(#[a, b], (fun x₁ x₂ => (∀ y₁ y₂ y₃, x₁ = .mk₁ y₁ → x₂ = .mk₂ y₂ y₃ → False)) a b)
```
Note that the lambda abstraction is identical to the first one. Let's call it `l`.
Thus, we can write the two pairs above as
- `(#[t, s], l t s)`
- `(#[a, b], l a b)`
Moreover, `C₁` is definitionally equal to `l t s`, and `C₂` is definitionally equal to `l a b`.
Then, if `grind` infers that `t = a` and `s = b`, it will detect that `l t s` and `l a b` are
equal by congruence, and consequently `C₁` is equal to `C₂`.

Gruesome details for heterogenenous equalities.

When pattern matching on indexing families, the generated conditions often use heterogenenous equalities. Here is an example:
```
(∀ (x : Vec α 0), n = 0 → HEq as Vec.nil → HEq bs x → False)
```
In this case, it is not sufficient to abstract the left-hand side. We also have
to abstract its type. The following is produced in this case.
```
(#[n, Vec α n, as, Vec α n, bs],
 (fun (x_0 : Nat) (ty_1 : Type u_1) (x_1 : ty_1) (ty_2 : Type u_1) (x_2 : ty_2) =>
    ∀ (x : Vec α 0), x_0 = 0 → HEq x_1 Vec.nil → HEq x_2 x → False)
 n (Vec α n) as (Vec α n) bs)
```
The example makes it clear why this is needed, `as` and `bs` depend on `n`.
Note that we can abstract the type without introducing typer errors because
heterogenenous equality is used for `as` and `bs`.
-/
def collectMatchCondLhssAndAbstract (matchCond : Expr) : GoalM (Array Expr × Expr) := do
  let_expr Grind.MatchCond e := matchCond | return (#[], matchCond)
  let lhssαs := collectMatchCondLhss e
  let rec go (i : Nat) (xs : Array Expr) (tys : Array (Option Expr)) (tysxs : Array Expr) (args : Array Expr) : GoalM (Array Expr × Expr) := do
    if h : i < lhssαs.size then
      let (lhs, α?) := lhssαs[i]
      if let some α := α? then
        withLocalDeclD ((`ty).appendIndexAfter i) (← inferType α) fun ty =>
        withLocalDeclD ((`x).appendIndexAfter i) ty fun x =>
          go (i+1) (xs.push x) (tys.push ty) (tysxs.push ty |>.push x) (args.push α |>.push lhs)
      else
        withLocalDeclD ((`x).appendIndexAfter i) (← inferType lhs) fun x =>
          go (i+1) (xs.push x) (tys.push none) (tysxs.push x) (args.push lhs)
    else
      let rec replaceLhss (e : Expr) (i : Nat) : Expr := Id.run do
        let .forallE _ d b _ := e | return e
        if h : i < xs.size then
          if let some dNew := replaceLhs? d xs[i] tys[i]! then
            return e.updateForallE! dNew (replaceLhss b (i+1))
          else
            return e.updateForallE! d (replaceLhss b i)
        else
          return e
      let eAbst := replaceLhss e 0
      let eLam  ← mkLambdaFVars tysxs eAbst
      let e' := mkAppN eLam args
      return (args, ← shareCommon e')
  go 0 #[] #[] #[] #[]

/--
Helper function for `isSatisfied`.
See `isSatisfied`.
-/
private partial def isMatchCondFalseHyp (e : Expr) : GoalM Bool := do
  let some (_, lhs, rhs) := isEqHEq? e | return false
  isFalse lhs rhs
where
  isFalse (lhs rhs : Expr) : GoalM Bool := do
    if lhs.hasLooseBVars then return false
    let root ← getRootENode lhs
    if root.ctor then
      let some ctorLhs ← isConstructorApp? root.self | return false
      let some ctorRhs ← isConstructorApp? rhs | return false
      if ctorLhs.name ≠ ctorRhs.name then return true
      let lhsArgs := root.self.getAppArgs
      let rhsArgs := rhs.getAppArgs
      for i in [ctorLhs.numParams : ctorLhs.numParams + ctorLhs.numFields] do
        if (← isFalse lhsArgs[i]! rhsArgs[i]!) then
          return true
      return false
    else if root.interpreted then
      if rhs.hasLooseBVars then return false
      unless (← isLitValue rhs) do return false
      return (← normLitValue root.self) != (← normLitValue rhs)
    else
      return false

/--
Returns `true` if `e` is a `Grind.MatchCond`, and it has been satifisfied.
Recall that we use `Grind.MatchCond` to annotate conditional `match`-equations.
Consider the following example:
```
inductive S where
  | mk1 (n : Nat)
  | mk2 (n : Nat) (s : S)
  | mk3 (n : Bool)
  | mk4 (s1 s2 : S)

def f (x y : S) :=
  match x, y with
  | .mk1 _, _ => 2
  | _, .mk2 1 (.mk4 _ _) => 3
  | .mk3 _, _ => 4
  | _, _ => 5
```
The `match`-expression in the example above has overlapping patterns and
consequently produces conditional `match` equations. Thus, `grind` generates
the following auxiliary `Grind.MatchCond` terms for an application `f a b`:
- `Grind.MatchCond (∀ (n : Nat), a = S.mk1 n → False)`
- `Grind.MatchCond (∀ (s1 s2 : S), b = S.mk2 1 (s1.mk4 s2) → False)`
- `Grind.MatchCond (∀ (n : Bool), a = S.mk3 n → False)`

`isSatisfied` uses the fact that constructor applications and literal values
are always the root of their equivalence classes.
-/
private partial def isStatisfied (e : Expr) : GoalM Bool := do
  let_expr Grind.MatchCond e ← e | return false
  let mut e := e
  repeat
    let .forallE _ d b _ := e | break
    if (← isMatchCondFalseHyp d) then
      trace[grind.debug.matchCond] "satifised{indentExpr e}\nthe following equality is false{indentExpr d}"
      return true
    e := b
  return false

/-- Constructs a proof for a satisfied `match`-expression condition. -/
private partial def mkMatchCondProof? (e : Expr) : GoalM (Option Expr) := do
  let_expr Grind.MatchCond f ← e | return none
  forallTelescopeReducing f fun xs _ => do
    for x in xs do
      let type ← inferType x
      if (← isMatchCondFalseHyp type) then
        trace[grind.debug.matchCond] ">>> {type}"
        let some h ← go? x | pure ()
        return some (← mkLambdaFVars xs h)
    return none
where
  go? (h : Expr) : GoalM (Option Expr) := do
    trace[grind.debug.matchCond] "go?: {← inferType h}"
    let some (α?, lhs, rhs) := isEqHEq? (← inferType h)
      | return none
    let target ← (← get).mvarId.getType
    let root ← getRootENode lhs
    let isHEq := α?.isSome
    let h ← if isHEq then
      mkEqOfHEq (← mkHEqTrans (← mkHEqProof root.self lhs) h)
    else
      mkEqTrans (← mkEqProof root.self lhs) h
    if root.ctor then
      let some ctorLhs ← isConstructorApp? root.self | return none
      let some ctorRhs ← isConstructorApp? rhs | return none
      let h ← mkNoConfusion target h
      if ctorLhs.name ≠ ctorRhs.name then
        return some h
      else
        let .forallE _ k _ _ ← whnfD (← inferType h)
          | return none
        forallTelescopeReducing k fun xs _ => do
          for x in xs do
            let some hx ← go? x | pure ()
            return some (mkApp h (← mkLambdaFVars xs hx))
          return none
    else if root.interpreted then
      if (← normLitValue root.self) != (← normLitValue rhs) then
        let hne ← mkDecideProof (mkNot (← mkEq root.self rhs))
        return some (mkApp hne h)
      else
        return none
    else
      return none

/-- Propagates `MatchCond` upwards -/
builtin_grind_propagator propagateMatchCond ↑Grind.MatchCond := fun e => do
  trace[grind.debug.matchCond] "visiting{indentExpr e}"
  if !(← isStatisfied e) then return ()
  let some h ← mkMatchCondProof? e
     | reportIssue m!"failed to construct proof for{indentExpr e}"; return ()
  trace[grind.debug.matchCond] "{← inferType h}"
  pushEqTrue e <| mkEqTrueCore e h

end Lean.Meta.Grind
