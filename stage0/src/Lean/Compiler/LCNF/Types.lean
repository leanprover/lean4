/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.InferType

namespace Lean.Compiler

scoped notation:max "◾" => lcErased

namespace LCNF

def erasedExpr := mkConst ``lcErased

def _root_.Lean.Expr.isErased (e : Expr) :=
  e.isAppOf ``lcErased

def isPropFormerTypeQuick : Expr → Bool
  | .forallE _ _ b _ => isPropFormerTypeQuick b
  | .sort .zero => true
  | _ => false

/--
Return true iff `type` is `Prop` or `As → Prop`.
-/
partial def isPropFormerType (type : Expr) : MetaM Bool := do
  match isPropFormerTypeQuick type with
  | true => return true
  | false => go type #[]
where
  go (type : Expr) (xs : Array Expr) : MetaM Bool := do
    match type with
    | .sort .zero => return true
    | .forallE n d b c => Meta.withLocalDecl n c (d.instantiateRev xs) fun x => go b (xs.push x)
    | _ =>
      let type ← Meta.whnfD (type.instantiateRev xs)
      match type with
      | .sort .zero => return true
      | .forallE .. => go type #[]
      | _ => return false

/--
Return true iff `e : Prop` or `e : As → Prop`.
-/
def isPropFormer (e : Expr) : MetaM Bool := do
  isPropFormerType (← Meta.inferType e)

/-!
The code generator uses a format based on A-normal form.
This normal form uses many let-expressions and it is very convenient for
applying compiler transformations. However, it creates a few issues
in a dependently typed programming language.

- Many casts are needed.
- It is too expensive to ensure we are not losing typeability when creating join points
  and simplifying let-values
- It may not be possible to create a join point because the resulting expression is
  not type correct. For example, suppose we are trying to create a join point for
  making the following `match` terminal.
  ```
  let x := match a with | true => b | false => c;
  k[x]
  ```
  and want to transform this code into
  ```
  let jp := fun x => k[x]
  match a with
  | true => jp b
  | false => jp c
  ```
  where `jp` is a new join point (i.e., a local function that is always fully applied and
  tail recursive). In many examples in the Lean code-base, we have to skip this transformation
  because it produces a type-incorrect term. Recall that types/propositions in `k[x]` may rely on
  the fact that `x` is definitionally equal to `match a with ...` before the creation of
  the join point.

Thus, in the first code generator pass, we convert types into a `LCNFType` (Lean Compiler Normal Form Type).
The method `toLCNFType` produces a type with the following properties:

- All constants occurring in the result type are inductive datatypes.
- The arguments of type formers are type formers, or `◾`. We use `◾` to denote erased information.
- All type definitions are expanded. If reduction gets stuck, it is replaced with `◾`.

Remark: you can view `◾` occurring in a type position as the "any type".
Remark: in our runtime, `◾` is represented as `box(0)`.

The goal is to preserve as much information as possible and avoid the problems described above.
Then, we don't have `let x := v; ...` in LCNF code when `x` is a type former.
If the user provides a `let x := v; ...` where x is a type former, we can always expand it when
converting into LCNF.
Thus, given a `let x := v, ...` in occurring in LCNF, we know `x` cannot occur in any type since it is
not a type former.

We try to preserve type information because they unlock new optimizations, and we can type check
the result produced by each code generator step.


Below, we provide some example programs and their erased variants:
-- 1. Source type: `f: (n: Nat) -> (tupleN Nat n)`.
      LCNF type: `f: Nat -> ◾`.
      We convert the return type `(tupleN Nat n) to `◾`, since we cannot reduce
      `(tupleN Nat n)` to a term of the form `(InductiveTy ...)`.

-- 2. Source type: `f: (n: Nat) (fin: Fin n) -> (tupleN Nat fin)`.
      LCNF type: `f: Nat -> Fin ◾ -> ◾`.
      Since `(Fin n)` has dependency on `n`, we erase the `n` to get the
      type `(Fin ◾)`.
-/

open Meta in
/--
Convert a Lean type into a LCNF type used by the code generator.
-/
partial def toLCNFType (type : Expr) : MetaM Expr := do
  if (← isProp type) then
    return erasedExpr
  let type ← whnfEta type
  match type with
  | .sort u     => return .sort u
  | .const ..   => visitApp type #[]
  | .lam n d b bi =>
    withLocalDecl n bi d fun x => do
      let d ← toLCNFType d
      let b ← toLCNFType (b.instantiate1 x)
      if b.isErased then
        return b
      else
        return Expr.lam n d (b.abstract #[x]) bi
  | .forallE .. => visitForall type #[]
  | .app ..  => type.withApp visitApp
  | .fvar .. => visitApp type #[]
  | _        => return erasedExpr
where
  whnfEta (type : Expr) : MetaM Expr := do
    let type ← whnf type
    let type' := type.eta
    if type' != type then
      whnfEta type'
    else
      return type

  visitForall (e : Expr) (xs : Array Expr) : MetaM Expr := do
    match e with
    | .forallE n d b bi =>
      let d := d.instantiateRev xs
      withLocalDecl n bi d fun x => do
        let d := (← toLCNFType d).abstract xs
        return .forallE n d (← visitForall b (xs.push x)) bi
    | _ =>
      let e ← toLCNFType (e.instantiateRev xs)
      return e.abstract xs

  visitApp (f : Expr) (args : Array Expr) := do
    let fNew ← match f with
      | .const declName us =>
        let .inductInfo _ ← getConstInfo declName | return erasedExpr
        pure <| .const declName us
      | .fvar .. => pure f
      | _ => return erasedExpr
    let mut result := fNew
    for arg in args do
      if (← isProp arg) then
        result := mkApp result erasedExpr
      else if (← isPropFormer arg) then
        result := mkApp result erasedExpr
      else if (← isTypeFormer arg) then
        result := mkApp result (← toLCNFType arg)
      else
        result := mkApp result erasedExpr
    return result

mutual

partial def joinTypes (a b : Expr) : Expr :=
  joinTypes? a b |>.getD erasedExpr

partial def joinTypes? (a b : Expr) : Option Expr := do
  if a.isErased || b.isErased then
    return erasedExpr -- See comment at `compatibleTypes`.
  else if a == b then
    return a
  else
    let a' := a.headBeta
    let b' := b.headBeta
    if a != a' || b != b' then
      joinTypes? a' b'
    else
      match a, b with
      | .mdata _ a, b => joinTypes? a b
      | a, .mdata _ b => joinTypes? a b
      | .app f a, .app g b =>
        (do return .app (← joinTypes? f g) (← joinTypes? a b))
         <|>
        return erasedExpr
      | .forallE n d₁ b₁ _, .forallE _ d₂ b₂ _ =>
        (do return .forallE n (← joinTypes? d₁ d₂) (joinTypes b₁ b₂) .default)
        <|>
        return erasedExpr
      | .lam n d₁ b₁ _, .lam _ d₂ b₂ _ =>
        (do return .lam n (← joinTypes? d₁ d₂) (joinTypes b₁ b₂) .default)
        <|>
        return erasedExpr
      | _, _ => return erasedExpr

end

/--
Return `true` if `type` is a LCNF type former type.

Remark: This is faster than `Lean.Meta.isTypeFormer`, as this
        assumes that the input `type` is an LCNF type.
-/
partial def isTypeFormerType (type : Expr) : Bool :=
  match type.headBeta with
  | .sort .. => true
  | .forallE _ _ b _ => isTypeFormerType b
  | _ => false

/--
Given a LCNF `type` of the form `forall (a_1 : A_1) ... (a_n : A_n), B[a_1, ..., a_n]` and `p_1 : A_1, ... p_n : A_n`,
return `B[p_1, ..., p_n]`.

Remark: similar to `Meta.instantiateForall`, buf for LCNF types.
-/
def instantiateForall (type : Expr) (ps : Array Expr) : CoreM Expr :=
  go 0 type
where
  go (i : Nat) (type : Expr) : CoreM Expr :=
    if h : i < ps.size then
      if let .forallE _ _ b _ := type.headBeta then
        go (i+1) (b.instantiate1 ps[i])
      else
        throwError "invalid instantiateForall, too many parameters"
    else
      return type
termination_by go i _ => ps.size - i

/--
Return `true` if `type` is a predicate.
Examples: `Nat → Prop`, `Prop`, `Int → Bool → Prop`.
-/
partial def isPredicateType (type : Expr) : Bool :=
  match type.headBeta with
  | .sort .zero => true
  | .forallE _ _ b _ => isPredicateType b
  | _ => false

/--
Return `true` if `type` is a LCNF type former type or it is an "any" type.
This function is similar to `isTypeFormerType`, but more liberal.
For example, `isTypeFormerType` returns false for `◾` and `Nat → ◾`, but
this function returns true.
-/
partial def maybeTypeFormerType (type : Expr) : Bool :=
  match type.headBeta with
  | .sort .. => true
  | .forallE _ _ b _ => maybeTypeFormerType b
  | _ => type.isErased

/--
`isClass? type` return `some ClsName` if the LCNF `type` is an instance of the class `ClsName`.
-/
def isClass? (type : Expr) : CoreM (Option Name) := do
  let .const declName _ := type.getAppFn | return none
  if isClass (← getEnv) declName then
    return declName
  else
    return none

/--
`isArrowClass? type` return `some ClsName` if the LCNF `type` is an instance of the class `ClsName`, or
if it is arrow producing an instance of the class `ClsName`.
-/
partial def isArrowClass? (type : Expr) : CoreM (Option Name) := do
  match type.headBeta with
  | .forallE _ _ b _ => isArrowClass? b
  | _ => isClass? type

partial def getArrowArity (e : Expr) :=
  match e.headBeta with
  | .forallE _ _ b _ => getArrowArity b + 1
  | _ => 0

/-- Return `true` if `type` is an inductive datatype with 0 constructors. -/
def isInductiveWithNoCtors (type : Expr) : CoreM Bool := do
  let .const declName _ := type.getAppFn | return false
  let some (.inductInfo info) := (← getEnv).find? declName | return false
  return info.numCtors == 0

end Lean.Compiler.LCNF
