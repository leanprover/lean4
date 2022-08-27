/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.BorrowedAnnotation
import Lean.Meta.InferType

namespace Lean.Compiler.LCNF

structure LCNFTypeExtState where
  types : Std.PHashMap Name Expr := {}
  instLevelType : Core.InstantiateLevelCache := {}
  deriving Inhabited

builtin_initialize lcnfTypeExt : EnvExtension LCNFTypeExtState ←
  registerEnvExtension (pure {})

def erasedExpr := mkConst ``lcErased
def anyTypeExpr := mkConst  ``lcAny

def _root_.Lean.Expr.isAnyType (e : Expr) :=
  e.isConstOf ``lcAny

def _root_.Lean.Expr.erased (e : Expr) :=
  e.isConstOf ``lcErased

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
- The arguments of type formers are type formers, `◾`, or `⊤`. We use `◾` to denote erased information,
  and `⊤` the any type.
- All type definitions are expanded. If reduction gets stuck, it is replaced with `⊤`.


The goal is to preserve as much information as possible and avoid the problems described above.
Then, we don't have `let x := v; ...` in LCNF code when `x` is a type former.
If the user provides a `let x := v; ...` where x is a type former, we can always expand it when
converting into LCNF.
Thus, given a `let x := v, ...` in occurring in LCNF, we know `x` cannot occur in any type since it is
not a type former.

We try to preserve type information because they unlock new optimizations, and we can type check
the result produced by each code generator step.
-/

open Meta in
/--
Convert a Lean type into a LCNF type used by the code generator.
-/
partial def toLCNFType (type : Expr) : MetaM Expr := do
  if (← isProp type) then
    return erasedExpr
  let type ← whnf type
  match type with
  | .sort u     => return .sort u
  | .const ..   => visitApp type #[]
  | .lam n d b bi =>
    withLocalDecl n bi d fun x => do
      let d ← toLCNFType d
      let b ← toLCNFType (b.instantiate1 x)
      if b.isAnyType || b.erased then
        return b
      else
        return (Expr.lam n d (b.abstract #[x]) bi).eta
  | .forallE .. => visitForall type #[]
  | .app ..  => type.withApp visitApp
  | .fvar .. => visitApp type #[]
  | _        => return anyTypeExpr
where
  visitForall (e : Expr) (xs : Array Expr) : MetaM Expr := do
    match e with
    | .forallE n d b bi =>
      let d := d.instantiateRev xs
      withLocalDecl n bi d fun x => do
        let borrowed := isMarkedBorrowed d
        let mut d := (← toLCNFType d).abstract xs
        if borrowed then
          d := markBorrowed d
        return .forallE n d (← visitForall b (xs.push x)) bi
    | _ =>
      let e ← toLCNFType (e.instantiateRev xs)
      return e.abstract xs

  visitApp (f : Expr) (args : Array Expr) := do
    let fNew ← match f with
      | .const declName us =>
        let .inductInfo _ ← getConstInfo declName | return anyTypeExpr
        pure <| .const declName us
      | .fvar .. => pure f
      | _ => return anyTypeExpr
    let mut result := fNew
    for arg in args do
      if (← isProp arg) then
        result := mkApp result erasedExpr
      else if (← isTypeFormer arg) then
        result := mkApp result (← toLCNFType arg)
      else
        result := mkApp result erasedExpr
    return result

/--
Return the LCNF type for the given declaration.
-/
def getDeclLCNFType (declName : Name) : CoreM Expr := do
  match lcnfTypeExt.getState (← getEnv) |>.types.find? declName with
  | some type => return type
  | none =>
    let info ← getConstInfo declName
    let type ← Meta.MetaM.run' <| toLCNFType info.type
    modifyEnv fun env => lcnfTypeExt.modifyState env fun s => { s with types := s.types.insert declName type }
    return type

/--
Instantiate the LCNF type for the given declaration with the given universe levels.
-/
def instantiateLCNFTypeLevelParams (declName : Name) (us : List Level) : CoreM Expr := do
  if us.isEmpty then
    getDeclLCNFType declName
  else
    if let some (us', r) := lcnfTypeExt.getState (← getEnv) |>.instLevelType.find? declName then
      if us == us' then
        return r
    let type ← getDeclLCNFType declName
    let info ← getConstInfo declName
    let r := type.instantiateLevelParams info.levelParams us
    modifyEnv fun env => lcnfTypeExt.modifyState env fun s => { s with instLevelType := s.instLevelType.insert declName (us, r) }
    return r

/--
Return true if the LCNF types `a` and `b` are compatible.

Remark: `a` and `b` can be type formers (e.g., `List`, or `fun (α : Type) => Nat → Nat × α`)

Remark: LCNFs types are eagerly eta reduced.
-/
partial def compatibleTypes (a b : Expr) : Bool :=
  if a.isAnyType || b.isAnyType then
    true
  else
    let a := a.headBeta
    let b := b.headBeta
    if a == b then
      true
    else
      match a, b with
      | .mdata _ a, b => compatibleTypes a b
      | a, .mdata _ b => compatibleTypes a b
      | .app f a, .app g b => compatibleTypes f g && compatibleTypes a b
      | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => compatibleTypes d₁ d₂ && compatibleTypes b₁ b₂
      | .lam _ d₁ b₁ _, .lam _ d₂ b₂ _ => compatibleTypes d₁ d₂ && compatibleTypes b₁ b₂
      | .sort u, .sort v => Level.isEquiv u v
      | .const n us, .const m vs => n == m && List.isEqv us vs Level.isEquiv
      | _, _ => false

mutual

partial def joinTypes (a b : Expr) : Expr :=
  joinTypes? a b |>.getD anyTypeExpr

partial def joinTypes? (a b : Expr) : Option Expr := do
  if a.isAnyType then return a
  else if b.isAnyType then return b
  else if a == b then return a
  else if a.erased || b.erased then failure
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
        return anyTypeExpr
      | .forallE n d₁ b₁ _, .forallE _ d₂ b₂ _ =>
        (do return .forallE n (← joinTypes? d₁ d₂) (joinTypes b₁ b₂) .default)
        <|>
        return anyTypeExpr
      | .lam n d₁ b₁ _, .lam _ d₂ b₂ _ =>
        (do return .lam n (← joinTypes? d₁ d₂) (joinTypes b₁ b₂) .default)
        <|>
        return anyTypeExpr
      | _, _ => return anyTypeExpr

end

/--
Return `true` if `type` is a LCNF type former type.
-/
def isTypeFormerType (type : Expr) : Bool :=
  match type with
  | .sort .. => true
  | .forallE _ _ b _ => isTypeFormerType b
  | _ => type.isAnyType

/--
`isClass? type` return `some ClsName` if the LCNF `type` is an instance of the class `ClsName`.
-/
def isClass? (type : Expr) : CoreM (Option Name) := do
  let .const declName _ := type.getAppFn | return none
  if isClass (← getEnv) declName then
    return declName
  else
    return none

end Lean.Compiler.LCNF