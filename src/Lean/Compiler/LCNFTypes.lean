/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.BorrowedAnnotation
import Lean.Meta.InferType

namespace Lean.Compiler

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
      return .lam n d (b.abstract #[x]) bi
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      let borrowed := isMarkedBorrowed d
      let mut d ← toLCNFType d
      if borrowed then
        d := markBorrowed d
      let b ← toLCNFType (b.instantiate1 x)
      return .forallE n d (b.abstract #[x]) bi
  | .app ..  => type.withApp visitApp
  | .fvar .. => visitApp type #[]
  | _        => return anyTypeExpr
where
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

end Lean.Compiler