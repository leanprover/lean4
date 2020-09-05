/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Meta.ExprDefEq

namespace Lean
namespace Meta

def forallTelescopeCompatibleAux {α} (k : Array Expr → Expr → Expr → MetaM α) : Nat → Expr → Expr → Array Expr → MetaM α
| 0, type₁, type₂, xs   => k xs type₁ type₂
| i+1, type₁, type₂, xs => do
  type₁ ← whnf type₁;
  type₂ ← whnf type₂;
  match type₁, type₂ with
  | Expr.forallE n₁ d₁ b₁ c₁, Expr.forallE n₂ d₂ b₂ c₂ => do
    unless (n₁ == n₂) $
      throwError ("parameter name mismatch '" ++ n₁ ++ "', expected '" ++ n₂ ++ "'");
    unlessM (isDefEq d₁ d₂) $
      throwError ("type mismatch at parameter '" ++ n₁ ++ "'" ++ indentExpr d₁  ++ Format.line ++ "expected type" ++ indentExpr d₂);
    unless (c₁.binderInfo == c₂.binderInfo) $
      throwError ("binder annotation mismatch at parameter '" ++ n₁ ++ "'");
    withLocalDecl n₁ c₁.binderInfo d₁ fun x =>
      let type₁ := b₁.instantiate1 x;
      let type₂ := b₂.instantiate1 x;
      forallTelescopeCompatibleAux i type₁ type₂ (xs.push x)
  | _, _ => throwError ("unexpected number of parameters")

/-- Given two forall-expressions `type₁` and `type₂`, ensure the first `numParams` parameters are compatible, and
    then execute `k` with the parameters and remaining types. -/
@[inline] def forallTelescopeCompatible {α m} [Monad m] [MonadControlT MetaM m] (type₁ type₂ : Expr) (numParams : Nat) (k : Array Expr → Expr → Expr → m α) : m α :=
controlAt MetaM fun runInBase => forallTelescopeCompatibleAux (fun xs type₁ type₂ => runInBase $ k xs type₁ type₂) numParams type₁ type₂ #[]

end Meta

namespace Elab

def expandOptDeclSig (stx : Syntax) : Syntax × Option Syntax :=
-- many Term.bracketedBinder >> Term.optType
let binders := stx.getArg 0;
let optType := stx.getArg 1; -- optional (parser! " : " >> termParser)
if optType.isNone then
  (binders, none)
else
  let typeSpec := optType.getArg 0;
  (binders, some $ typeSpec.getArg 1)

def expandDeclSig (stx : Syntax) : Syntax × Syntax :=
-- many Term.bracketedBinder >> Term.typeSpec
let binders := stx.getArg 0;
let typeSpec := stx.getArg 1;
(binders, typeSpec.getArg 1)

def mkFreshInstanceName (env : Environment) (nextIdx : Nat) : Name :=
(env.mainModule ++ `_instance).appendIndexAfter nextIdx

def isFreshInstanceName (name : Name) : Bool :=
match name with
| Name.str _ s _ => "_instance".isPrefixOf s
| _              => false

/--
  Sort the given list of `usedParams` using the following order:
  - If it is an explicit level `allUserParams`, then use user given order.
  - Otherwise, use lexicographical.

  Remark: `scopeParams` are the universe params introduced using the `universe` command. `allUserParams` contains
  the universe params introduced using the `universe` command *and* the `.{...}` notation.

  Remark: this function return an exception if there is an `u` not in `usedParams`, that is in `allUserParams` but not in `scopeParams`.

  Remark: `explicitParams` are in reverse declaration order. That is, the head is the last declared parameter. -/
def sortDeclLevelParams (scopeParams : List Name) (allUserParams : List Name) (usedParams : Array Name) : Except String (List Name) :=
match allUserParams.find? $ fun u => !usedParams.contains u && !scopeParams.elem u with
| some u => throw ("unused universe parameter '" ++ toString u ++ "'")
| none   =>
  let result := allUserParams.foldl (fun result levelName => if usedParams.elem levelName then levelName :: result else result) [];
  let remaining := usedParams.filter (fun levelParam => !allUserParams.elem levelParam);
  let remaining := remaining.qsort Name.lt;
  pure $ result ++ remaining.toList

end Elab
end Lean
