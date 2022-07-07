/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Meta.Basic
import Lean.Meta.Check

namespace Lean.Meta

def forallTelescopeCompatibleAux {α} (k : Array Expr → Expr → Expr → MetaM α) : Nat → Expr → Expr → Array Expr → MetaM α
  | 0, type₁, type₂, xs   => k xs type₁ type₂
  | i+1, type₁, type₂, xs => do
    let type₁ ← whnf type₁
    let type₂ ← whnf type₂
    match type₁, type₂ with
    | Expr.forallE n₁ d₁ b₁ c₁, Expr.forallE n₂ d₂ b₂ c₂ =>
      unless n₁ == n₂ do
        throwError "parameter name mismatch '{n₁}', expected '{n₂}'"
      unless (← isDefEq d₁ d₂) do
        throwError "parameter '{n₁}' {← mkHasTypeButIsExpectedMsg d₁ d₂}"
      unless c₁ == c₂ do
        throwError "binder annotation mismatch at parameter '{n₁}'"
      withLocalDecl n₁ c₁ d₁ fun x =>
        let type₁ := b₁.instantiate1 x
        let type₂ := b₂.instantiate1 x
        forallTelescopeCompatibleAux k i type₁ type₂ (xs.push x)
    | _, _ => throwError "unexpected number of parameters"

/-- Given two forall-expressions `type₁` and `type₂`, ensure the first `numParams` parameters are compatible, and
    then execute `k` with the parameters and remaining types. -/
def forallTelescopeCompatible {α m} [Monad m] [MonadControlT MetaM m] (type₁ type₂ : Expr) (numParams : Nat) (k : Array Expr → Expr → Expr → m α) : m α :=
  controlAt MetaM fun runInBase =>
    forallTelescopeCompatibleAux (fun xs type₁ type₂ => runInBase $ k xs type₁ type₂) numParams type₁ type₂ #[]

end Meta

namespace Elab

def expandOptDeclSig (stx : Syntax) : Syntax × Option Syntax :=
  -- many Term.bracketedBinder >> Term.optType
  let binders := stx[0]
  let optType := stx[1] -- optional (leading_parser " : " >> termParser)
  if optType.isNone then
    (binders, none)
  else
    let typeSpec := optType[0]
    (binders, some typeSpec[1])

def expandDeclSig (stx : Syntax) : Syntax × Syntax :=
  -- many Term.bracketedBinder >> Term.typeSpec
  let binders  := stx[0]
  let typeSpec := stx[1]
  (binders, typeSpec[1])

def mkFreshInstanceName (env : Environment) (nextIdx : Nat) : Name :=
  (env.mainModule ++ `_instance).appendIndexAfter nextIdx

def isFreshInstanceName (name : Name) : Bool :=
  match name with
  | .str _ s => "_instance".isPrefixOf s
  | _        => false

/--
  Sort the given list of `usedParams` using the following order:
  - If it is an explicit level `allUserParams`, then use user given order.
  - Otherwise, use lexicographical.

  Remark: `scopeParams` are the universe params introduced using the `universe` command. `allUserParams` contains
  the universe params introduced using the `universe` command *and* the `.{...}` notation.

  Remark: this function return an exception if there is an `u` not in `usedParams`, that is in `allUserParams` but not in `scopeParams`.

  Remark: `explicitParams` are in reverse declaration order. That is, the head is the last declared parameter. -/
def sortDeclLevelParams (scopeParams : List Name) (allUserParams : List Name) (usedParams : Array Name) : Except String (List Name) :=
  match allUserParams.find? fun u => !usedParams.contains u && !scopeParams.elem u with
  | some u => throw s!"unused universe parameter '{u}'"
  | none   =>
    let result := allUserParams.foldl (fun result levelName => if usedParams.elem levelName then levelName :: result else result) []
    let remaining := usedParams.filter (fun levelParam => !allUserParams.elem levelParam)
    let remaining := remaining.qsort Name.lt
    pure $ result ++ remaining.toList

end Lean.Elab
