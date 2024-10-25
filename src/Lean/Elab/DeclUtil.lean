/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Lean.Meta.Basic
import Lean.Meta.Check

namespace Lean.Meta

def forallTelescopeCompatibleAux (k : Array Expr → Expr → Expr → MetaM α) : Nat → Expr → Expr → Array Expr → MetaM α
  | 0, type₁, type₂, xs   => k xs type₁ type₂
  | i+1, type₁, type₂, xs => do
    let type₁ ← whnf type₁
    let type₂ ← whnf type₂
    match type₁, type₂ with
    | .forallE n₁ d₁ b₁ c₁, .forallE n₂ d₂ b₂ c₂ =>
      -- Remark: we use `mkIdent` to ensure macroscopes do not leak into error messages
      unless c₁ == c₂ do
        throwError "binder annotation mismatch at parameter '{mkIdent n₁}'"
      /-
      Remark: recall that users may suppress parameter names for instance implicit arguments.
      A fresh name (with macro scopes) is generated in this case. Thus, we allow the names
      to be different in this case. See issue #4310.
      -/
      unless n₁ == n₂ || (c₁.isInstImplicit && n₁.hasMacroScopes && n₂.hasMacroScopes) do
        throwError "parameter name mismatch '{mkIdent n₁}', expected '{mkIdent n₂}'"
      unless (← isDefEq d₁ d₂) do
        throwError "parameter '{mkIdent n₁}' {← mkHasTypeButIsExpectedMsg d₁ d₂}"
      withLocalDecl n₁ c₁ d₁ fun x =>
        let type₁ := b₁.instantiate1 x
        let type₂ := b₂.instantiate1 x
        forallTelescopeCompatibleAux k i type₁ type₂ (xs.push x)
    | _, _ => throwError "unexpected number of parameters"

/-- Given two forall-expressions `type₁` and `type₂`, ensure the first `numParams` parameters are compatible, and
    then execute `k` with the parameters and remaining types. -/
def forallTelescopeCompatible [Monad m] [MonadControlT MetaM m] (type₁ type₂ : Expr) (numParams : Nat) (k : Array Expr → Expr → Expr → m α) : m α :=
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

/--
Sort the given list of `usedParams` using the following order:
- If it is an explicit level in `allUserParams`, then use user-given order.
- All other levels come in lexicographic order after these.

Remark: `scopeParams` are the universe params introduced using the `universe` command. `allUserParams` contains
the universe params introduced using the `universe` command *and* the `.{...}` notation.

Remark: this function return an exception if there is an `u` not in `usedParams`, that is in `allUserParams` but not in `scopeParams`.

Remark: `scopeParams` and `allUserParams` are in reverse declaration order. That is, the head is the last declared parameter.
-/
def sortDeclLevelParams (scopeParams : List Name) (allUserParams : List Name) (usedParams : Array Name) : Except String (List Name) :=
  match allUserParams.find? fun u => !usedParams.contains u && !scopeParams.elem u with
  | some u => throw s!"unused universe parameter '{u}'"
  | none   =>
    -- Recall that `allUserParams` (like `scopeParams`) are in reverse order. That is, the last declared universe is the first element of the list.
    -- The following `foldl` will reverse the elements and produce a list of universe levels using the user given order.
    let result := allUserParams.foldl (fun result levelName => if usedParams.elem levelName then levelName :: result else result) []
    let remaining := usedParams.filter (fun levelParam => !allUserParams.elem levelParam)
    let remaining := remaining.qsort Name.lt
    return result ++ remaining.toList

end Lean.Elab
