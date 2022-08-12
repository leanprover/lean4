/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.InferType
import Lean.Compiler.Util

namespace Lean.Compiler
open InferType

/-!
Type checker for LCNF expressions
-/

structure Check.Config where
  terminalCasesOnly : Bool := true

def lambdaBoundedTelescope (e : Expr) (n : Nat) (k : Array Expr → Expr → InferTypeM α) : InferTypeM α :=
  go e n #[]
where
  go (e : Expr) (i : Nat) (xs : Array Expr) : InferTypeM α :=
    match i with
    | 0 => k xs e
    | i+1 => match e with
      | .lam n d b bi =>
        withLocalDecl n (d.instantiateRev xs) bi fun x => go b i (xs.push x)
      | _ => throwError "lambda expected"

partial def check (e : Expr) (cfg : Check.Config := {}) : InferTypeM Unit := do
  checkBlock e #[]
where
  checkBlock (e : Expr) (xs : Array Expr) : InferTypeM Unit := do
    match e with
    | .lam n d b bi => withLocalDecl n (d.instantiateRev xs) bi fun x => checkBlock b (xs.push x)
    | .letE n t v b _ =>
      let value := v.instantiateRev xs
      checkValue value (isTerminal := false)
      let type := t.instantiateRev xs
      let valueType ← inferType value
      unless compatibleTypes type valueType do
        throwError "type mismatch at let-declaration `{n}`, value has type{indentExpr valueType}\nbut is expected to have type{indentExpr type}"
      withLocalDecl n type .default fun x => checkBlock b (xs.push x)
    | _ => checkValue (e.instantiateRev xs) (isTerminal := true)

  checkValue (e : Expr) (isTerminal : Bool) : InferTypeM Unit := do
    match e with
    | .lit _ => pure ()
    | .lam .. => checkBlock e #[]
    | .app .. => checkApp e isTerminal
    | .proj _ _ (.fvar _) => pure ()
    | .mdata _ (.fvar _)  => pure ()
    | .const _ _ => pure () -- TODO: check number of universe level parameters
    | .fvar _ => pure () -- TODO: report unnecessary fvar?
    | _ => throwError "unexpected expression at LCNF{indentExpr e}"

  checkApp (e : Expr) (isTerminal : Bool) : InferTypeM Unit := do
    let f := e.getAppFn
    let args := e.getAppArgs
    unless f.isConst || f.isFVar do
      throwError "unexpected function application, function must be a constant or free variable{indentExpr e}"
    if let some casesInfo ← isCasesApp? e then
      unless isTerminal || !cfg.terminalCasesOnly do
        throwError "non-terminal occurrence of cases-like term{indentExpr e}"
      checkCases casesInfo args
    else
      let mut fType ← inferType f
      let mut j := 0
      for i in [:args.size] do
        let arg := args[i]!
        if fType.isAnyType then
          return ()
        fType := fType.headBeta
        let (d, b) ←
          match fType with
          | .forallE _ d b _ => pure (d, b)
          | _ =>
            fType := fType.instantiateRevRange j i args |>.headBeta
            match fType with
            | .forallE _ d b _ => j := i; pure (d, b)
            | _ =>
              if fType.isAnyType then return ()
              throwError "function expected at{indentExpr e}\narrow type expected{indentExpr fType}"
        let argType ← inferType arg
        let expectedType := d.instantiateRevRange j i args
        unless compatibleTypes argType expectedType do
          throwError "type mismatch at LCNF application{indentExpr e}\nargument {arg} has type{indentExpr argType}\nbut is expected to have type{indentExpr expectedType}"
        unless isTypeFormerType d || d.erased do
          unless arg.isFVar do
            throwError "invalid LCNF application{indentExpr e}\nargument {arg} must be a free variable"
        fType := b

  checkCases (casesInfo : CasesInfo) (args : Array Expr) : InferTypeM Unit := do
    let mut motive := args[casesInfo.motivePos]!
    for i in casesInfo.discrsRange do
      let discr := args[i]!
      let discrType ← inferType discr
      if let .lam _ d b _ := motive then
        unless compatibleTypes d discrType do
          throwError "type mismatch at LCNF `cases` discriminant{indentExpr discr}\nhas type{indentExpr discrType}\nbut is expected to have type{indentExpr d}"
        motive := b
    let expectedType := motive
    for i in casesInfo.altsRange, numParams in casesInfo.altNumParams do
      let alt := args[i]!
      lambdaBoundedTelescope alt numParams fun _ altBody => do
        let altBodyType ← inferType altBody
        unless compatibleTypes expectedType altBodyType do
          throwError "type mismatch at LCNF `cases` alternative{indentExpr altBody}\nhas type{indentExpr altBodyType}\nbut is expected to have type{indentExpr expectedType}"

end Lean.Compiler