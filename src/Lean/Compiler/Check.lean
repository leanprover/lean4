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

structure Check.Context where
  /-- Join points that are in scope. -/
  jps : FVarIdSet := {}

abbrev CheckM := ReaderT Check.Context InferTypeM

def withFreshJps (x : CheckM α) : CheckM α :=
  withReader (fun ctx => { ctx with jps := {} }) x

def lambdaBoundedTelescope (e : Expr) (n : Nat) (k : Array Expr → Expr → CheckM α) : CheckM α :=
  go e n #[]
where
  go (e : Expr) (i : Nat) (xs : Array Expr) : CheckM α :=
    match i with
    | 0 => k xs (e.instantiateRev xs)
    | i+1 => match e with
      | .lam n d b bi =>
        withLocalDecl n (d.instantiateRev xs) bi fun x => go b i (xs.push x)
      | _ => throwError "lambda expected"

partial def check (e : Expr) (cfg : Check.Config := {}) : CheckM Unit := do
  checkLambda e #[] |>.run {}
where
  checkLambda (e : Expr) (xs : Array Expr) : CheckM Unit := do
    match e with
    | .lam n d b bi =>
      withLocalDecl n (d.instantiateRev xs) bi fun x => checkLambda b (xs.push x)
    | _ => checkBlock e xs

  checkBlock (e : Expr) (xs : Array Expr) : CheckM Unit := do
    match e with
    | .lam .. =>
      throwError "invalid occurrence of lambda-expression at the end of a let-declaration block{indentExpr (e.instantiateRev xs)}"
    | .letE n t v b _ =>
      let value := v.instantiateRev xs
      if value.isAppOf ``lcUnreachable then
        throwError "invalid occurrence of `lcUnreachable` in let-declaration `{n}`"
      if isJpBinderName n then
        checkLambda value #[]
      else if value.isLambda then
        -- This is a local function declaration
        withFreshJps <| checkLambda value #[]
      else
        checkValue value (isTerminal := false)
      let type := t.instantiateRev xs
      let valueType ← inferType value
      unless compatibleTypes type valueType do
        throwError "type mismatch at let-declaration `{n}`, value has type{indentExpr valueType}\nbut is expected to have type{indentExpr type}"
      withLocalDecl n type .default fun x =>
        withReader (fun ctx => { ctx with jps := if isJpBinderName n then ctx.jps.insert x.fvarId! else ctx.jps }) do
          checkBlock b (xs.push x)
    | _ =>
      if let some fvarId ← isJump? e then
        unless (← read).jps.contains fvarId do
          /-
          We cannot jump to join points defined out of the scope of a local function declaration.
          For example, the following is an invalid LCNF.
          ```
          let _jp.1 := fun x => ... -- Some join point
          let f := fun y => -- Local function declaration.
            ...
            _jp.1 _x.n -- jump to a join point that is not in the scope of `f`.
          ```
          -/
          throwError "invalid jump to out of scope join point"
      checkValue (e.instantiateRev xs) (isTerminal := true)

  checkValue (e : Expr) (isTerminal : Bool) : CheckM Unit := do
    match e with
    | .lit _ => pure ()
    | .app .. => checkApp e isTerminal
    | .proj _ _ (.fvar _) => pure ()
    | .mdata _ (.fvar _)  => pure ()
    | .const _ _ => pure () -- TODO: check number of universe level parameters
    | .fvar _ => pure () -- TODO: report unnecessary fvar?
    | _ => throwError "unexpected expression at LCNF{indentExpr e}"

  checkApp (e : Expr) (isTerminal : Bool) : CheckM Unit := do
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
        unless isTypeFormerType expectedType || expectedType.erased do
          unless arg.isFVar do
            throwError "invalid LCNF application{indentExpr e}\nargument{indentExpr arg}\nmust be a free variable"
        fType := b

  checkCases (casesInfo : CasesInfo) (args : Array Expr) : CheckM Unit := do
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
        checkBlock altBody #[]

end Lean.Compiler