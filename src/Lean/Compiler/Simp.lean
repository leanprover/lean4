/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.CompilerM
import Lean.Compiler.Decl
import Lean.Compiler.Stage1
import Lean.Compiler.InlineAttrs

namespace Lean.Compiler

namespace Simp

structure Config where
  increaseFactor : Nat := 2

structure Context where
  config : Config := {}
  jp? : Option Expr := none

structure State where
  unit : Unit := ()

abbrev SimpM := ReaderT Context $ StateRefT State CompilerM

def inlineCandidate? (e : Expr) : SimpM (Option Nat) := do
  let .const declName _ := e.getAppFn | return none
  unless hasInlineAttribute (← getEnv) declName do return none
  let some decl ← getStage1Decl? declName | return none
  if e.getAppNumArgs < decl.getArity then return none
  return e.getAppNumArgs - decl.getArity

partial def findExpr (e : Expr) (skipMData := true): CompilerM Expr := do
  match e with
  | .fvar fvarId =>
    let some (.ldecl (value := v) ..) ← findDecl? fvarId | return e
    findExpr v
  | .mdata _ e' => if skipMData then findExpr e' else return e
  | _ => return e

/--
If `e` if a free variable that expands to a valid LCNF terminal `let`-block expression `e'`,
return `e'`. -/
def expandTrivialExpr (e : Expr) : CompilerM Expr := do
  if e.isFVar then
    let e' ← findExpr e
    unless e'.isLambda do
      return e'
  return e

mutual

partial def visitLambda (e : Expr) : SimpM Expr :=
  withNewScope do
    let (as, e) ← Compiler.visitLambda e
    let e ← mkLetUsingScope (← visitLet e)
    mkLambda as e

partial def visitCases (casesInfo : CasesInfo) (e : Expr) : SimpM Expr := do
  let mut args  := e.getAppArgs
  let major := args[casesInfo.discrsRange.stop - 1]!
  let major ← findExpr major
  if let some (ctorVal, ctorArgs) := major.constructorApp? (← getEnv) then
    /- Simplify `casesOn` constructor -/
    let ctorIdx := ctorVal.cidx
    let alt := args[casesInfo.altsRange.start + ctorIdx]!
    let ctorFields := ctorArgs[ctorVal.numParams:]
    let alt := alt.beta ctorFields
    assert! !alt.isLambda
    visitLet alt
  else
    if let some jp := (← read).jp? then
      let .forallE _ _ b _ ← inferType jp | unreachable! -- jp's type is guaranteed to be an nondependent arrow
      args := casesInfo.updateResultingType args b
    for i in casesInfo.altsRange do
      args ← args.modifyM i visitLambda
    return mkAppN e.getAppFn args

partial def inlineApp (e : Expr) : SimpM Expr := do
  let .const declName us := e.getAppFn | unreachable!
  let some decl ← getStage1Decl? declName | unreachable!
  let args := e.getAppArgs
  let value := decl.value.instantiateLevelParams decl.levelParams us
  let value := value.beta args
  assert! !value.isLambda
  visitLet value

partial def visitLet (e : Expr) : SimpM Expr := do
  go e #[]
where
  go (e : Expr) (xs : Array Expr) : SimpM Expr := do
    let rec inlineApp? (e : Expr) (k? : Option Expr) : SimpM (Option Expr) := do
      let some numExtraArgs ← inlineCandidate? e | return none
      let args := e.getAppArgs
      if k?.isNone && numExtraArgs == 0 then
        inlineApp e
      else
        let toInline := mkAppN e.getAppFn args[:args.size - numExtraArgs]
        let jpDomain ← inferType toInline
        let binderName ← mkFreshUserName `_y
        let bodyAbst ← withNewScope do
          let y ← mkLocalDecl binderName jpDomain
          let body ← if numExtraArgs == 0 then
            go k?.get! (xs.push y)
          else if let some k := k? then
            let x ← mkAuxLetDecl (mkAppN y args[args.size - numExtraArgs:])
            go k (xs.push x)
          else
            pure <| mkAppN y args[args.size - numExtraArgs:]
          let body ← mkLetUsingScope body
          return body.abstract #[y]
        let jp ← if (← isSimpleLCNF bodyAbst) then
          -- Join point is too simple, we eagerly inline it.
          pure <| .lam binderName jpDomain bodyAbst .default
        else
          mkJpDecl (.lam binderName jpDomain bodyAbst .default)
        withReader (fun _ => { jp? := some jp }) do
          inlineApp toInline
    match e with
    | .letE binderName type value body nonDep =>
      let mut value := value.instantiateRev xs
      if value.isLambda then
        value ← withReader (fun _ => {}) <| visitLambda value
      if value.isFVar then
        /- Eliminate `let _x_i := _x_j;` -/
        go body (xs.push value)
      else if let some e ← inlineApp? value body then
        return e
      else
        let type := type.instantiateRev xs
        let x ← mkLetDecl binderName type value nonDep
        go body (xs.push x)
    | _ =>
      let e := e.instantiateRev xs
      if let some casesInfo ← isCasesApp? e then
        visitCases casesInfo e
      else if let some e ← inlineApp? e none then
        return e
      else
        let e ← expandTrivialExpr e
        match (← read).jp? with
        | none => return e
        | some jp => mkJump jp e

end

end Simp

def Decl.simp (decl : Decl) : CoreM Decl := do
  let decl ← decl.ensureUniqueLetVarNames
  /- TODO:
  - Collect local function number of occurrences.
  - Fixpoint.
  -/
  decl.mapValue fun value => Simp.visitLambda value |>.run {} |>.run' {}

end Lean.Compiler