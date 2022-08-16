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
  /--
  Current continuation. It is a join point or lambda abstraction.
  -/
  jp? : Option Expr := none

abbrev SimpM := ReaderT Context CompilerM

def withJp (jp : Expr) (x : SimpM α) : SimpM α := do
  let jp ← mkJpDeclIfNotSimple jp
  withReader (fun ctx => { ctx with jp? := some jp }) x

def withoutJp (x : SimpM α) : SimpM α :=
  withReader (fun ctx => { ctx with jp? := none }) x

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

/--
If `e` is an application that can be inlined, inline it.

`k?` is the optional "continuation" for `e`, and it may contain loose bound variables
that need to instantiated with `xs`. That is, if `k? = some k`, then `k.instantiateRev xs`
is an expression without loose bound variables.
-/
partial def inlineApp? (e : Expr) (xs : Array Expr) (k? : Option Expr) : SimpM (Option Expr) := do
  let some numExtraArgs ← inlineCandidate? e | return none
  let args := e.getAppArgs
  if k?.isNone && numExtraArgs == 0 then
    -- Easy case, there is not continuation and `e` is not over applied
    inlineApp e
  else
    /-
    There is a continuation `k` or `e` is over applied.
    If `e` is over applied, the extra arguments act as continuation.
    -/
    let toInline := mkAppN e.getAppFn args[:args.size - numExtraArgs]
    /-
    `toInline` is the application that is going to be inline
     We create a new join point
     ```
     let jp := fun y =>
       let x := y <extra-arguments> -- if `e` is over applied
       k
     ```
     Recall that `visitLet` incorporates the current continuation
     to the new join point `jp`.
    -/
    let jpDomain ← inferType toInline
    let binderName ← mkFreshUserName `_y
    let jp ← withNewScope do
      let y ← mkLocalDecl binderName jpDomain
      let body ← if numExtraArgs == 0 then
        visitLet k?.get! (xs.push y)
      else
        let x ← mkAuxLetDecl (mkAppN y args[args.size - numExtraArgs:])
        if let some k := k? then
          visitLet k (xs.push x)
        else
          visitLet x (xs.push x)
      let body ← mkLetUsingScope body
      mkLambda #[y] body
    /- Inline `toInline` and "go-to" `jp` with the result. -/
    withJp jp do inlineApp toInline

/--
Let-declaration basic block visitor. `e` may contain loose bound variables that
still have to be instantiated with `xs`.
-/
partial def visitLet (e : Expr) (xs : Array Expr := #[]): SimpM Expr := do
  match e with
  | .letE binderName type value body nonDep =>
    let mut value := value.instantiateRev xs
    if value.isLambda then
      value ← withoutJp <| visitLambda value
    if value.isFVar then
      /- Eliminate `let _x_i := _x_j;` -/
      visitLet body (xs.push value)
    else if let some e ← inlineApp? value xs body then
      return e
    else
      let type := type.instantiateRev xs
      let x ← mkLetDecl binderName type value nonDep
      visitLet body (xs.push x)
  | _ =>
    let e := e.instantiateRev xs
    if let some casesInfo ← isCasesApp? e then
      visitCases casesInfo e
    else if let some e ← inlineApp? e #[] none then
      return e
    else
      mkOptJump (← read).jp? (← expandTrivialExpr e)
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