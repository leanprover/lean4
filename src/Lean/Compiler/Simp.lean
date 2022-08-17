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

partial def findLambda? (e : Expr) : CompilerM (Option LocalDecl) := do
  match e with
  | .fvar fvarId =>
    let some d@(.ldecl (value := v) ..) ← findDecl? fvarId | return none
    if v.isLambda then return some d else findLambda? v
  | .mdata _ e => findLambda? e
  | _ => return none

partial def findExpr (e : Expr) (skipMData := true): CompilerM Expr := do
  match e with
  | .fvar fvarId =>
    let some (.ldecl (value := v) ..) ← findDecl? fvarId | return e
    findExpr v
  | .mdata _ e' => if skipMData then findExpr e' else return e
  | _ => return e

/--
Local function declaration statistics.

Remark: we use the `userName` as the key. Thus, `ensureUniqueLetVarNames`
must be used before collectin stastistics.
-/
structure InlineStats where
  /--
  Mapping from local function name to the number of times it is used
  in a declaration.
  -/
  numOccs : Std.HashMap Name Nat := {}
  /--
  Mapping from local function name to their LCNF size.
  -/
  size : Std.HashMap Name Nat := {}

def InlineStats.format (s : InlineStats) : Format := Id.run do
  let mut result := Format.nil
  for (k, n) in s.numOccs.toList do
    let some size := s.size.find? k | pure ()
    result := result ++ "\n" ++ f!"{k} ↦ {n}, {size}"
    pure ()
  return result

def InlineStats.shouldInline (s : InlineStats) (k : Name) : Bool := Id.run do
  let some numOccs := s.numOccs.find? k | return false
  if numOccs == 1 then return true
  let some sz := s.size.find? k | return false
  return sz == 1

instance : ToFormat InlineStats where
  format := InlineStats.format

partial def collectInlineStats (e : Expr) : CoreM InlineStats := do
  let ((_, s), _) ← goLambda e |>.run {} |>.run {}
  return s
where
  goLambda (e : Expr) : StateRefT InlineStats CompilerM Unit := do
    withNewScope do
      let (_, body) ← visitLambda e
      go body

  goValue (value : Expr) : StateRefT InlineStats CompilerM Unit := do
    match value with
    | .lam .. => goLambda value
    | .app .. =>
      match (← findLambda? value.getAppFn) with
      | some localDecl =>
        trace[Meta.debug] "found decl {localDecl.userName}"
        if localDecl.value.isLambda then
          let key := localDecl.userName
          match (← get).numOccs.find? localDecl.userName with
          | some numOccs => modify fun s => { s with numOccs := s.numOccs.insert key (numOccs + 1) }
          | _ =>
            let sz ← getLCNFSize localDecl.value
            modify fun { numOccs, size } => { numOccs := numOccs.insert key 1, size := size.insert key sz }
      | _ => pure ()
    | _ => pure ()

  go (e : Expr) : StateRefT InlineStats CompilerM Unit := do
    match e with
    | .letE .. =>
      withNewScope do
        let body ← visitLet e fun value => do goValue value; return value
        go body
    | e =>
      if let some casesInfo ← isCasesApp? e then
        let args := e.getAppArgs
        for i in casesInfo.altsRange do
          goLambda args[i]!
      else
        goValue e

structure Config where
  increaseFactor : Nat := 2

structure Context where
  config : Config := {}
  /--
  Statistics for deciding whether to inline local function declarations.
  -/
  stats : InlineStats
  /--
  We only inline local declarations when `localInline` is `true`.
  We set it to `false` when we are inlining a non local definition
  that may have let-declarations whose names collide with the ones
  stored at `stats`.
  -/
  localInline : Bool := true
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

def shouldInline (localDecl : LocalDecl) : SimpM Bool :=
  return (← read).localInline && (← read).stats.shouldInline localDecl.userName

def isJump (e : Expr) : CompilerM Bool := do
  let .fvar fvarId := e.getAppFn | return false
  let some localDecl ← findDecl? fvarId | return false
  return localDecl.userName matches .num `_jp _

def inlineCandidate? (e : Expr) : SimpM (Option Nat) := do
  let f := e.getAppFn
  let arity ← match f with
    | .const declName _ =>
      unless hasInlineAttribute (← getEnv) declName do return none
      -- TODO: check whether function is recursive or not.
      -- We can skip the test and store function inline so far.
      let some decl ← getStage1Decl? declName | return none
      pure decl.getArity
    | _ =>
      match (← findLambda? f) with
      | none => return none
      | some localDecl =>
        unless (← shouldInline localDecl) do return none
        pure (getLambdaArity localDecl.value)
  if e.getAppNumArgs < arity then return none
  return e.getAppNumArgs - arity

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
  let f := e.getAppFn
  let value ← match f with
    | .const declName us =>
      let some decl ← getStage1Decl? declName | unreachable!
      pure <| decl.value.instantiateLevelParams decl.levelParams us
    | _ =>
      let some localDecl ← findLambda? f | unreachable!
      pure localDecl.value
  let args := e.getAppArgs
  let value := value.beta args
  assert! !value.isLambda
  withReader (fun ctx => { ctx with localInline := !f.isConst }) do
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
    else if (← isJump e) then
      /- TODO: fix, this is buggy.
         Suppose we have
         ```
         let _jp.1 := fun x => k[x]
         ```
         and we are trying to jump to `_jp.2` when processing
         ```
         let _x.3 := ...
         _jp.1 _x.3
         ```
         We must create a new join point `_jp.4` which fuses `_jp.1` and `_jp.2`.
         ```
         let _jp.4 := fun x => let r := k[x]; _jp.2 r
         ```
         and replace `_jp.1` with `_jp.4`.

         When inlining, we must "fix" the join points **before** we process it.
         We should not need `jp?` in the context. It will simplify the code too.
      -/
      return e
    else
      mkOptJump (← read).jp? (← expandTrivialExpr e)
end

end Simp

def Decl.simp (decl : Decl) : CoreM Decl := do
  let decl ← decl.ensureUniqueLetVarNames
  let stats ← Simp.collectInlineStats decl.value
  trace[Compiler.simp.inline.stats] "{decl.name}:{Format.nest 2 (format stats)}"
  /- TODO:
  - Fixpoint.
  -/
  decl.mapValue fun value => Simp.visitLambda value |>.run { stats } |>.run' {}

builtin_initialize
  registerTraceClass `Compiler.simp.inline.stats

end Lean.Compiler