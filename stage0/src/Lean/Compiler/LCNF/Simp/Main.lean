/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.LCNF.ElimDead
import Lean.Compiler.LCNF.AlphaEqv
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.Bind
import Lean.Compiler.LCNF.Simp.FunDeclInfo
import Lean.Compiler.LCNF.Simp.InlineCandidate
import Lean.Compiler.LCNF.Simp.InlineProj
import Lean.Compiler.LCNF.Simp.Used
import Lean.Compiler.LCNF.Simp.DefaultAlt
import Lean.Compiler.LCNF.Simp.SimpValue
import Lean.Compiler.LCNF.Simp.ConstantFold

namespace Lean.Compiler.LCNF
namespace Simp

/--
Return `true` if `c` has only one exit point.
This is a quick approximation. It does not check cases
such as: a `cases` with many but only one alternative is not reachable.
It is only used to avoid the creation of auxiliary join points, and does not need
to be precise.
-/
private partial def oneExitPointQuick (c : Code) : Bool :=
  go c
where
  go (c : Code) : Bool :=
    match c with
    | .let _ k | .fun _ k => go k
    -- Approximation, the cases may have many unreachable alternatives, and only reachable.
    | .cases c => c.alts.size == 1 && go c.alts[0]!.getCode
    -- Approximation, we assume that any code containing join points have more than one exit point
    | .jp .. | .jmp .. | .unreach .. => false
    | .return .. => true

/--
Create a new local function declaration when `info.args.size < info.params.size`.
We use this function to inline/specialize a partial application of a local function.
-/
def specializePartialApp (info : InlineCandidateInfo) : SimpM FunDecl := do
  let mut subst := {}
  for param in info.params, arg in info.args do
    subst := subst.insert param.fvarId arg
  let mut paramsNew := #[]
  for param in info.params[info.args.size:] do
    let type ← replaceExprFVars param.type subst (translator := true)
    let paramNew ← mkAuxParam type
    paramsNew := paramsNew.push paramNew
    subst := subst.insert param.fvarId (.fvar paramNew.fvarId)
  let code ← info.value.internalize subst
  updateFunDeclInfo code
  mkAuxFunDecl paramsNew code

/--
Try to inline a join point.
-/
partial def inlineJp? (fvarId : FVarId) (args : Array Expr) : SimpM (Option Code) := do
  let some decl ← LCNF.findFunDecl? fvarId | return none
  unless (← shouldInlineLocal decl) do return none
  markSimplified
  betaReduce decl.params decl.value args

/--
When the configuration flag `etaPoly = true`, we eta-expand
partial applications of functions that take local instances as arguments.
This kind of function is inlined or specialized, and we create new
simplification opportunities by eta-expanding them.
-/
def etaPolyApp? (letDecl : LetDecl) : OptionT SimpM FunDecl := do
  guard <| (← read).config.etaPoly
  let .const declName _ := letDecl.value.getAppFn | failure
  let some info := (← getEnv).find? declName | failure
  guard <| hasLocalInst info.type
  guard <| !(← Meta.isInstance declName)
  let some decl ← getDecl? declName | failure
  let numArgs := letDecl.value.getAppNumArgs
  guard <| decl.getArity > numArgs
  let params ← mkNewParams letDecl.type
  let value := mkAppN letDecl.value (params.map (.fvar ·.fvarId))
  let auxDecl ← mkAuxLetDecl value
  let funDecl ← mkAuxFunDecl params (.let auxDecl (.return auxDecl.fvarId))
  addFVarSubst letDecl.fvarId funDecl.fvarId
  eraseLetDecl letDecl
  return funDecl

/--
Similar to `Code.isReturnOf`, but taking the current substitution into account.
-/
def isReturnOf (c : Code) (fvarId : FVarId) : SimpM Bool := do
  match c with
  | .return fvarId' => return (← normFVar fvarId') == fvarId
  | _ => return false

mutual
/--
If the value of the given let-declaration is an application that can be inlined,
inline it and simplify the result.

`k` is the "continuation" for the let declaration, if the application is inlined,
it will also be simplified.

Note: `inlineApp?` did not use to be in this mutually recursive declaration.
It used to be invoked by `simp`, and would return `Option Code` that would be
then simplified by `simp`. However, this simpler architecture produced an
exponential blowup in when processing functions such as `Lean.Elab.Deriving.Ord.mkMatch.mkAlts`.
The key problem is that when inlining a declaration we often can reduce the number
of exit points by simplified the inlined code, and then connecting the result to the
continuation `k`. However, this optimization is only possible if we simplify the
inlined code **before** we attach it to the continuation.
-/
partial def inlineApp? (letDecl : LetDecl) (k : Code) : SimpM (Option Code) := do
  let some info ← inlineCandidate? letDecl.value | return none
  let numArgs := info.args.size
  withInlining letDecl.value info.recursive do
  let fvarId := letDecl.fvarId
  if numArgs < info.arity then
    let funDecl ← specializePartialApp info
    addFVarSubst fvarId funDecl.fvarId
    markSimplified
    simp (.fun funDecl k)
  else
    let code ← betaReduce info.params info.value info.args[:info.arity]
    if k.isReturnOf fvarId && numArgs == info.arity then
      /- Easy case, the continuation `k` is just returning the result of the application. -/
      markSimplified
      simp code
    else
      let code ← simp code
      if oneExitPointQuick code then
        -- TODO: if `k` is small, we should also inline it here
        markSimplified
        code.bind fun fvarId' => do
          markUsedFVar fvarId'
          /- fvarId' is the result of the computation -/
          if numArgs > info.arity then
            let decl ← mkAuxLetDecl (mkAppN (.fvar fvarId') info.args[info.arity:])
            addFVarSubst fvarId decl.fvarId
            simp (.let decl k)
          else
            addFVarSubst fvarId fvarId'
            simp k
      -- else if info.ifReduce then
      --  eraseCode code
      --  return none
      else
        markSimplified
        let jpParam ← mkAuxParam (← inferType (mkAppN info.f info.args[:info.arity]))
        let jpValue ← if numArgs > info.arity then
          let decl ← mkAuxLetDecl (mkAppN (.fvar jpParam.fvarId) info.args[info.arity:])
          addFVarSubst fvarId decl.fvarId
          simp (.let decl k)
        else
          addFVarSubst fvarId jpParam.fvarId
          simp k
        let jpDecl ← mkAuxJpDecl #[jpParam] jpValue
        let code ← code.bind fun fvarId => return .jmp jpDecl.fvarId #[.fvar fvarId]
        return Code.jp jpDecl code

/--
Simplify the given local function declaration.
-/
partial def simpFunDecl (decl : FunDecl) : SimpM FunDecl := do
  let type ← normExpr decl.type
  let params ← normParams decl.params
  let value ← simp decl.value
  decl.update type params value

/--
Try to simplify `cases` of `constructor`
-/
partial def simpCasesOnCtor? (cases : Cases) : SimpM (Option Code) := do
  let discr ← normFVar cases.discr
  let discrExpr ← findCtor (.fvar discr)
  let some (ctorVal, ctorArgs) := discrExpr.constructorApp? (← getEnv) (useRaw := true) | return none
  let (alt, cases) := cases.extractAlt! ctorVal.name
  eraseCode (.cases cases)
  markSimplified
  match alt with
  | .default k => simp k
  | .alt _ params k =>
    let fields := ctorArgs[ctorVal.numParams:]
    let mut auxDecls := #[]
    for param in params, field in fields do
      /-
      `field` may not be a free variable. Recall that `constructorApp?` has special support for numerals,
      and `ctorArgs` contains a numeral if `discrExpr` is a numeral. We may have other cases in the future.
      To make the code robust, we add auxiliary declarations whenever the `field` is not a free variable.
      -/
      if field.isFVar then
        addFVarSubst param.fvarId field.fvarId!
      else
        let auxDecl ← mkAuxLetDecl field
        auxDecls := auxDecls.push (CodeDecl.let auxDecl)
        addFVarSubst param.fvarId auxDecl.fvarId
    let k ← simp k
    eraseParams params
    attachCodeDecls auxDecls k

/--
Simplify `code`
-/
partial def simp (code : Code) : SimpM Code := withIncRecDepth do
  incVisited
  match code with
  | .let decl k =>
    let mut decl ← normLetDecl decl
    if let some value ← simpValue? decl.value then
      decl ← decl.updateValue value
    if let some decls ← ConstantFold.foldConstants decl then
      markSimplified
      let k ← simp k
      attachCodeDecls decls k
    else if let some funDecl ← etaPolyApp? decl then
      simp (.fun funDecl k)
    else if decl.value.isFVar then
      /- Eliminate `let _x_i := _x_j;` -/
      addFVarSubst decl.fvarId decl.value.fvarId!
      eraseLetDecl decl
      simp k
    else if let some code ← inlineApp? decl k then
      eraseLetDecl decl
      return code
    else if let some (decls, fvarId) ← inlineProjInst? decl.value then
      addFVarSubst decl.fvarId fvarId
      eraseLetDecl decl
      let k ← simp k
      attachCodeDecls decls k
    else
      let k ← simp k
      if (← isUsed decl.fvarId) then
        markUsedLetDecl decl
        return code.updateLet! decl k
      else
        /- Dead variable elimination -/
        eraseLetDecl decl
        return k
  | .fun decl k | .jp decl k =>
    let mut decl := decl
    let toBeInlined ← isOnceOrMustInline decl.fvarId
    if toBeInlined then
      /-
      If the declaration will be inlined, it is wasteful to eagerly simplify it.
      So, we just normalize it (i.e., apply the substitution to it).
      -/
      decl ← normFunDecl decl
    else
      /-
      Note that functions in `decl` will be marked as used even if `decl` is not actually used.
      They will only be deleted in the next pass. TODO: investigate whether this is a problem.
      -/
      if code.isFun then
        if decl.isEtaExpandCandidate then
          /- We must apply substitution before trying to eta-expand, otherwise `inferType` may fail. -/
          decl ← normFunDecl decl
          /-
          We want to eta-expand **before** trying to simplify local function declaration because
          eta-expansion creates many optimization opportunities.
          -/
          decl ← decl.etaExpand
          markSimplified
      decl ← simpFunDecl decl
    let k ← simp k
    if (← isUsed decl.fvarId) then
      if toBeInlined then
        /-
        `decl` was supposed to be inlined, but there are still references to it.
        Thus, we must all variables in `decl` as used. Recall it was not eagerly simplified.
        -/
        markUsedFunDecl decl
      return code.updateFun! decl k
    else
      /- Dead function elimination -/
      eraseFunDecl decl
      return k
  | .return fvarId =>
    let fvarId ← normFVar fvarId
    markUsedFVar fvarId
    return code.updateReturn! fvarId
  | .unreach type =>
    return code.updateUnreach! (← normExpr type)
  | .jmp fvarId args =>
    let fvarId ← normFVar fvarId
    let args ← normExprs args
    if let some code ← inlineJp? fvarId args then
      simp code
    else
      markUsedFVar fvarId
      args.forM markUsedExpr
      return code.updateJmp! fvarId args
  | .cases c =>
    if let some k ← simpCasesOnCtor? c then
      return k
    else
      let simpCasesDefault := do
        let discr ← normFVar c.discr
        let resultType ← normExpr c.resultType
        markUsedFVar discr
        let alts ← c.alts.mapMonoM fun alt =>
          match alt with
          | .alt ctorName ps k =>
            withDiscrCtor discr ctorName ps do
              return alt.updateCode (← simp k)
          | .default k => return alt.updateCode (← simp k)
        let alts ← addDefaultAlt alts
        if alts.size == 1 && alts[0]! matches .default .. then
          return alts[0]!.getCode
        else
          return code.updateCases! resultType discr alts
      simpCasesDefault
end
