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
    subst := subst.insert param.fvarId arg.toExpr
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
partial def inlineJp? (fvarId : FVarId) (args : Array Arg) : SimpM (Option Code) := do
  /- Remark: we don't need to use `findFunDecl'?` here. -/
  let some decl ← findFunDecl? fvarId | return none
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
  let .const declName us args := letDecl.value | failure
  let some info := (← getEnv).find? declName | failure
  guard <| hasLocalInst info.type
  guard <| !(← Meta.isInstance declName)
  let some decl ← getDecl? declName | failure
  guard <| decl.getArity > args.size
  let params ← mkNewParams letDecl.type
  let auxDecl ← mkAuxLetDecl (.const declName us (args ++ params.map (.fvar ·.fvarId)))
  let funDecl ← mkAuxFunDecl params (.let auxDecl (.return auxDecl.fvarId))
  addFVarSubst letDecl.fvarId funDecl.fvarId
  eraseLetDecl letDecl
  return funDecl

/--
Similar to `Code.isReturnOf`, but taking the current substitution into account.
-/
def isReturnOf (c : Code) (fvarId : FVarId) : SimpM Bool := do
  match c with
  | .return fvarId' => match (← normFVar fvarId') with
    | .fvar fvarId'' => return fvarId'' == fvarId
    | .erased => return false
  | _ => return false

def elimVar? (value : LetValue) : SimpM (Option FVarId) := do
  let .fvar fvarId #[] := value | return none
  return fvarId

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
      let simpK (result : FVarId) : SimpM Code := do
        /- `result` contains the result of the inlined code -/
        if numArgs > info.arity then
          let decl ← mkAuxLetDecl (.fvar result info.args[info.arity:])
          addFVarSubst fvarId decl.fvarId
          simp (.let decl k)
        else
          addFVarSubst fvarId result
          simp k
      if oneExitPointQuick code then
        -- TODO: if `k` is small, we should also inline it here
        markSimplified
        code.bind fun fvarId' => do
          markUsedFVar fvarId'
          simpK fvarId'
      -- else if info.ifReduce then
      --  eraseCode code
      --  return none
      else
        markSimplified
        let expectedType ← inferAppType info.fType info.args[:info.arity]
        if expectedType.headBeta.isForall then
          /-
          If `code` returns a function, we create an auxiliary local function declaration (and eta-expand it)
          instead of creating a joinpoint that takes a closure as an argument.
          -/
          let auxFunDecl ← mkAuxFunDecl #[] code
          let auxFunDecl ← auxFunDecl.etaExpand
          let k ← simpK auxFunDecl.fvarId
          attachCodeDecls #[.fun auxFunDecl] k
        else
          let jpParam ← mkAuxParam expectedType
          let jpValue ← simpK jpParam.fvarId
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
  match (← normFVar cases.discr) with
  | .erased => mkReturnErased
  | .fvar discr =>
    let some ctorInfo ← findCtor? discr | return none
    let (alt, cases) := cases.extractAlt! ctorInfo.getName
    eraseCode (.cases cases)
    markSimplified
    match alt with
    | .default k => simp k
    | .alt _ params k =>
      match ctorInfo with
      | .ctor ctorVal ctorArgs =>
        let fields := ctorArgs[ctorVal.numParams:]
        for param in params, field in fields do
          addSubst param.fvarId field.toExpr
        let k ← simp k
        eraseParams params
        return k
      | .natVal 0 => simp k
      | .natVal (n+1) =>
        let auxDecl ← mkAuxLetDecl (.value (.natVal n))
        addFVarSubst params[0]!.fvarId auxDecl.fvarId
        let k ← simp k
        eraseParams params
        return some <| .let auxDecl k

/--
Simplify `code`
-/
partial def simp (code : Code) : SimpM Code := withIncRecDepth do
  incVisited
  match code with
  | .let decl k =>
    let baseDecl := decl
    let mut decl ← normLetDecl baseDecl
    if baseDecl != decl then
      markSimplified
    if let some value ← simpValue? decl.value then
      markSimplified
      decl ← decl.updateValue value
    if let some decls ← ConstantFold.foldConstants decl then
      markSimplified
      let k ← simp k
      attachCodeDecls decls k
    else if let some funDecl ← etaPolyApp? decl then
      simp (.fun funDecl k)
    else if let some fvarId ← elimVar? decl.value then
      /- Eliminate `let _x_i := _x_j;` -/
      addFVarSubst decl.fvarId fvarId
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
    withNormFVarResult (← normFVar fvarId) fun fvarId => do
      markUsedFVar fvarId
      return code.updateReturn! fvarId
  | .unreach type =>
    return code.updateUnreach! (← normExpr type)
  | .jmp fvarId args =>
    withNormFVarResult (← normFVar fvarId) fun fvarId => do
      let args ← normArgs args
      if let some code ← inlineJp? fvarId args then
        simp code
      else
        markUsedFVar fvarId
        args.forM markUsedArg
        return code.updateJmp! fvarId args
  | .cases c =>
    if let some k ← simpCasesOnCtor? c then
      return k
    else
      withNormFVarResult (← normFVar c.discr) fun discr => do
        let resultType ← normExpr c.resultType
        markUsedFVar discr
        let alts ← c.alts.mapMonoM fun alt => do
          match alt with
          | .alt ctorName ps k =>
            if !(k matches .unreach ..) && (← ps.anyM fun p => isInductiveWithNoCtors p.type) then
              let type ← k.inferType
              eraseCode k
              markSimplified
              return alt.updateCode (.unreach type)
            else
              withDiscrCtor discr ctorName ps do
                return alt.updateCode (← simp k)
          | .default k => return alt.updateCode (← simp k)
        let alts ← addDefaultAlt alts
        if alts.size == 1 && alts[0]! matches .default .. then
          return alts[0]!.getCode
        else
          return code.updateCases! resultType discr alts
end
