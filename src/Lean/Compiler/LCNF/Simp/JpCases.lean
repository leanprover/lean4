/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.DependsOn
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.LCNF.Simp.Basic
import Lean.Compiler.LCNF.Simp.DiscrM

namespace Lean.Compiler.LCNF
namespace Simp

/--
Given the function declaration `decl`, return `some idx` if it is of the form
```
f y :=
  ... /- This part is not bigger than smallThreshold. -/
  cases y
  | ... => ...
  ...
```
`idx` is the index of the parameter used in the `cases` statement.
-/
def isJpCases? (decl : FunDecl) : CompilerM (Option Nat) := do
  if decl.params.size == 0 then
    return none
  else
    let small := (← getConfig).smallThreshold
    let rec go (code : Code) (prefixSize : Nat) : Option Nat :=
      if prefixSize > small then none else
      match code with
      | .let _ k => go k (prefixSize + 1) /- TODO: we should have uniform heuristics for estimating the size. -/
      | .cases c => decl.params.findIdx? fun param => c.discr == param.fvarId
      | _ => none
    return go decl.value 0

/--
Information for join points that satisfy `isJpCases?`
-/
structure JpCasesInfo where
  /-- Parameter index returned by `isJpCases?`. This parameter is the one the join point is performing the case-split. -/
  paramIdx  : Nat
  /--
  Set of constructor names s.t. `ctorName` is in the set if there is a jump to the join point where the parameter
  `paramIdx` is a constructor application.
  -/
  ctorNames : NameSet := {}
  deriving Inhabited

abbrev JpCasesInfoMap := FVarIdMap JpCasesInfo

/-- Return `true` if the collected information suggests opportunities for the `JpCases` optimization. -/
def JpCasesInfoMap.isCandidate (info : JpCasesInfoMap) : Bool :=
  info.any fun _ s => !s.ctorNames.isEmpty

/--
Return a map containing entries `jpFVarId ↦ { paramIdx, ctorNames }` where `jpFVarId` is the id of join point
in code that satisfies `isJpCases`, and `ctorNames` is a set of constructor names such that
there is a jump `.jmp jpFVarId #[..., x, ...]` in `code` and `x` is a constructor application.
`paramIdx` is the index of the parameter
-/
partial def collectJpCasesInfo (code : Code) : CompilerM JpCasesInfoMap := do
  let (_, s) ← go code |>.run {} |>.run {}
  return s
where
  go (code : Code) : StateRefT JpCasesInfoMap DiscrM Unit := do
    match code with
    | .let _ k => go k
    | .fun decl k => go decl.value; go k
    | .jp decl k =>
      if let some paramIdx ← isJpCases? decl then
        modify fun s => s.insert decl.fvarId { paramIdx }
      go decl.value; go k
    | .cases c => c.alts.forM fun alt =>
      match alt with
      | .default k => go k
      | .alt ctorName ps k => withDiscrCtor c.discr ctorName ps <| go k
    | .return .. | .unreach .. => return ()
    | .jmp fvarId args =>
      if let some info := (← get).find? fvarId then
        let .fvar argFVarId := args[info.paramIdx]! | return ()
        let some ctorName ← findCtorName? argFVarId | return ()
        modify fun map => map.insert fvarId <| { info with ctorNames := info.ctorNames.insert ctorName }

/--
Extract the let-declarations and `cases` for a join point body that satisfies `isJpCases?`.
-/
private def extractJpCases (code : Code) : Array CodeDecl × Cases :=
  go code #[]
where
  go (code : Code) (decls : Array CodeDecl) :=
    match code with
    | .let decl k => go k <| decls.push (.let decl)
    | .cases c => (decls, c)
    | _ => unreachable! -- `code` is not the body of a join point that satisfies `isJpCases`

structure JpCasesAlt where
  decl           : FunDecl
  default        : Bool
  dependsOnDiscr : Bool

abbrev Ctor2JpCasesAlt := FVarIdMap (NameMap JpCasesAlt)

open Internalize in
/--
Construct an auxiliary join point for a particular alternative in a join-point that satisfies `isJpCases?`.
- `decls` is the prefix (before the `cases`). See `isJpCases?`.
- `params` are the parameters of the main join point that satisfies `isJpCases?`.
- `targetParamIdx` is the index of the parameter that we are expanding to `fields`
- `fields` are the fields/parameter of the alternative.
- `k` is the body of the alternative.
- `default` is true if it is a default alternative.
-/
private def mkJpAlt (decls : Array CodeDecl) (params : Array Param) (targetParamIdx : Nat) (fields : Array Param) (k : Code) (default : Bool) : CompilerM JpCasesAlt := do
  go |>.run' {}
where
  go : InternalizeM JpCasesAlt := do
    let mut paramsNew := #[]
    let singleton : FVarIdSet := ({} : FVarIdSet).insert params[targetParamIdx]!.fvarId
    let dependsOnDiscr := k.dependsOn singleton || decls.any (·.dependsOn singleton)
    for i in [:params.size] do
      let param := params[i]!
      if targetParamIdx == i then
        if dependsOnDiscr then
          paramsNew := paramsNew.push (← internalizeParam param)
        paramsNew := paramsNew ++ (← fields.mapM internalizeParam)
      else
        paramsNew := paramsNew.push (← internalizeParam param)
    let decls ← decls.mapM internalizeCodeDecl
    let k ← internalizeCode k
    let value := LCNF.attachCodeDecls decls k
    return { decl := (← mkAuxJpDecl paramsNew value), default, dependsOnDiscr }

/-- Create the arguments for a jump to an auxiliary join point created using `mkJpAlt`. -/
private def mkJmpNewArgs (args : Array Arg) (targetParamIdx : Nat) (fields : Array Arg) (dependsOnTarget : Bool) : Array Arg :=
  if dependsOnTarget then
    args[:targetParamIdx+1] ++ fields ++ args[targetParamIdx+1:]
  else
    args[:targetParamIdx] ++ fields ++ args[targetParamIdx+1:]

/--
Create the arguments for a jump to an auxiliary join point created using `mkJpAlt`.
This function is used to create jumps from the join point satisfying `isJpCases?` to the new auxiliary join points created using `mkJpAlt`.
-/
private def mkJmpArgsAtJp (params : Array Param) (targetParamIdx : Nat) (fields : Array Param) (dependsOnTarget : Bool) : Array Arg := Id.run do
  mkJmpNewArgs (params.map (Arg.fvar ·.fvarId)) targetParamIdx (fields.map (Arg.fvar ·.fvarId)) dependsOnTarget

/--
Try to optimize `jpCases` join points.
We say a join point is a `jpCases` when it satisfies the predicate `isJpCases`.
If we have a jump to `jpCases` with a constructor, then we can optimize the code by creating an new join point for
the constructor.
Example: suppose we have
```lean
jp _jp.1 y :=
  let x.1 := true
  cases y
  | nil => let x.2 := g x.1; return x.2
  | cons h t => let x.3 := h x.1; return x.3
...
cases x.4
| ctor1 =>
  let x.5 := cons z.1 z.2
  jmp _jp.1 x.5
| ctor2 =>
  let x.6 := f x.4
  jmp _jp.1 x.6
```
This `simpJpCases?` converts it to
```lean
jp _jp.2 h t :=
  let x.1 := true
  let x.3 := h x.1
  return x.3
jp _jp.1 y :=
  let x.1 := true
  cases y
  | nil => let x.2 := g x.1; return x.2
  | cons h t => jmp _jp.2 h t
...
cases x.4
| ctor1 =>
  -- The constructor has been eliminated here
  jmp _jp.2 z.1 z.2
| ctor2 =>
  let x.6 := f x.4
  jmp _jp.1 x.6
```
Note that if all jumps to the join point are with constructors,
then the join point is eliminated as dead code.
-/
partial def simpJpCases? (code : Code) : CompilerM (Option Code) := do
  let map ← collectJpCasesInfo code
  unless map.isCandidate do return none
  traceM `Compiler.simp.jpCases do
    let mut msg : MessageData := "candidates"
    for (fvarId, info) in map.toList do
      msg := msg ++ indentD m!"{mkFVar fvarId} ↦ {info.ctorNames.toList}"
    return msg
  visit code map |>.run' {} |>.run {}
where
  visit (code : Code) : ReaderT JpCasesInfoMap (StateRefT Ctor2JpCasesAlt DiscrM) Code := do
    match code with
    | .let decl k =>
      return code.updateLet! decl (← visit k)
    | .fun decl k =>
      let value ← visit decl.value
      let decl ← decl.updateValue value
      return code.updateFun! decl (← visit k)
    | .jp decl k =>
      if let some code ← visitJp? decl k then
        return code
      else
        let value ← visit decl.value
        let decl ← decl.updateValue value
        return code.updateFun! decl (← visit k)
    | .cases c =>
      let alts ← c.alts.mapMonoM fun alt =>
        match alt with
        | .alt ctorName ps k =>
          withDiscrCtor c.discr ctorName ps do
            return alt.updateCode (← visit k)
        | .default k => return alt.updateCode (← visit k)
      return code.updateAlts! alts
    | .return _ | .unreach _ => return code
    | .jmp fvarId args =>
      let some code ← visitJmp? fvarId args | return code
      return code

  visitJp? (decl : FunDecl) (k : Code) : ReaderT JpCasesInfoMap (StateRefT Ctor2JpCasesAlt DiscrM) (Option Code) := do
    let some info := (← read).find? decl.fvarId | return none
    if info.ctorNames.isEmpty then return none
    -- This join point satisfies `isJpCases?` and there are jumps with constructors in `info` to it.
    let (decls, cases) := extractJpCases decl.value
    let mut jpAltMap := {}
    let mut jpAltDecls := #[]
    let mut altsNew := #[]
    for alt in cases.alts do
      match alt with
      | .default k =>
        let k ← visit k
        let explicitCtorNames := cases.getCtorNames
        if info.ctorNames.any fun ctorNameInJump => !explicitCtorNames.contains ctorNameInJump then
          let jpAlt ← mkJpAlt decls decl.params info.paramIdx #[] k (default := true)
          jpAltDecls := jpAltDecls.push (.jp jpAlt.decl)
          eraseCode k
          for ctorNameInJmp in info.ctorNames do
            unless explicitCtorNames.contains ctorNameInJmp do
              jpAltMap := jpAltMap.insert ctorNameInJmp jpAlt
          let args := mkJmpArgsAtJp decl.params info.paramIdx #[] jpAlt.dependsOnDiscr
          altsNew := altsNew.push (alt.updateCode (.jmp jpAlt.decl.fvarId args))
        else
          altsNew := altsNew.push (alt.updateCode k)
      | .alt ctorName fields k =>
        let k ← withDiscrCtor cases.discr ctorName fields <| visit k
        if info.ctorNames.contains ctorName then
          let jpAlt ← mkJpAlt decls decl.params info.paramIdx fields k (default := false)
          jpAltDecls := jpAltDecls.push (.jp jpAlt.decl)
          jpAltMap := jpAltMap.insert ctorName jpAlt
          let args := mkJmpArgsAtJp decl.params info.paramIdx fields jpAlt.dependsOnDiscr
          eraseCode k
          altsNew := altsNew.push (alt.updateCode (.jmp jpAlt.decl.fvarId args))
        else
          altsNew := altsNew.push (alt.updateCode k)
    modify fun s => s.insert decl.fvarId jpAltMap
    let value := LCNF.attachCodeDecls decls (.cases { cases with alts := altsNew })
    let decl ← decl.updateValue value
    let code := .jp decl (← visit k)
    return LCNF.attachCodeDecls jpAltDecls code

  visitJmp? (fvarId : FVarId) (args : Array Arg) : ReaderT JpCasesInfoMap (StateRefT Ctor2JpCasesAlt DiscrM) (Option Code) := do
    let some ctorJpAltMap := (← get).find? fvarId | return none
    let some info := (← read).find? fvarId | return none
    let .fvar argFVarId := args[info.paramIdx]! | return none
    let some ctorInfo ← findCtor? argFVarId | return none
    let some jpAlt := ctorJpAltMap.find? ctorInfo.getName | return none
    if jpAlt.default then
      let argsNew := mkJmpNewArgs args info.paramIdx #[] jpAlt.dependsOnDiscr
      return some <| .jmp jpAlt.decl.fvarId argsNew
    else
      match ctorInfo with
      | .ctor ctorVal ctorArgs =>
         let fields := ctorArgs[ctorVal.numParams:]
         let argsNew := mkJmpNewArgs args info.paramIdx fields jpAlt.dependsOnDiscr
         return some <| .jmp jpAlt.decl.fvarId argsNew
      | .natVal 0 =>
        let argsNew := mkJmpNewArgs args info.paramIdx #[] jpAlt.dependsOnDiscr
        return some <| .jmp jpAlt.decl.fvarId argsNew
      | .natVal (n+1) =>
        let auxDecl ← mkAuxLetDecl (.value (.natVal n))
        let argsNew := mkJmpNewArgs args info.paramIdx #[.fvar auxDecl.fvarId] jpAlt.dependsOnDiscr
        return some <| .let auxDecl (.jmp jpAlt.decl.fvarId argsNew)

end Simp

builtin_initialize
  registerTraceClass `Compiler.simp.jpCases

end Lean.Compiler.LCNF

