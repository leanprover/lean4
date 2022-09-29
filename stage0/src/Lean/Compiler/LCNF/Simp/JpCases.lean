/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.LCNF.DependsOn
import Lean.Compiler.LCNF.InferType
import Lean.Compiler.LCNF.Simp.Basic

namespace Lean.Compiler.LCNF
namespace Simp

/--
Given the function declaration `decl`, return `true` if it is of the form
```
f y :=
  ... /- This part is not bigger than smallThreshold. -/
  cases y
  | ... => ...
  ...
```
-/
def isJpCases (decl : FunDecl) : CompilerM Bool := do
  if decl.params.size != 1 then
    return false
  else
    let param := decl.params[0]!
    let small := (← getConfig).smallThreshold
    let rec go (code : Code) (prefixSize : Nat) : Bool :=
      prefixSize <= small &&
      match code with
      | .let _ k => go k (prefixSize + 1) /- TODO: we should have uniform heuristics for estimating the size. -/
      | .cases c => c.discr == param.fvarId
      | _ => false
    return go decl.value 0

abbrev JpCasesInfo := FVarIdMap NameSet

/-- Return `true` if the collected information suggests opportunities for the `JpCases` optimization. -/
def JpCasesInfo.isCandidate (info : JpCasesInfo) : Bool :=
  info.any fun _ s => !s.isEmpty

/--
Return a map containing entries `jpFVarId ↦ ctorNames` where `jpFVarId` is the id of join point
in code that satisfies `isJpCases`, and `ctorNames` is a set of constructor names such that
there is a jump `.jmp jpFVarId #[x]` in `code` and `x` is a constructor application.
-/
partial def collectJpCasesInfo (code : Code) : CompilerM JpCasesInfo := do
  let (_, s) ← go code |>.run {}
  return s
where
  go (code : Code) : StateRefT JpCasesInfo CompilerM Unit := do
    match code with
    | .let _ k => go k
    | .fun decl k => go decl.value; go k
    | .jp decl k =>
      if (← isJpCases decl) then
        modify fun s => s.insert decl.fvarId {}
      go decl.value; go k
    | .cases c => c.alts.forM fun alt => go alt.getCode
    | .return .. | .unreach .. => return ()
    | .jmp fvarId args =>
      if args.size == 1 then
      if let some ctorNames := (← get).find? fvarId then
        let arg ← findExpr args[0]!
        let some (cval, _) := arg.constructorApp? (← getEnv) | return ()
        modify fun s => s.insert fvarId <| ctorNames.insert cval.name

/--
Extract the let-declarations and `cases` for a join point body that satisfies `isJpCases`.
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
private def mkJpAlt (decls : Array CodeDecl) (discr : Param) (fields : Array Param) (k : Code) (default : Bool) : CompilerM JpCasesAlt := do
  go |>.run' {}
where
  go : InternalizeM JpCasesAlt := do
    let s : FVarIdSet := {}
    let mut paramsNew := #[]
    let dependsOnDiscr := k.dependsOn (s.insert discr.fvarId)
    if dependsOnDiscr then
      paramsNew := paramsNew.push (← internalizeParam discr)
    paramsNew := paramsNew ++ (← fields.mapM internalizeParam)
    let decls ← decls.mapM internalizeCodeDecl
    let k ← internalizeCode k
    let value := LCNF.attachCodeDecls decls k
    return { decl := (← mkAuxJpDecl paramsNew value), default, dependsOnDiscr }

/--
Try to optimize `jpCases` join points.
We say a join point is a `jpCases` when it satifies the predicate `isJpCases`.
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
  let info ← collectJpCasesInfo code
  unless info.isCandidate do return none
  traceM `Compiler.simp.jpCases do
    let mut msg : MessageData := "candidates"
    for (fvarId, ctorName) in info.toList do
      msg := msg ++ indentD m!"{mkFVar fvarId} ↦ {ctorName.toList}"
    return msg
  visit code info |>.run' {}
where
  visit (code : Code) : ReaderT JpCasesInfo (StateRefT Ctor2JpCasesAlt CompilerM) Code := do
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
      let alts ← c.alts.mapMonoM fun alt => return alt.updateCode (← visit alt.getCode)
      return code.updateAlts! alts
    | .return _ | .unreach _ => return code
    | .jmp fvarId args =>
      let some code ← visitJmp? fvarId args | return code
      return code

  visitJp? (decl : FunDecl) (k : Code) : ReaderT JpCasesInfo (StateRefT Ctor2JpCasesAlt CompilerM) (Option Code) := do
    let some s := (← read).find? decl.fvarId | return none
    if s.isEmpty then return none
    -- This join point satisfies `isJp` and there jumps with constructors in `s` to it.
    let p := decl.params[0]!
    let (decls, cases) := extractJpCases decl.value
    let mut jpAltMap := {}
    let mut jpAltDecls := #[]
    let mut altsNew := #[]
    for alt in cases.alts do
      match alt with
      | .default k =>
        let k ← visit k
        let explicitCtorNames := cases.getCtorNames
        if s.any fun ctorNameInJump => !explicitCtorNames.contains ctorNameInJump then
          let jpAlt ← mkJpAlt decls p #[] k (default := true)
          jpAltDecls := jpAltDecls.push (.jp jpAlt.decl)
          eraseCode k
          for ctorNameInJmp in s do
            unless explicitCtorNames.contains ctorNameInJmp do
              jpAltMap := jpAltMap.insert ctorNameInJmp jpAlt
          let args := if jpAlt.dependsOnDiscr then #[.fvar p.fvarId] else #[]
          altsNew := altsNew.push (alt.updateCode (.jmp jpAlt.decl.fvarId args))
        else
          altsNew := altsNew.push (alt.updateCode k)
      | .alt ctorName fields k =>
        let k ← visit k
        if s.contains ctorName then
          let jpAlt ← mkJpAlt decls p fields k (default := false)
          jpAltDecls := jpAltDecls.push (.jp jpAlt.decl)
          jpAltMap := jpAltMap.insert ctorName jpAlt
          let mut args := fields.map (mkFVar ·.fvarId)
          if jpAlt.dependsOnDiscr then
            args := #[mkFVar p.fvarId] ++ args
          eraseCode k
          altsNew := altsNew.push (alt.updateCode (.jmp jpAlt.decl.fvarId args))
        else
          altsNew := altsNew.push (alt.updateCode k)
    modify fun s => s.insert decl.fvarId jpAltMap
    let value := LCNF.attachCodeDecls decls (.cases { cases with alts := altsNew })
    let decl ← decl.updateValue value
    let code := .jp decl (← visit k)
    return LCNF.attachCodeDecls jpAltDecls code

  visitJmp? (fvarId : FVarId) (args : Array Expr) : ReaderT JpCasesInfo (StateRefT Ctor2JpCasesAlt CompilerM) (Option Code) := do
    let some ctorJpAltMap := (← get).find? fvarId | return none
    assert! args.size == 1
    let arg ← findExpr args[0]!
    let some (ctorVal, ctorArgs) := arg.constructorApp? (← getEnv) (useRaw := true) | return none
    let some jpAlt := ctorJpAltMap.find? ctorVal.name | return none
    if jpAlt.default then
      if jpAlt.dependsOnDiscr then
        return some <| .jmp jpAlt.decl.fvarId args
      else
        return some <| .jmp jpAlt.decl.fvarId #[]
    else
      let fields := ctorArgs[ctorVal.numParams:]
      -- Recall that if `arg` is a `Nat` literal, then `ctorArgs` is a literal too.
      -- We use a for-loop because we may have other special cases in the future.
      let mut auxDecls := #[]
      let mut fieldsNew := #[]
      for field in fields do
        if field.isFVar then
          fieldsNew := fieldsNew.push field
        else
          let letDecl ← mkAuxLetDecl field
          auxDecls := auxDecls.push (CodeDecl.let letDecl)
          fieldsNew := fieldsNew.push (.fvar letDecl.fvarId)
      let code ← if jpAlt.dependsOnDiscr then
        pure <| .jmp jpAlt.decl.fvarId (args ++ fieldsNew)
      else
        pure <| .jmp jpAlt.decl.fvarId fieldsNew
      return some <| LCNF.attachCodeDecls auxDecls code

end Simp

builtin_initialize
  registerTraceClass `Compiler.simp.jpCases

end Lean.Compiler.LCNF

