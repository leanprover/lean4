/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.LCNF.Renaming
import Lean.Compiler.LCNF.ElimDead
import Lean.Compiler.LCNF.AlphaEqv
import Lean.Compiler.LCNF.PrettyPrinter
import Lean.Compiler.LCNF.Bind
import Lean.Compiler.LCNF.Internalize
import Lean.Compiler.LCNF.Simp.JpCases
import Lean.Compiler.LCNF.Simp.DiscrM
import Lean.Compiler.LCNF.Simp.FunDeclInfo
import Lean.Compiler.LCNF.Simp.Config

namespace Lean.Compiler.LCNF
namespace Simp

structure Context where
  /--
  Name of the declaration being simplified.
  We currently use this information because we are generating phase1 declarations  on demand,
  and it may trigger non-termination when trying to access the phase1 declaration.
  -/
  declName : Name
  config : Config := {}
  /--
  Stack of global declarations being recursively inlined.
  -/
  inlineStack : List Name := []
  /--
  Mapping from declaration names to number of occurrences at `inlineStack`
  -/
  inlineStackOccs : PHashMap Name Nat := {}

structure State where
  /--
  Free variable substitution. We use it to implement inlining and removing redundant variables `let _x.i := _x.j`
  -/
  subst : FVarSubst := {}
  /--
  Track used local declarations to be able to eliminate dead variables.
  -/
  used : UsedLocalDecls := {}
  /--
  Mapping containing free variables ids that need to be renamed (i.e., the `binderName`).
  We use this map to preserve user provide names.
  -/
  binderRenaming : Renaming := {}
  /--
  Mapping used to decide whether a local function declaration must be inlined or not.
  -/
  funDeclInfoMap : FunDeclInfoMap := {}
  /--
  `true` if some simplification was performed in the current simplification pass.
  -/
  simplified : Bool := false
  /--
  Number of visited `let-declarations` and terminal values.
  This is a performance counter, and currently has no impact on code generation.
  -/
  visited : Nat := 0
  /--
  Number of definitions inlined.
  This is a performance counter.
  -/
  inline : Nat := 0
  /--
  Number of local functions inlined.
  This is a performance counter.
  -/
  inlineLocal : Nat := 0

abbrev SimpM := ReaderT Context $ StateRefT State DiscrM

@[always_inline]
instance : Monad SimpM := let i := inferInstanceAs (Monad SimpM); { pure := i.pure, bind := i.bind }

instance : MonadFVarSubst SimpM false where
  getSubst := return (← get).subst

instance : MonadFVarSubstState SimpM where
  modifySubst f := modify fun s => { s with subst := f s.subst }

/-- Set the `simplified` flag to `true`. -/
def markSimplified : SimpM Unit :=
  modify fun s => { s with simplified := true }

/-- Increment `visited` performance counter. -/
def incVisited : SimpM Unit :=
  modify fun s => { s with visited := s.visited + 1 }

/-- Increment `inline` performance counter. It is the number of inlined global declarations. -/
def incInline : SimpM Unit :=
  modify fun s => { s with inline := s.inline + 1 }

/-- Increment `inlineLocal` performance counter. It is the number of inlined local function and join point declarations. -/
def incInlineLocal : SimpM Unit :=
  modify fun s => { s with inlineLocal := s.inlineLocal + 1 }

/-- Mark the local function declaration or join point with the given id as a "must inline". -/
def addMustInline (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with funDeclInfoMap := s.funDeclInfoMap.addMustInline fvarId }

/-- Add a new occurrence of local function `fvarId`. -/
def addFunOcc (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with funDeclInfoMap := s.funDeclInfoMap.add fvarId }

/-- Add a new occurrence of local function `fvarId` in argument position . -/
def addFunHoOcc (fvarId : FVarId) : SimpM Unit :=
  modify fun s => { s with funDeclInfoMap := s.funDeclInfoMap.addHo fvarId }

@[inherit_doc FunDeclInfoMap.update]
partial def updateFunDeclInfo (code : Code) (mustInline := false) : SimpM Unit := do
  let map ← modifyGet fun s => (s.funDeclInfoMap, { s with funDeclInfoMap := {} })
  let map ← map.update code mustInline
  modify fun s => { s with funDeclInfoMap := map }

/--
Execute `x` with an updated `inlineStack`. If `value` is of the form `const ...`, add `const` to the stack.
Otherwise, do not change the `inlineStack`.
-/
@[inline] def withInlining (value : LetValue) (recursive : Bool) (x : SimpM α) : SimpM α := do
  if let .const declName _ _ := value then
    let numOccs ← check declName
    withReader (fun ctx => { ctx with inlineStack := declName :: ctx.inlineStack, inlineStackOccs := ctx.inlineStackOccs.insert declName numOccs }) x
  else
    x
where
  check (declName : Name) : SimpM Nat := do
    trace[Compiler.simp.inline] "{declName}"
    let numOccs := (← read).inlineStackOccs.find? declName |>.getD 0
    let numOccs := numOccs + 1
    let inlineIfReduce ← if let some decl ← getDecl? declName then pure decl.inlineIfReduceAttr else pure false
    if recursive && inlineIfReduce && numOccs > (← getConfig).maxRecInlineIfReduce then
      throwError "function `{declName}` has been recursively inlined more than #{(← getConfig).maxRecInlineIfReduce}, consider removing the attribute `[inline_if_reduce]` from this declaration or increasing the limit using `set_option compiler.maxRecInlineIfReduce <num>`"
    return numOccs

/--
Similar to the default `Lean.withIncRecDepth`, but include the `inlineStack` in the error message.
-/
@[inline] def withIncRecDepth (x : SimpM α) : SimpM α := do
  let curr ← MonadRecDepth.getRecDepth
  let max  ← MonadRecDepth.getMaxRecDepth
  if curr == max then
    throwMaxRecDepth
  else
    MonadRecDepth.withRecDepth (curr+1) x
where
  throwMaxRecDepth : SimpM α := do
    match (← read).inlineStack with
    | [] => throwError maxRecDepthErrorMessage
    | declName :: stack =>
      let mut fmt  := f!"{declName}\n"
      let mut prev := declName
      let mut ellipsis := false
      for declName in stack do
        if prev == declName then
          unless ellipsis do
            ellipsis := true
            fmt := fmt ++ "...\n"
        else
          fmt := fmt ++ f!"{declName}\n"
          prev := declName
          ellipsis := false
      throwError "maximum recursion depth reached in the code generator\nfunction inline stack:\n{fmt}"

/--
Execute `x` with `fvarId` set as `mustInline`.
After execution the original setting is restored.
-/
def withAddMustInline (fvarId : FVarId) (x : SimpM α) : SimpM α := do
  let saved? := (← get).funDeclInfoMap.map.find? fvarId
  try
    addMustInline fvarId
    x
  finally
    modify fun s => { s with funDeclInfoMap := s.funDeclInfoMap.restore fvarId saved? }

/--
Return true if the given local function declaration or join point id is marked as
`once` or `mustInline`. We use this information to decide whether to inline them.
-/
def isOnceOrMustInline (fvarId : FVarId) : SimpM Bool := do
  match (← get).funDeclInfoMap.map.find? fvarId with
    | some .once | some .mustInline  => return true
    | _ => return false

/--
Return `true` if the given code is considered "small".
-/
def isSmall (code : Code) : SimpM Bool :=
  return code.sizeLe (← getConfig).smallThreshold

/--
Return `true` if the given local function declaration should be inlined.
-/
def shouldInlineLocal (decl : FunDecl) : SimpM Bool := do
  if (← isOnceOrMustInline decl.fvarId) then
    return true
  else
    isSmall decl.value

/--
LCNF "Beta-reduce". The equivalent of `(fun params => code) args`.
If `mustInline` is true, the local function declarations in the resulting code are marked as `.mustInline`.
See comment at `updateFunDeclInfo`.
-/
def betaReduce (params : Array Param) (code : Code) (args : Array Arg) (mustInline := false) : SimpM Code := do
  let mut subst := {}
  for param in params, arg in args do
    subst := subst.insert param.fvarId arg.toExpr
  let code ← code.internalize subst
  updateFunDeclInfo code mustInline
  return code

/--
Erase the given let-declaration from the local context,
and set the `simplified` flag to true.
-/
def eraseLetDecl (decl : LetDecl) : SimpM Unit := do
  LCNF.eraseLetDecl decl
  markSimplified

/--
Erase the given local function declaration from the local context,
and set the `simplified` flag to true.
-/
def eraseFunDecl (decl : FunDecl) : SimpM Unit := do
  LCNF.eraseFunDecl decl
  markSimplified

/--
Similar to `LCNF.addFVarSubst`. That is, add the entry
`fvarId ↦ fvarId'` to the free variable substitution.
If `fvarId` has a non-internal binder name `n`, but `fvarId'` does not,
this method also adds the entry `fvarId' ↦ n` to the `binderRenaming` map.
The goal is to preserve user provided names.
-/
def addFVarSubst (fvarId : FVarId) (fvarId' : FVarId) : SimpM Unit := do
  LCNF.addFVarSubst fvarId fvarId'
  let binderName ← getBinderName fvarId
  unless binderName.isInternal do
    let binderName' ← getBinderName fvarId'
    if binderName'.isInternal then
      modify fun s => { s with binderRenaming := s.binderRenaming.insert fvarId' binderName }
