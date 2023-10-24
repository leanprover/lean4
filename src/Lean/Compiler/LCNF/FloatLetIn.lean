/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
import Lean.Compiler.LCNF.CompilerM
import Lean.Compiler.LCNF.FVarUtil
import Lean.Compiler.LCNF.PassManager
import Lean.Compiler.LCNF.Types

namespace Lean.Compiler.LCNF

namespace FloatLetIn

/--
The decision of the float mechanism.
-/
inductive Decision where
|
  /--
  Push into the arm with name `name`.
  -/
  arm (name : Name)
| /--
  Push into the default arm.
  -/
  default
|
  /--
  Dont move this declaration it is needed where it is right now.
  -/
  dont
|
  /--
  No decision has been made yet.
  -/
  unknown
deriving Hashable, BEq, Inhabited, Repr

def Decision.ofAlt : Alt → Decision
| .alt name _ _ => .arm name
| .default _ => .default

/--
The context for `BaseFloatM`.
-/
structure BaseFloatContext where
  /--
  All the declarations that were collected in the current LCNF basic
  block up to the current statement (in reverse order for efficiency).
  -/
  decls : List CodeDecl := []

/--
The state for `FloatM`
-/
structure FloatState where
  /--
  A map from identifiers of declarations to their current decision.
  -/
  decision : HashMap FVarId Decision
  /--
  A map from decisions (excluding `unknown`) to the declarations with
  these decisions (in correct order). Basically:
  - Which declarations do we not move
  - Which declarations do we move into a certain arm
  - Which declarations do we move into the default arm
  -/
  newArms : HashMap Decision (List CodeDecl)

/--
Use to collect relevant declarations for the floating mechanism.
-/
abbrev BaseFloatM :=  ReaderT BaseFloatContext CompilerM

/--
Use to compute the actual floating.
-/
abbrev FloatM := StateRefT FloatState BaseFloatM

/--
Add `decl` to the list of declarations and run `x` with that updated context.
-/
def withNewCandidate (decl : CodeDecl) (x : BaseFloatM α) : BaseFloatM α :=
  withReader (fun r => { r with decls := decl :: r.decls }) do
    x

/--
Run `x` with an empty list of declarations.
-/
def withNewScope (x : BaseFloatM α) : BaseFloatM α := do
  withReader (fun _ => {}) do
    x

/--
Whether to ignore `decl` for the floating mechanism. We want to do this if:
- `decl`' is storing a typeclass instance
- `decl` is a projection from a variable that is storing a typeclass instance
-/
def ignore? (decl : LetDecl) : BaseFloatM Bool :=  do
   if (← isArrowClass? decl.type).isSome then
     return true
   else if let .proj _ _ fvarId := decl.value then
     return (← isArrowClass? (← getType fvarId)).isSome
   else
     return false

/--
Compute the initial decision for all declarations that `BaseFloatM` collected
up to this point, with respect to `cs`. The initial decisions are:
- `dont` if the declaration is detected by `ignore?`
- `dont` if the declaration is the discriminant of `cs` since we obviously need
  the discriminant to be computed before the match.
- `dont` if we see the declaration being used in more than one cases arm
- `arm` or `default` if we see the declaration only being used in exactly one cases arm
- `unknown` otherwise
-/
def initialDecisions (cs : Cases) : BaseFloatM (HashMap FVarId Decision) := do
  let mut map := mkHashMap (← read).decls.length
  let folder val acc := do
    if let .let decl := val then
      if (← ignore? decl) then
        return acc.insert decl.fvarId .dont
    return acc.insert val.fvarId .unknown

  map ← (← read).decls.foldrM (init := map) folder
  if map.contains cs.discr then
    map := map.insert cs.discr .dont
  (_, map) ← goCases cs |>.run map
  return map
where
  goFVar (plannedDecision : Decision) (var : FVarId) : StateRefT (HashMap FVarId Decision) BaseFloatM Unit := do
    if let some decision := (← get).find? var then
      if decision == .unknown then
        modify fun s => s.insert var plannedDecision
      else if decision != plannedDecision then
          modify fun s => s.insert var .dont
      -- otherwise we already have the proper decision

  goAlt (alt : Alt) : StateRefT (HashMap FVarId Decision) BaseFloatM Unit :=
    forFVarM (goFVar (.ofAlt alt)) alt
  goCases (cs : Cases) : StateRefT (HashMap FVarId Decision) BaseFloatM Unit :=
    cs.alts.forM goAlt

/--
Compute the initial new arms. This will just set up a map from all arms of
`cs` to empty `Array`s, plus one additional entry for `dont`.
-/
def initialNewArms (cs : Cases) : HashMap Decision (List CodeDecl) := Id.run do
  let mut map := mkHashMap (cs.alts.size + 1)
  map := map.insert .dont []
  cs.alts.foldr (init := map) fun val acc => acc.insert (.ofAlt val) []

/--
Will:
- put `decl` into the `dont` arm
- decide that any free variable that occurs in `decl` and is a declaration
  of interest as not getting moved either.
```
let x := ...
let y := ...
let z := x + y
cases z with
| n => z * x
| m => z * y
```
Here `x` and `y` are originally marked as getting floated into `n` and `m`
respectively but since `z` can't be moved we don't want that to move `x` and `y`.
-/
def dontFloat (decl : CodeDecl) : FloatM Unit := do
  forFVarM goFVar decl
  modify fun s => { s with newArms := s.newArms.insert .dont (decl :: s.newArms.find! .dont) }
where
  goFVar (fvar : FVarId) : FloatM Unit := do
    if (← get).decision.contains fvar then
      modify fun s => { s with decision := s.decision.insert fvar .dont }

/--
Will:
- put `decl` into the arm it is marked to be moved into
- for any variables that might occur in `decl` and are of interest:
  - if they are already meant to be floated into the same arm or not at all leave them untouched:
    ```
    let x := ...
    let y := x + z
    cases z with
    | n => x * y
    | m => z
    ```
    If we are at `y` `x` is already marked to be floated into `n` as well.
  - if there hasn't be a decision yet, that is they are marked with `.unknown` we float
    them into the same arm as the current value:
    ```
    let x := ..
    let y := x + 2
    cases z with
    | n => y
    | m => z
    ```
    Here `x` is initially marked as `.unknown` since it occurs in no branch, however
    since we want to move `y` into the `n` branch we can also decide to move `x`
    into the `n` branch. Note that this decision might be revoked later on in the case of:
    ```
    let x := ..
    let a := x + 1
    let y := x + 2
    cases z with
    | n => y
    | m => a
    ```
    When we visit `a` `x` is now marked as getting moved into `n` but since it also occurs
    in `a` which wants to be moved somewhere else we will instead decide to not move `x`
    at all.
  - if they are meant to be floated somewhere else decide that they won't get floated:
    ```
    let x := ...
    let y := x + z
    cases z with
    | n => y
    | m => x
    ```
    If we are at `y` `x` is still marked to be moved but we don't want that.
-/
def float (decl : CodeDecl) : FloatM Unit := do
  let arm := (← get).decision.find! decl.fvarId
  forFVarM (goFVar · arm) decl
  modify fun s => { s with newArms := s.newArms.insert arm (decl :: s.newArms.find! arm) }
where
  goFVar (fvar : FVarId) (arm : Decision) : FloatM Unit := do
    let some decision := (← get).decision.find? fvar | return ()
    if decision != arm then
      modify fun s => { s with decision := s.decision.insert fvar .dont }
    else if decision == .unknown then
      modify fun s => { s with decision := s.decision.insert fvar arm }

/--
Iterate through `decl`, pushing local declarations that are only used in one
control flow arm into said arm in order to avoid useless computations.
-/
partial def floatLetIn (decl : Decl) : CompilerM Decl := do
  let newValue ← go decl.value |>.run {}
  return { decl with value := newValue }
where
  /--
  Iterate through the collected declarations,
  determining from the bottom up whether they (and the declarations they refer to)
  should get moved down into the arms of the cases statement or not.
  -/
  goCases : FloatM Unit := do
    for decl in (← read).decls do
      let currentDecision := (← get).decision.find! decl.fvarId
      if currentDecision == .unknown then
        /-
        If the decision is still unknown by now this means `decl` is
        unused in its continuation and can hence be removed.
        -/
        eraseCodeDecl decl
      else if currentDecision == .dont then
        dontFloat decl
      else
        float decl

  go (code : Code) : BaseFloatM Code := do
    match code with
    | .let decl k =>
      withNewCandidate (.let decl) do
        go k
    | .jp decl k =>
      let value ← withNewScope do
        go decl.value
      let decl ← decl.updateValue value
      withNewCandidate (.jp decl) do
        go k
    | .fun decl k =>
      let value ← withNewScope do
        go decl.value
      let decl ← decl.updateValue value
      withNewCandidate (.fun decl) do
        go k
    | .cases cs =>
      let base := {
        decision := (← initialDecisions cs)
        newArms := initialNewArms cs
      }
      let (_, res) ← goCases |>.run base
      let remainders := res.newArms.find! .dont
      let altMapper alt := do
        let decision := .ofAlt alt
        let newCode := res.newArms.find! decision
        trace[Compiler.floatLetIn] "Size of code that was pushed into arm: {repr decision} {newCode.length}"
        let fused ← withNewScope do
          go (attachCodeDecls newCode.toArray alt.getCode)
        return alt.updateCode fused
      let newAlts ← cs.alts.mapM altMapper
      let mut newCases := Code.updateCases! code cs.resultType cs.discr newAlts
      return attachCodeDecls remainders.toArray newCases
    | .jmp .. | .return .. | .unreach .. =>
    return attachCodeDecls (← read).decls.toArray.reverse code

end FloatLetIn

def Decl.floatLetIn (decl : Decl) : CompilerM Decl := do
  FloatLetIn.floatLetIn decl

def floatLetIn (phase := Phase.base) (occurrence := 0) : Pass :=
  .mkPerDeclaration `floatLetIn Decl.floatLetIn phase occurrence

builtin_initialize
  registerTraceClass `Compiler.floatLetIn (inherited := true)

end Lean.Compiler.LCNF
