/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.Specialize
import Lean.Compiler.LCNF.FixedParams
import Lean.Compiler.LCNF.InferType

namespace Lean.Compiler.LCNF

/--
Each parameter is associated with a `SpecParamInfo`. This information is used by `LCNF/Specialize.lean`.
-/
inductive SpecParamInfo where
  /--
  A parameter that is an type class instance (or an arrow that produces a type class instance),
  and is fixed in recursive declarations. By default, Lean always specializes this kind of argument.
  -/
  | fixedInst
  /--
  A parameter that is a function and is fixed in recursive declarations. If the user tags a declaration
  with `@[specialize]` without specifying which arguments should be specialized, Lean will specialize
  `.fixedHO` arguments in addition to `.fixedInst`.
  -/
  | fixedHO
  /--
  Computationally irrelevant parameters that are fixed in recursive declarations,
  *and* there is a `fixedInst`, `fixedHO`, or `user` param that depends on it.
  -/
  | fixedNeutral
  /--
  An argument that has been specified in the `@[specialize]` attribute. Lean specializes it even if it is
  not fixed in recursive declarations. Non-termination can happen, and Lean interrupts it with an error message
  based on the stack depth.
  -/
  | user
  /--
  Parameter is not going to be specialized.
  -/
  | other
  deriving Inhabited, Repr

instance : ToMessageData SpecParamInfo where
  toMessageData
    | .fixedInst => "I"
    | .fixedHO => "H"
    | .fixedNeutral => "N"
    | .user => "U"
    | .other => "O"

structure SpecState where
  specInfo : PHashMap Name (Array SpecParamInfo) := {}
  deriving Inhabited

structure SpecEntry where
  declName   : Name
  paramsInfo : Array SpecParamInfo
  deriving Inhabited

namespace SpecState

def addEntry (s : SpecState) (e : SpecEntry) : SpecState :=
  match s with
  | { specInfo } => { specInfo := specInfo.insert e.declName e.paramsInfo }

end SpecState

private abbrev declLt (a b : SpecEntry) :=
  Name.quickLt a.declName b.declName

private abbrev sortEntries (entries : Array SpecEntry) : Array SpecEntry :=
  entries.qsort declLt

private abbrev findAtSorted? (entries : Array SpecEntry) (declName : Name) : Option SpecEntry :=
  entries.binSearch { declName, paramsInfo := #[] } declLt

/--
Extension for storing `SpecParamInfo` for declarations being compiled.
Remark: we only store information for declarations that will be specialized.
-/
builtin_initialize specExtension : SimplePersistentEnvExtension SpecEntry SpecState ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := SpecState.addEntry
    addImportedFn := fun _ => {}
    toArrayFn     := fun s => sortEntries s.toArray
  }

/--
Return `true` if `type` is a type tagged with `@[nospecialize]` or an arrow that produces this kind of type.
For example, this function returns true for `Inhabited Nat`, and `Nat → Inhabited Nat`.
-/
private def isNoSpecType (env : Environment) (type : Expr) : Bool :=
  match type with
  | .forallE _ _ b _ => isNoSpecType env b
  | _ =>
    if let .const declName _ := type.getAppFn then
      hasNospecializeAttribute env declName
    else
      false

/-!
*Note*: `fixedNeutral` must have forward dependencies.

The code specializer consider a `fixedNeutral` parameter during code specialization
only if it contains forward dependencies that are tagged as `.user`, `.fixedHO`, or `.fixedInst`.
The motivation is to minimize the number of code specializations that have little or no impact on
performance. For example, let's consider the function.
```
def liftMacroM
    {α : Type} {m : Type → Type}
    [Monad m] [MonadMacroAdapter m] [MonadEnv m] [MonadRecDepth m] [MonadError m]
    [MonadResolveName m] [MonadTrace m] [MonadOptions m] [AddMessageContext m] [MonadLiftT IO m] (x : MacroM α) : m α := do
```
The parameter `α` does not occur in any local instance, and `x` is marked as `.other` since the function
is not tagged as `[specialize]`. There is little value in considering `α` during code specialization,
but if we do many copies of this function will be generated.
Recall users may still force the code specializer to take `α` into account by using `[specialize α]` (`α` has `.user` info),
or `[specialize x]` (`α` has `.fixedNeutral` since `x` is a forward dependency tagged as `.user`),
or `[specialize]` (`α` has `.fixedNeutral` since `x` is a forward dependency tagged as `.fixedHO`).
-/

/--
Return `true` if parameter `j` of the given declaration has a forward dependency at parameter `k`,
and `k` is tagged as `.user`, `.fixedHO`, or `.fixedInst`.

See comment at `.fixedNeutral`.
-/
private def hasFwdDeps (decl : Decl) (paramsInfo : Array SpecParamInfo) (j : Nat) : Bool := Id.run do
  let param := decl.params[j]!
  for k in [j+1 : decl.params.size] do
    if paramsInfo[k]! matches .user | .fixedHO | .fixedInst then
      let param' := decl.params[k]!
      if param'.type.containsFVar param.fvarId then
        return true
  return false

/--
Save parameter information for `decls`.

Remark: this function, similarly to `mkFixedArgMap`,
assumes that if a function `f` was declared in a mutual block, then `decls`
contains all (computationally relevant) functions in the mutual block.
-/
def saveSpecParamInfo (decls : Array Decl) : CompilerM Unit := do
  let mut declsInfo := #[]
  for decl in decls do
    if hasNospecializeAttribute (← getEnv) decl.name then
      declsInfo := declsInfo.push (mkArray decl.params.size .other)
    else
      let specArgs? := getSpecializationArgs? (← getEnv) decl.name
      let contains (i : Nat) : Bool := specArgs?.getD #[] |>.contains i
      let mut paramsInfo : Array SpecParamInfo := #[]
      for i in [:decl.params.size] do
        let param := decl.params[i]!
        let info ←
          if contains i then
            pure .user
          /-
          If the user tagged class (e.g., `Inhabited`) with the `@[nospecialize]` attribute,
          then parameters of this type should not be considered for specialization.
          -/
          else if isNoSpecType (← getEnv) param.type then
            pure .other
          else if isTypeFormerType param.type then
            pure .fixedNeutral
          else if (← isArrowClass? param.type).isSome then
            pure .fixedInst
          /-
          Recall that if `specArgs? == some #[]`, then user annotated function with `@[specialize]`, but did not
          specify which arguments must be specialized besides instances. In this case, we try to specialize
          any "fixed higher-order argument"
          -/
          else if specArgs? == some #[] && param.type matches .forallE .. then
            pure .fixedHO
          else
            pure .other
        paramsInfo := paramsInfo.push info
        pure ()
      declsInfo := declsInfo.push paramsInfo
  if declsInfo.any fun paramsInfo => paramsInfo.any (· matches .user | .fixedInst | .fixedHO) then
    let m := mkFixedParamsMap decls
    for i in [:decls.size] do
      let decl := decls[i]!
      let mut paramsInfo := declsInfo[i]!
      let some mask := m.find? decl.name | unreachable!
      trace[Compiler.specialize.info] "{decl.name} {mask}"
      paramsInfo := paramsInfo.zipWith mask fun info fixed => if fixed || info matches .user then info else .other
      for j in [:paramsInfo.size] do
        let mut info  := paramsInfo[j]!
        if info matches .fixedNeutral && !hasFwdDeps decl paramsInfo j then
          paramsInfo := paramsInfo.set! j .other
      if paramsInfo.any fun info => info matches .fixedInst | .fixedHO | .user then
        trace[Compiler.specialize.info] "{decl.name} {paramsInfo}"
        modifyEnv fun env => specExtension.addEntry env { declName := decl.name, paramsInfo }

def getSpecParamInfoCore? (env : Environment) (declName : Name) : Option (Array SpecParamInfo) :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    if let some entry := findAtSorted? (specExtension.getModuleEntries env modIdx) declName then
      some entry.paramsInfo
    else
      none
  | none => (specExtension.getState env).specInfo.find? declName

def getSpecParamInfo? [Monad m] [MonadEnv m] (declName : Name) : m (Option (Array SpecParamInfo)) :=
  return getSpecParamInfoCore? (← getEnv) declName

def isSpecCandidate [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  return getSpecParamInfoCore? (← getEnv) declName |>.isSome

builtin_initialize
  registerTraceClass `Compiler.specialize.info

end Lean.Compiler.LCNF

