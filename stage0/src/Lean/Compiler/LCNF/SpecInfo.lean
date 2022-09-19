/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.Specialize
import Lean.Compiler.LCNF.FixedArgs
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
  Computationally irrelevant parameters that are fixed in recursive declarations.
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
  specInfo : SMap Name (Array SpecParamInfo) := {}
  deriving Inhabited

structure SpecEntry where
  declName   : Name
  paramsInfo : Array SpecParamInfo
  deriving Inhabited

namespace SpecState

def addEntry (s : SpecState) (e : SpecEntry) : SpecState :=
  match s with
  | { specInfo } => { specInfo := specInfo.insert e.declName e.paramsInfo }

def switch : SpecState → SpecState
  | { specInfo } => { specInfo := specInfo.switch }

end SpecState

/--
Extension for storing `SpecParamInfo` for declarations being compiled.
Remark: we only store information for declarations that will be specialized.
-/
builtin_initialize specExtension : SimplePersistentEnvExtension SpecEntry SpecState ←
  registerSimplePersistentEnvExtension {
    name          := `specInfoExt
    addEntryFn    := SpecState.addEntry
    addImportedFn := fun es => mkStateFromImportedEntries SpecState.addEntry {} es |>.switch
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
    let m := mkFixedArgMap decls
    for i in [:decls.size] do
      let decl := decls[i]!
      let paramsInfo := declsInfo[i]!
      let some mask := m.find? decl.name | unreachable!
      let paramsInfo := paramsInfo.zipWith mask fun info mask => if mask || info matches .user then info else .other
      if paramsInfo.any fun info => info matches .fixedInst | .fixedHO | .user then
        trace[Compiler.specialize.info] "{decl.name} {paramsInfo}"
        modifyEnv fun env => specExtension.addEntry env { declName := decl.name, paramsInfo }

def getSpecParamInfoCore? (env : Environment) (declName : Name) : Option (Array SpecParamInfo) :=
  (specExtension.getState env).specInfo.find? declName

def getSpecParamInfo? [Monad m] [MonadEnv m] (declName : Name) : m (Option (Array SpecParamInfo)) :=
  return (specExtension.getState (← getEnv)).specInfo.find? declName

def isSpecCandidate [Monad m] [MonadEnv m] (declName : Name) : m Bool :=
  return (specExtension.getState (← getEnv)).specInfo.contains declName

builtin_initialize
  registerTraceClass `Compiler.specialize.info

end Lean.Compiler.LCNF

