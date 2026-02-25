/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Attributes
import Lean.Util.CollectLevelParams
public section
namespace Lean

/-- An entry for the persistent environment extension for declared type classes -/
structure ClassEntry where
  /-- Class name. -/
  name      : Name
  /--
  Position of the class `outParams`.
  For example, for class
  ```
  class GetElem (cont : Type u) (idx : Type v) (elem : outParam (Type w)) (dom : outParam (cont → idx → Prop)) where
  ```
  `outParams := #[2, 3]`
  -/
  outParams : Array Nat
  /--
  Positions of universe level parameters that only appear in output parameter types.
  For example, for `HAdd (α : Type u) (β : Type v) (γ : outParam (Type w))`,
  `outLevelParams := #[2]` since universe `w` only appears in the output parameter `γ`.
  This is used to normalize TC resolution cache keys.
  -/
  outLevelParams : Array Nat

namespace ClassEntry

def lt (a b : ClassEntry) : Bool :=
  Name.quickLt a.name b.name

end ClassEntry

/-- State of the type class environment extension. -/
structure ClassState where
  outParamMap : SMap Name (Array Nat) := SMap.empty
  outLevelParamMap : SMap Name (Array Nat) := SMap.empty
  deriving Inhabited

namespace ClassState

def addEntry (s : ClassState) (entry : ClassEntry) : ClassState :=
  { s with
    outParamMap := s.outParamMap.insert entry.name entry.outParams
    outLevelParamMap := s.outLevelParamMap.insert entry.name entry.outLevelParams }

/--
Switch the state into persistent mode. We switch to this mode after
we read all imported .olean files.
Recall that we use a `SMap` for implementing the state of the type class environment extension.
-/
def switch (s : ClassState) : ClassState :=
  { s with
    outParamMap := s.outParamMap.switch
    outLevelParamMap := s.outLevelParamMap.switch }

end ClassState

/--
Type class environment extension
-/
-- TODO: add support for scoped instances
builtin_initialize classExtension : SimplePersistentEnvExtension ClassEntry ClassState ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := ClassState.addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries ClassState.addEntry {} es).switch
  }

/-- Return `true` if `n` is the name of type class in the given environment. -/
@[export lean_is_class]
def isClass (env : Environment) (n : Name) : Bool :=
  (classExtension.getState env).outParamMap.contains n

/-- If `declName` is a class, return the position of its `outParams`. -/
def getOutParamPositions? (env : Environment) (declName : Name) : Option (Array Nat) :=
  (classExtension.getState env).outParamMap.find? declName

/-- Return `true` if the given `declName` is a type class with output parameters. -/
@[export lean_has_out_params]
def hasOutParams (env : Environment) (declName : Name) : Bool :=
  match getOutParamPositions? env declName with
  | some outParams => !outParams.isEmpty
  | none => false

/-- If `declName` is a class, return the positions of universe level parameters that only appear in output parameter types. -/
def getOutLevelParamPositions? (env : Environment) (declName : Name) : Option (Array Nat) :=
  (classExtension.getState env).outLevelParamMap.find? declName

/--
  Auxiliary function for collection the position class `outParams`, and
  checking whether they are being correctly used.
  A regular (i.e., non `outParam`) must not depend on an `outParam`.
  Reason for this restriction:
  When performing type class resolution, we replace arguments that
  are `outParam`s with fresh metavariables. If regular parameters could
  depend on `outParam`s, then we would also have to replace them with
  fresh metavariables. Otherwise, the resulting expression could be type
  incorrect. This transformation would be counterintuitive to users since
  we would implicitly treat these regular parameters as `outParam`s.
-/
private partial def checkOutParam (i : Nat) (outParamFVarIds : Array FVarId) (outParams : Array Nat) (type : Expr) : Except MessageData (Array Nat) :=
  match type with
  | .forallE _ d b bi =>
    let addOutParam (_ : Unit) :=
      let fvarId := { name := Name.mkNum `_fvar outParamFVarIds.size }
      let fvar      := mkFVar fvarId
      let b         := b.instantiate1 fvar
      checkOutParam (i+1) (outParamFVarIds.push fvarId) (outParams.push i) b
    if d.isOutParam then
      addOutParam ()
    else if d.hasAnyFVar fun fvarId => outParamFVarIds.contains fvarId then
      if bi.isInstImplicit then
        /- See issue #1852 for a motivation for `bi.isInstImplicit` -/
        addOutParam ()
      else
        Except.error m!"invalid class, parameter #{i+1} depends on `outParam`, but it is not an `outParam`"
    else
      checkOutParam (i+1) outParamFVarIds outParams b
  | _ => return outParams

/--
Mark `outParam`s in `type` as implicit. Note that it also marks instance implicit arguments that depend on `outParam`s as implicit.

Remark: this function consumes the `outParam` annotations.

This function uses the same logic used as `checkOutParam`.
See issue #1901
-/
@[export lean_mk_outparam_args_implicit]
partial def mkOutParamArgsImplicit (type : Expr) : Expr :=
  go type type #[]
where
  go (type : Expr) (typeAux : Expr) (outParamFVarIds : Array FVarId) : Expr :=
    match typeAux with
    | .forallE _ d b bi =>
      let mkOutParamImplicit (dNew : Expr) :=
        let fvarId := { name := Name.mkNum `_fvar outParamFVarIds.size }
        let fvar      := mkFVar fvarId
        let b         := b.instantiate1 fvar
        let bNew      := go type.bindingBody! b (outParamFVarIds.push fvarId)
        type.updateForall! .implicit dNew bNew
      let keepBinderInfo (_ : Unit) :=
        let bNew := go type.bindingBody! b outParamFVarIds
        type.updateForallE! type.bindingDomain! bNew
      if d.isOutParam then
        mkOutParamImplicit type.bindingDomain!.appArg! -- consume `outParam` annotation
      else if d.hasAnyFVar fun fvarId => outParamFVarIds.contains fvarId then
        if bi.isInstImplicit then
          mkOutParamImplicit type.bindingDomain!
        else
          keepBinderInfo ()
      else
        keepBinderInfo ()
    | _ => type

/--
Compute positions of universe level parameters that only appear in output parameter types.

During type class resolution, the cache key for a query like
`HAppend.{0, 0, ?u} (BitVec 8) (BitVec 8) ?m` should be independent of the specific
metavariable IDs in output parameter positions. To achieve this, output parameter arguments
are erased from the cache key. However, universe levels that only appear in output parameter
types (e.g., `?u` corresponding to the result type's universe) must also be erased to avoid
cache misses when the same query is issued with different universe metavariable IDs.

This function identifies which universe level parameter positions are "output-only" by
collecting all level param names that appear in non-output parameter domains, then returning
the positions of any level params not in that set.
-/
private partial def computeOutLevelParams (type : Expr) (outParams : Array Nat) (levelParams : List Name) : Array Nat := Id.run do
  let nonOutLevels := go type 0 {} |>.params
  let mut result := #[]
  let mut i := 0
  for name in levelParams do
    unless nonOutLevels.contains name do
      result := result.push i
    i := i + 1
  result
where
  go (type : Expr) (i : Nat) (s : CollectLevelParams.State) : CollectLevelParams.State :=
    match type with
    | .forallE _ d b _ =>
      if outParams.contains i then
        go b (i + 1) s
      else
        go b (i + 1) (collectLevelParams s d)
    | _ => s

/--
Add a new type class with the given name to the environment.
`declName` must not be the name of an existing type class,
and it must be the name of constant in `env`.
`declName` must be a inductive datatype or axiom.
Recall that all structures are inductive datatypes.
-/
def addClass (env : Environment) (clsName : Name) : Except MessageData Environment := do
  if isClass env clsName then
    throw m!"class has already been declared `{.ofConstName clsName true}`"
  let some decl := env.find? clsName
    | throw m!"unknown declaration `{clsName}`"
  unless decl matches .inductInfo .. | .axiomInfo .. do
    throw m!"invalid `class`, declaration `{.ofConstName clsName}` must be inductive datatype, structure, or constant"
  let outParams ← checkOutParam 0 #[] #[] decl.type
  let outLevelParams := computeOutLevelParams decl.type outParams decl.levelParams
  return classExtension.addEntry env { name := clsName, outParams, outLevelParams }

/--
Registers an inductive type or structure as a type class. Using `class` or `class inductive` is
generally preferred over using `@[class] structure` or `@[class] inductive` directly.
-/
@[builtin_init, builtin_doc]
private def init :=
  registerBuiltinAttribute {
    name  := `class
    descr := "type class"
    add   := fun decl stx kind => do
      let env ← getEnv
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `class kind
      let env ← ofExcept (addClass env decl)
      setEnv env
  }

builtin_initialize
  registerBuiltinAttribute {
    name  := `univ_out_params
    descr := "universe output parameters for a type class"
    add   := fun decl stx kind => do
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `univ_out_params kind
      let env ← getEnv
      unless isClass env decl do
        throwError "invalid `univ_out_params`, `{decl}` is not a class"
      let info ← getConstInfo decl
      let us := info.levelParams
      let args := stx[1].getArgs
      args.forM fun arg => do
        unless us.contains arg.getId do
          throwErrorAt arg "`{arg}` is not a universe parameter of `{decl}`"
      let args := args.map (·.getId)
      let mut outLevelParams : Array Nat := #[]
      let mut i := 0
      for u in us do
        if args.contains u then
          outLevelParams := outLevelParams.push i
        i := i + 1
      let outParams := getOutParamPositions? env decl |>.getD #[]
      modifyEnv fun env => classExtension.addEntry env { name := decl, outParams, outLevelParams }
  }

end Lean
