/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Attributes

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

namespace ClassEntry

def lt (a b : ClassEntry) : Bool :=
  Name.quickLt a.name b.name

end ClassEntry

/-- State of the type class environment extension. -/
structure ClassState where
  outParamMap : SMap Name (Array Nat) := SMap.empty
  deriving Inhabited

namespace ClassState

def addEntry (s : ClassState) (entry : ClassEntry) : ClassState :=
  { s with outParamMap := s.outParamMap.insert entry.name entry.outParams }

/--
Switch the state into persistent mode. We switch to this mode after
we read all imported .olean files.
Recall that we use a `SMap` for implementing the state of the type class environment extension.
-/
def switch (s : ClassState) : ClassState :=
  { s with outParamMap := s.outParamMap.switch }

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
Add a new type class with the given name to the environment.
`declName` must not be the name of an existing type class,
and it must be the name of constant in `env`.
`declName` must be a inductive datatype or axiom.
Recall that all structures are inductive datatypes.
-/
def addClass (env : Environment) (clsName : Name) : Except MessageData Environment := do
  if isClass env clsName then
    throw m!"class has already been declared '{.ofConstName clsName true}'"
  let some decl := env.find? clsName
    | throw m!"unknown declaration '{clsName}'"
  unless decl matches .inductInfo .. | .axiomInfo .. do
    throw m!"invalid 'class', declaration '{.ofConstName clsName}' must be inductive datatype, structure, or constant"
  let outParams ← checkOutParam 0 #[] #[] decl.type
  return classExtension.addEntry env { name := clsName, outParams }

builtin_initialize
  registerBuiltinAttribute {
    name  := `class
    descr := "type class"
    add   := fun decl stx kind => do
      let env ← getEnv
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwError "invalid attribute 'class', must be global"
      let env ← ofExcept (addClass env decl)
      setEnv env
  }

end Lean
