/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes

namespace Lean

structure ClassEntry where
  name      : Name
  /--
    Position of the class `outParams`.
    For example, for class
    ```
    class GetElem (Cont : Type u) (Idx : Type v) (Elem : outParam (Type w)) (Dom : outParam (Cont → Idx → Prop)) where
    ```
    `outParams := #[2, 3]`
  -/
  outParams : Array Nat

namespace ClassEntry

def lt (a b : ClassEntry) : Bool :=
  Name.quickLt a.name b.name

end ClassEntry

structure ClassState where
  outParamMap : SMap Name (Array Nat) := SMap.empty
  deriving Inhabited

namespace ClassState

def addEntry (s : ClassState) (entry : ClassEntry) : ClassState :=
  { s with outParamMap := s.outParamMap.insert entry.name entry.outParams }

def switch (s : ClassState) : ClassState :=
  { s with outParamMap := s.outParamMap.switch }

end ClassState

/- TODO: add support for scoped instances -/
builtin_initialize classExtension : SimplePersistentEnvExtension ClassEntry ClassState ←
  registerSimplePersistentEnvExtension {
    name          := `classExt
    addEntryFn    := ClassState.addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries ClassState.addEntry {} es).switch
  }

@[export lean_is_class]
def isClass (env : Environment) (n : Name) : Bool :=
  (classExtension.getState env).outParamMap.contains n

/--
  If `declName` is a class, return the position of its `outParams`.
-/
def getOutParamPositions? (env : Environment) (declName : Name) : Option (Array Nat) :=
  (classExtension.getState env).outParamMap.find? declName

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
private partial def checkOutParam (i : Nat) (outParamFVarIds : Array FVarId) (outParams : Array Nat) (type : Expr) : Except String (Array Nat) :=
  match type with
  | .forallE _ d b _ =>
    if d.isOutParam then
      let fvarId := { name := Name.mkNum `_fvar outParamFVarIds.size }
      let fvar      := mkFVar fvarId
      let b         := b.instantiate1 fvar
      checkOutParam (i+1) (outParamFVarIds.push fvarId) (outParams.push i) b
    else if d.hasAnyFVar fun fvarId => outParamFVarIds.contains fvarId then
      Except.error s!"invalid class, parameter #{i+1} depends on `outParam`, but it is not an `outParam`"
    else
      checkOutParam (i+1) outParamFVarIds outParams b
  | _ => return outParams

def addClass (env : Environment) (clsName : Name) : Except String Environment := do
  if isClass env clsName then
    throw s!"class has already been declared '{clsName}'"
  let some decl := env.find? clsName
    | throw s!"unknown declaration '{clsName}'"
  unless decl matches .inductInfo .. | .axiomInfo .. do
    throw s!"invalid 'class', declaration '{clsName}' must be inductive datatype, structure, or constant"
  let outParams ← checkOutParam 0 #[] #[] decl.type
  return classExtension.addEntry env { name := clsName, outParams }

private def consumeNLambdas : Nat → Expr → Option Expr
  | 0,   e            => some e
  | i+1, .lam _ _ b _ => consumeNLambdas i b
  | _,   _            => none

partial def getClassName (env : Environment) : Expr → Option Name
  | .forallE _ _ b _ => getClassName env b
  | e                => do
    let Expr.const c _ ← pure e.getAppFn | none
    let info ← env.find? c
    match info.value? with
    | some val => do
      let body ← consumeNLambdas e.getAppNumArgs val
      getClassName env body
    | none =>
      if isClass env c then some c
      else none

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
