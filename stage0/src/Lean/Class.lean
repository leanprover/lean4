/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes

namespace Lean

structure ClassEntry where
  name : Name
  hasOutParam : Bool

namespace ClassEntry

def lt (a b : ClassEntry) : Bool :=
  Name.quickLt a.name b.name

end ClassEntry

structure ClassState where
  hasOutParam : SMap Name Bool := SMap.empty
  deriving Inhabited

namespace ClassState

def addEntry (s : ClassState) (entry : ClassEntry) : ClassState :=
  { s with hasOutParam := s.hasOutParam.insert entry.name entry.hasOutParam }

def switch (s : ClassState) : ClassState :=
  { s with hasOutParam := s.hasOutParam.switch }

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
  (classExtension.getState env).hasOutParam.contains n

@[export lean_has_out_params]
def hasOutParams (env : Environment) (n : Name) : Bool :=
  match (classExtension.getState env).hasOutParam.find? n with
  | some b => b
  | none   => false

@[export lean_is_out_param]
def isOutParam (e : Expr) : Bool :=
  e.isAppOfArity `outParam 1

/--
  Auxiliary function for checking whether a class has `outParam`, and
  whether they are being correctly used.
  A regular (i.e., non `outParam`) must not depend on an `outParam`.
  Reason for this restriction:
  When performing type class resolution, we replace arguments that
  are `outParam`s with fresh metavariables. If regular parameters could
  depend on `outParam`s, then we would also have to replace them with
  fresh metavariables. Otherwise, the resulting expression could be type
  incorrect. This transformation would be counterintuitive to users since
  we would implicitly treat these regular parameters as `outParam`s.
-/
private partial def checkOutParam : Nat → Array FVarId → Expr → Except String Bool
  | i, outParams, Expr.forallE _ d b _ =>
    if isOutParam d then
      let fvarId    := { name := Name.mkNum `_fvar outParams.size }
      let outParams := outParams.push fvarId
      let fvar      := mkFVar fvarId
      let b         := b.instantiate1 fvar
      checkOutParam (i+1) outParams b
    else if d.hasAnyFVar fun fvarId => outParams.contains fvarId then
      Except.error s!"invalid class, parameter #{i} depends on `outParam`, but it is not an `outParam`"
    else
      checkOutParam (i+1) outParams b
  | i, outParams, e => pure (outParams.size > 0)

def addClass (env : Environment) (clsName : Name) : Except String Environment :=
  if isClass env clsName then
    Except.error s!"class has already been declared '{clsName}'"
  else match env.find? clsName with
    | none      => Except.error ("unknown declaration '" ++ toString clsName ++ "'")
    | some decl@(ConstantInfo.inductInfo _) => do
      let b ← checkOutParam 1 #[] decl.type
      Except.ok (classExtension.addEntry env { name := clsName, hasOutParam := b })
    | some _    => Except.error ("invalid 'class', declaration '" ++ toString clsName ++ "' must be inductive datatype or structure")

private def consumeNLambdas : Nat → Expr → Option Expr
  | 0,   e                => some e
  | i+1, Expr.lam _ _ b _ => consumeNLambdas i b
  | _,   _                => none

partial def getClassName (env : Environment) : Expr → Option Name
  | Expr.forallE _ _ b _ => getClassName env b
  | e                    => OptionM.run do
    let Expr.const c _ _ ← pure e.getAppFn | none
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
    name  := `class,
    descr := "type class",
    add   := fun decl stx kind => do
      let env ← getEnv
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwError "invalid attribute 'class', must be global"
      let env ← ofExcept (addClass env decl)
      setEnv env
  }

end Lean
