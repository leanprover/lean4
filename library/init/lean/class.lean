/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.attributes

namespace Lean

inductive ClassEntry
| «class»    (name : Name) (hasOutParam : Bool)
| «instance» (name : Name) (ofClass : Name)

namespace ClassEntry

@[inline] def getName : ClassEntry → Name
| «class» n _ => n
| «instance» n _ => n

def lt (a b : ClassEntry) : Bool :=
Name.quickLt a.getName b.getName

end ClassEntry

structure ClassState :=
(classToInstances : SMap Name (List Name) := SMap.empty)
(hasOutParam      : SMap Name Bool := SMap.empty)
(instances        : SMap Name Unit := SMap.empty)

namespace ClassState

instance : Inhabited ClassState := ⟨{}⟩

def addEntry (s : ClassState) (entry : ClassEntry) : ClassState :=
match entry with
| ClassEntry.«class» clsName hasOutParam =>
  { hasOutParam := s.hasOutParam.insert clsName hasOutParam, .. s }
| ClassEntry.«instance» instName clsName =>
  { instances        := s.instances.insert instName (),
    classToInstances := match s.classToInstances.find clsName with
      | some insts => s.classToInstances.insert clsName (instName :: insts)
      | none       => s.classToInstances.insert clsName [instName],
    .. s }

def switch : ClassState → ClassState
| ⟨m₁, m₂, m₃⟩ => ⟨m₁.switch, m₂.switch, m₃.switch⟩

end ClassState

/- TODO: add support for scoped instances -/
def mkClassExtension : IO (SimplePersistentEnvExtension ClassEntry ClassState) :=
registerSimplePersistentEnvExtension {
  name          := `classExt,
  addEntryFn    := ClassState.addEntry,
  addImportedFn := fun es => (mkStateFromImportedEntries ClassState.addEntry {} es).switch
}

@[init mkClassExtension]
constant classExtension : SimplePersistentEnvExtension ClassEntry ClassState := default _

@[export lean_is_class]
def isClass (env : Environment) (n : Name) : Bool :=
(classExtension.getState env).hasOutParam.contains n

@[export lean_is_instance]
def isInstance (env : Environment) (n : Name) : Bool :=
(classExtension.getState env).instances.contains n

@[export lean_get_class_instances]
def getClassInstances (env : Environment) (n : Name) : List Name :=
match (classExtension.getState env).classToInstances.find n with
| some insts => insts
| none       => []

@[export lean_has_out_params]
def hasOutParams (env : Environment) (n : Name) : Bool :=
match (classExtension.getState env).hasOutParam.find n with
| some b => b
| none   => false

@[export lean_is_out_param]
def isOutParam (e : Expr) : Bool :=
e.isAppOfArity `outParam 1

def Expr.hasOutParam : Expr → Bool
| Expr.pi _ _ d b => isOutParam d || Expr.hasOutParam b
| _               => false

def addClass (env : Environment) (clsName : Name) : Except String Environment :=
if isClass env clsName then Except.error ("class has already been declared '" ++ toString clsName ++ "'")
else match env.find clsName with
  | none      => Except.error ("unknown declaration '" ++ toString clsName ++ "'")
  | some decl => Except.ok (classExtension.addEntry env (ClassEntry.«class» clsName decl.type.hasOutParam))

private def consumeNLambdas : Nat → Expr → Option Expr
| 0,   e                => some e
| i+1, Expr.lam _ _ _ b => consumeNLambdas i b
| _,   _                => none

partial def getClassName (env : Environment) : Expr → Option Name
| Expr.pi _ _ _ d => getClassName d
| e               => do
  Expr.const c _ ← pure e.getAppFn | none;
  info ← env.find c;
  match info.value with
  | some val => do
    body ← consumeNLambdas e.getAppNumArgs val;
    getClassName body
  | none =>
    if isClass env c then some c
    else none

@[export lean_add_instance]
def addInstance (env : Environment) (instName : Name) : Except String Environment :=
match env.find instName with
| none      => Except.error ("unknown declaration '" ++ toString instName ++ "'")
| some decl =>
  match getClassName env decl.type with
  | none => Except.error ("invalid instance '" ++ toString instName ++ "', failed to retrieve class")
  | some clsName => Except.ok (classExtension.addEntry env (ClassEntry.«instance» instName clsName))

@[init] def registerClassAttr : IO Unit :=
registerAttribute {
  name  := `class,
  descr := "type class",
  add   := fun env decl args persistent => do
    unless args.isMissing $ throw (IO.userError ("invalid attribute 'class', unexpected argument"));
    unless persistent $ throw (IO.userError ("invalid attribute 'class', must be persistent"));
    IO.ofExcept (addClass env decl)
}

@[init] def registerInstanceAttr : IO Unit :=
registerAttribute {
  name  := `instance,
  descr := "type class instance",
  add   := fun env decl args persistent => do
    unless args.isMissing $ throw (IO.userError ("invalid attribute 'instance', unexpected argument"));
    unless persistent $ throw (IO.userError ("invalid attribute 'instance', must be persistent"));
    IO.ofExcept (addInstance env decl)
}

end Lean
