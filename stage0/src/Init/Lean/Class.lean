/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Attributes

namespace Lean

inductive ClassEntry
| «class»    (name : Name) (hasOutParam : Bool)
| «instance» (name : Name) (ofClass : Name) -- TODO: remove after we remove old type class resolution

namespace ClassEntry

@[inline] def getName : ClassEntry → Name
| «class» n _ => n
| «instance» n _ => n

def lt (a b : ClassEntry) : Bool :=
Name.quickLt a.getName b.getName

end ClassEntry

structure ClassState :=
(classToInstances : SMap Name (List Name) := SMap.empty) -- TODO: delete
(hasOutParam      : SMap Name Bool := SMap.empty)        -- We should keep only this one
(instances        : SMap Name Unit := SMap.empty)        -- TODO: delete

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
constant classExtension : SimplePersistentEnvExtension ClassEntry ClassState := arbitrary _

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
    let fvarId    := mkNameNum `_fvar outParams.size;
    let outParams := outParams.push fvarId;
    let fvar      := mkFVar fvarId;
    let b         := b.instantiate1 fvar;
    checkOutParam (i+1) outParams b
  else if d.hasAnyFVar (fun fvarId => outParams.contains fvarId) then
    Except.error $ "invalid class, parameter #" ++ toString i ++ " depends on `outParam`, but it is not an `outParam`"
  else
    checkOutParam (i+1) outParams b
| i, outParams, e => pure (outParams.size > 0)

def addClass (env : Environment) (clsName : Name) : Except String Environment :=
if isClass env clsName then Except.error ("class has already been declared '" ++ toString clsName ++ "'")
else match env.find clsName with
  | none      => Except.error ("unknown declaration '" ++ toString clsName ++ "'")
  | some decl@(ConstantInfo.inductInfo _) => do
    b ← checkOutParam 1 #[] decl.type;
    Except.ok (classExtension.addEntry env (ClassEntry.«class» clsName b))
  | some _    => Except.error ("invalid 'class', declaration '" ++ toString clsName ++ "' must be inductive datatype or structure")

private def consumeNLambdas : Nat → Expr → Option Expr
| 0,   e                => some e
| i+1, Expr.lam _ _ b _ => consumeNLambdas i b
| _,   _                => none

partial def getClassName (env : Environment) : Expr → Option Name
| Expr.forallE _ _ b _ => getClassName b
| e                    => do
  Expr.const c _ _ ← pure e.getAppFn | none;
  info ← env.find c;
  match info.value? with
  | some val => do
    body ← consumeNLambdas e.getAppNumArgs val;
    getClassName body
  | none =>
    if isClass env c then some c
    else none

@[init] def registerClassAttr : IO Unit :=
registerAttribute {
  name  := `class,
  descr := "type class",
  add   := fun env decl args persistent => do
    unless args.isMissing $ throw (IO.userError ("invalid attribute 'class', unexpected argument"));
    unless persistent $ throw (IO.userError ("invalid attribute 'class', must be persistent"));
    IO.ofExcept (addClass env decl)
}

-- TODO: delete
@[export lean_add_instance]
def addGlobalInstanceOld (env : Environment) (instName : Name) : Except String Environment :=
match env.find instName with
| none      => Except.error ("unknown declaration '" ++ toString instName ++ "'")
| some decl =>
  match getClassName env decl.type with
  | none => Except.error ("invalid instance '" ++ toString instName ++ "', failed to retrieve class")
  | some clsName => Except.ok (classExtension.addEntry env (ClassEntry.«instance» instName clsName))

end Lean
