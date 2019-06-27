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
| («class» n _) := n
| («instance» n _) := n

def lt (a b : ClassEntry) : Bool :=
Name.quickLt a.getName b.getName

end ClassEntry

structure ClassState :=
(classToInstances : SMap Name (List Name) Name.quickLt := SMap.empty)
(hasOutParam      : SMap Name Bool Name.quickLt := SMap.empty)
(instances        : SMap Name Unit Name.quickLt := SMap.empty)

namespace ClassState

instance : Inhabited ClassState := ⟨{}⟩

def addEntry (s : ClassState) (entry : ClassEntry) : ClassState :=
match entry with
| ClassEntry.«class» clsName hasOutParam :=
  { hasOutParam := s.hasOutParam.insert clsName hasOutParam, .. s }
| ClassEntry.«instance» instName clsName :=
  { instances        := s.instances.insert instName (),
    classToInstances := match s.classToInstances.find clsName with
      | some insts := s.classToInstances.insert clsName (instName :: insts)
      | none       := s.classToInstances.insert clsName [instName],
    .. s }

end ClassState

/- TODO: add support for scoped instances -/
def mkClassExtension : IO (SimplePersistentEnvExtension ClassEntry ClassState) :=
registerSimplePersistentEnvExtension {
  name          := `class,
  addEntryFn    := ClassState.addEntry,
  addImportedFn := mkStateFromImportedEntries ClassState.addEntry {}
}

@[init mkClassExtension]
constant classExtension : SimplePersistentEnvExtension ClassEntry ClassState := default _

def isClass (env : Environment) (n : Name) : Bool :=
(classExtension.getState env).hasOutParam.contains n

def isInstance (env : Environment) (n : Name) : Bool :=
(classExtension.getState env).instances.contains n

def getClassInstances (env : Environment) (n : Name) : List Name :=
match (classExtension.getState env).classToInstances.find n with
| some insts := insts
| none       := []

private def isOutParam (e : Expr) : Bool :=
e.isAppOfArity `outParam 1

private def hasOutParam : Expr → Bool
| (Expr.pi _ _ d b) := isOutParam d || hasOutParam b
| _                 := false

def addClass (env : Environment) (clsName : Name) : Except String Environment :=
if isClass env clsName then Except.error ("class has already been declared '" ++ toString clsName ++ "'")
else match env.find clsName with
  | none      := Except.error ("unknown declaration '" ++ toString clsName ++ "'")
  | some decl := Except.ok (classExtension.addEntry env (ClassEntry.«class» clsName (hasOutParam decl.type)))

-- def addInstance (env : Environment) (instName : Name) : Environment :=
-- match env.find

end Lean
