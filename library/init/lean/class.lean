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
(instances        : NameSet := ∅)

def ClassState.addEntry (imported : Bool) (s : ClassState) (entry : ClassEntry) : ClassState :=
match entry with
| ClassEntry.«class» clsName hasOutParam :=
  { hasOutParam := s.hasOutParam.insert clsName hasOutParam, .. s }
| ClassEntry.«instance» instName clsName :=
  { instances        := if imported then s.instances else s.instances.insert instName,
    classToInstances := match s.classToInstances.find clsName with
      | some insts := s.classToInstances.insert clsName (instName :: insts)
      | none       := s.classToInstances.insert clsName [instName],
    .. s }

def mkClassExtension : IO (SimplePersistentEnvExtension ClassEntry ClassState) :=
registerSimplePersistentEnvExtension {
  name          := `class,
  addEntryFn    := ClassState.addEntry false,
  addImportedFn := mkStateFromImportedEntries (ClassState.addEntry true) {}
}

end Lean
