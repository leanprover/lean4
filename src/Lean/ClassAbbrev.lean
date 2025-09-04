/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Class
public import Lean.Structure

public section

namespace Lean

/-- An entry for the persistent environment extension for declared type class abbreviations -/
structure ClassAbbrevEntry where
  /-- Class name. -/
  name      : Name
  /-- If the class is declared with `class abbrev`, we store the structure projections in `projs`. -/
  projs : Array Name

/-- State of the type classabbreviation environment extension. -/
structure ClassAbbrevState where
  abbrevProjMap : SMap Name (Array Name) := SMap.empty
  deriving Inhabited

namespace ClassAbbrevState

def addEntry (s : ClassAbbrevState) (entry : ClassAbbrevEntry) : ClassAbbrevState :=
  { s with abbrevProjMap := s.abbrevProjMap.insert entry.name entry.projs }

def switch (s : ClassAbbrevState) : ClassAbbrevState :=
  { s with abbrevProjMap := s.abbrevProjMap.switch }

end ClassAbbrevState

/-- Type class abbreviation environment extension -/
builtin_initialize classAbbrevExtension : SimplePersistentEnvExtension ClassAbbrevEntry ClassAbbrevState ←
  registerSimplePersistentEnvExtension {
    addEntryFn    := ClassAbbrevState.addEntry
    addImportedFn := fun es => (mkStateFromImportedEntries ClassAbbrevState.addEntry {} es).switch
  }

/-- Return `true` if `n` is the name of a `class abbrev` in the given environment. -/
def isClassAbbrev (env : Environment) (n : Name) : Bool :=
  (classAbbrevExtension.getState env).abbrevProjMap.contains n

/-- Return `true` if `n` is the name of a `class abbrev` in the given environment. -/
def getClassAbbrevProjs? (env : Environment) (declName : Name) : Option (Array Name) :=
  (classAbbrevExtension.getState env).abbrevProjMap.find? declName

def addClassAbbrev (env : Environment) (clsName : Name) : Except MessageData Environment := do
  let some { fieldNames, .. } := getStructureInfo? env clsName
    | throw m!"invalid 'class abbrev', declaration '{.ofConstName clsName}' must be a structure"
  let projs ← fieldNames.mapM fun fieldName =>
    if let some info := getFieldInfo? env clsName fieldName then
      if info.binderInfo.isInstImplicit then
        pure info.projFn
      else
        throw m!"invalid 'class abbrev', field '{fieldName}' is not marked instance implicit"
    else
      throw m!"invalid 'class abbrev', field '{fieldName}' doesn't have a projection function"
  return classAbbrevExtension.addEntry env { name := clsName, projs }

/--
Registers a structure as a type class abbreviation. Using `class abbrev` is
generally preferred over using `@[class_abbrev] structure` directly.
-/
@[builtin_init, builtin_doc]
private def init :=
  registerBuiltinAttribute {
    name  := `class_abbrev
    descr := "type class abbreviation"
    add   := fun decl stx kind => do
      let env ← getEnv
      Attribute.Builtin.ensureNoArgs stx
      unless kind == AttributeKind.global do throwAttrMustBeGlobal `class kind
      let env ← ofExcept (addClass env decl)
      let env ← ofExcept (addClassAbbrev env decl)
      setEnv env
  }
