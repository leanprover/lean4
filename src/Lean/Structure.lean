/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper functions for retrieving structure information.
-/
prelude
import Lean.Environment
import Lean.ProjFns

namespace Lean

structure StructureFieldInfo where
  fieldName  : Name
  projFn     : Name
  /-- It is `some parentStructName` if it is a subobject, and `parentStructName` is the name of the parent structure -/
  subobject? : Option Name
  binderInfo : BinderInfo
  autoParam? : Option Expr := none
  deriving Inhabited, Repr

def StructureFieldInfo.lt (i₁ i₂ : StructureFieldInfo) : Bool :=
  Name.quickLt i₁.fieldName i₂.fieldName

structure StructureInfo where
  structName : Name
  fieldNames : Array Name := #[] -- sorted by field position in the structure
  fieldInfo  : Array StructureFieldInfo := #[] -- sorted by `fieldName`
  deriving Inhabited

def StructureInfo.lt (i₁ i₂ : StructureInfo) : Bool :=
  Name.quickLt i₁.structName i₂.structName

def StructureInfo.getProjFn? (info : StructureInfo) (i : Nat) : Option Name :=
  if h : i < info.fieldNames.size then
    let fieldName := info.fieldNames.get ⟨i, h⟩
    info.fieldInfo.binSearch { fieldName := fieldName, projFn := default, subobject? := none, binderInfo := default } StructureFieldInfo.lt |>.map (·.projFn)
  else
    none

/-- Auxiliary state for structures defined in the current module. -/
private structure StructureState where
  map : PersistentHashMap Name StructureInfo := {}
  deriving Inhabited

builtin_initialize structureExt : SimplePersistentEnvExtension StructureInfo StructureState ← registerSimplePersistentEnvExtension {
  addImportedFn := fun _ => {}
  addEntryFn    := fun s e => { s with map := s.map.insert e.structName e }
  toArrayFn     := fun es => es.toArray.qsort StructureInfo.lt
}

structure StructureDescr where
  structName : Name
  fields     : Array StructureFieldInfo -- Should use the order the field appear in the constructor.
  deriving Inhabited

def registerStructure (env : Environment) (e : StructureDescr) : Environment :=
  structureExt.addEntry env {
    structName := e.structName
    fieldNames := e.fields.map fun e => e.fieldName
    fieldInfo  := e.fields.qsort StructureFieldInfo.lt
  }

def getStructureInfo? (env : Environment) (structName : Name) : Option StructureInfo :=
  match env.getModuleIdxFor? structName with
  | some modIdx => structureExt.getModuleEntries env modIdx |>.binSearch { structName } StructureInfo.lt
  | none        => structureExt.getState env |>.map.find? structName

/--
Gets the constructor of an inductive type that has exactly one constructor.
This is meant to be used with types that have had been registered as a structure by `registerStructure`,
but this is not checked.

Warning: these do *not* need to be "structure-likes". A structure-like is non-recursive,
and structure-likes have special kernel support.
-/
def getStructureCtor (env : Environment) (constName : Name) : ConstructorVal :=
  match env.find? constName with
  | some (.inductInfo { ctors := [ctorName], .. }) =>
    match env.find? ctorName with
    | some (ConstantInfo.ctorInfo val) => val
    | _ => panic! "ill-formed environment"
  | _ => panic! "structure expected"

/-- Gets the direct field names for the given structure, including subobject fields. -/
def getStructureFields (env : Environment) (structName : Name) : Array Name :=
  if let some info := getStructureInfo? env structName then
    info.fieldNames
  else
    panic! "structure expected"

def getFieldInfo? (env : Environment) (structName : Name) (fieldName : Name) : Option StructureFieldInfo :=
  if let some info := getStructureInfo? env structName then
    info.fieldInfo.binSearch { fieldName := fieldName, projFn := default, subobject? := none, binderInfo := default } StructureFieldInfo.lt
  else
    none

/-- If `fieldName` represents the relation to a parent structure `S`, returns `S` -/
def isSubobjectField? (env : Environment) (structName : Name) (fieldName : Name) : Option Name :=
  if let some fieldInfo := getFieldInfo? env structName fieldName then
    fieldInfo.subobject?
  else
    none

/-- Returns immediate parent structures. -/
def getParentStructures (env : Environment) (structName : Name) : Array Name :=
  let fieldNames := getStructureFields env structName;
  fieldNames.foldl (init := #[]) fun acc fieldName =>
      match isSubobjectField? env structName fieldName with
      | some parentStructName => acc.push parentStructName
      | none                  => acc

/-- Returns all parent structures. -/
partial def getAllParentStructures (env : Environment) (structName : Name) : Array Name :=
  visit structName |>.run #[] |>.2
where
  visit (structName : Name) : StateT (Array Name) Id Unit := do
    for p in getParentStructures env structName do
      modify fun s => s.push p
      visit p

/-- `findField? env S fname`. If `fname` is defined in a parent `S'` of `S`, return `S'` -/
partial def findField? (env : Environment) (structName : Name) (fieldName : Name) : Option Name :=
  if (getStructureFields env structName).contains fieldName then
    some structName
  else
    getParentStructures env structName |>.findSome? fun parentStructName => findField? env parentStructName fieldName

private partial def getStructureFieldsFlattenedAux (env : Environment) (structName : Name) (fullNames : Array Name) (includeSubobjectFields : Bool) : Array Name :=
  (getStructureFields env structName).foldl (init := fullNames) fun fullNames fieldName =>
    match isSubobjectField? env structName fieldName with
    | some parentStructName =>
      let fullNames := if includeSubobjectFields then fullNames.push fieldName else fullNames
      getStructureFieldsFlattenedAux env parentStructName fullNames includeSubobjectFields
    | none                  => fullNames.push fieldName

/--
Returns field names for the given structure, including "flattened" fields from parent
structures. To omit `toParent` projections, set `includeSubobjectFields := false`.

For example, given `Bar` such that
```lean
structure Foo where a : Nat
structure Bar extends Foo where b : Nat
```
return `#[toFoo,a,b]` or `#[a,b]` with subobject fields omitted. -/
def getStructureFieldsFlattened (env : Environment) (structName : Name) (includeSubobjectFields := true) : Array Name :=
  getStructureFieldsFlattenedAux env structName #[] includeSubobjectFields

/--
Returns true if `constName` is the name of an inductive datatype
created using the `structure` or `class` commands.

These are inductive types for which structure information has been registered with `registerStructure`.
-/
def isStructure (env : Environment) (constName : Name) : Bool :=
  getStructureInfo? env constName |>.isSome

def getProjFnForField? (env : Environment) (structName : Name) (fieldName : Name) : Option Name :=
  if let some fieldInfo := getFieldInfo? env structName fieldName then
    some fieldInfo.projFn
  else
    none

def getProjFnInfoForField? (env : Environment) (structName : Name) (fieldName : Name) : Option (Name × ProjectionFunctionInfo) :=
  if let some projFn := getProjFnForField? env structName fieldName then
    (projFn, ·) <$> env.getProjectionFnInfo? projFn
  else
    none

def mkDefaultFnOfProjFn (projFn : Name) : Name :=
  projFn ++ `_default

def getDefaultFnForField? (env : Environment) (structName : Name) (fieldName : Name) : Option Name :=
  if let some projName := getProjFnForField? env structName fieldName then
    let defFn := mkDefaultFnOfProjFn projName
    if env.contains defFn then defFn else none
  else
    -- Check if we have a default function for a default values overridden by substructure.
    let defFn := mkDefaultFnOfProjFn (structName ++ fieldName)
    if env.contains defFn then defFn else none

partial def getPathToBaseStructureAux (env : Environment) (baseStructName : Name) (structName : Name) (path : List Name) : Option (List Name) :=
  if baseStructName == structName then
    some path.reverse
  else
    let fieldNames := getStructureFields env structName;
    fieldNames.findSome? fun fieldName =>
      match isSubobjectField? env structName fieldName with
      | none                  => none
      | some parentStructName =>
        match getProjFnForField? env structName fieldName with
        | none        => none
        | some projFn => getPathToBaseStructureAux env baseStructName parentStructName (projFn :: path)

/--
If `baseStructName` is an ancestor structure for `structName`, then returns a sequence of projection functions
to go from `structName` to `baseStructName`.
-/
def getPathToBaseStructure? (env : Environment) (baseStructName : Name) (structName : Name) : Option (List Name) :=
  getPathToBaseStructureAux env baseStructName structName []

/--
Returns true iff `constName` is a non-recursive inductive datatype that has only one constructor and no indices.

Such types have special kernel support. This must be in sync with `is_structure_like`.
-/
def isStructureLike (env : Environment) (constName : Name) : Bool :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [_], numIndices := 0, .. }) => true
  | _ => false

def getStructureLikeCtor? (env : Environment) (constName : Name) : Option ConstructorVal :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [ctorName], .. }) =>
    match env.find? ctorName with
    | some (ConstantInfo.ctorInfo val) => val
    | _ => panic! "ill-formed environment"
  | _ => none

/-- Return number of fields for a structure-like type -/
def getStructureLikeNumFields (env : Environment) (constName : Name) : Nat :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [ctor], numIndices := 0, .. }) =>
    match env.find? ctor with
    | some (.ctorInfo { numFields := n, .. }) => n
    | _ => 0
  | _ => 0

end Lean
