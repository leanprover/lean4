/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper functions for retrieving structure information.
-/
prelude
import Lean.Environment
import Lean.ProjFns
import Lean.Exception

namespace Lean

/--
Data for a structure field.
These are direct fields of a structure, and the full collection of fields is the transitive closure of fields through subobjects.
-/
structure StructureFieldInfo where
  /-- The name of the field. This is a single-component name. -/
  fieldName  : Name
  /-- The projection function associated to the field. -/
  projFn     : Name
  /-- If this field is for a subobject (i.e., an embedded parent structure), contains the name of the parent structure. -/
  subobject? : Option Name
  /-- The binder info for the field from the `structure` definition. -/
  binderInfo : BinderInfo
  /-- If set, contains an expression that evaluates to `Syntax` to use as a tactic. From `field := by ...`. -/
  autoParam? : Option Expr := none
  deriving Inhabited, Repr

def StructureFieldInfo.lt (i₁ i₂ : StructureFieldInfo) : Bool :=
  Name.quickLt i₁.fieldName i₂.fieldName

/--
Data for a direct parent of a structure.
Some structure parents are represented as subobjects (embedded structures),
and for these the parent project is a true projection.
Otherwise, the fields of the parent structure are represented among the other fields of the structure,
and the `projFn` constructs a term from these fields.
-/
structure StructureParentInfo where
  /-- The name of the parent structure. -/
  structName : Name
  /-- Whether this parent structure is represented as a subobject. If so, then there is a `fieldInfo` entry with the same `projFn`. -/
  subobject  : Bool
  /-- The projection function associated to the field. -/
  projFn     : Name
  deriving Inhabited

/--
Data about a type created with the `structure` command.
-/
structure StructureInfo where
  /-- The name of the structure. -/
  structName  : Name
  /-- The direct fields of a structure, sorted by position in the structure.
  For example, the `s.3` notation refers to `fieldNames[3 - 1]`. -/
  fieldNames  : Array Name := #[]
  /-- Information about the structure fields, sorted by `fieldName`. -/
  fieldInfo   : Array StructureFieldInfo := #[]
  /-- Information about structure parents. These are in the order they appear in the `extends` clause. -/
  parentInfo  : Array StructureParentInfo := #[]
  /-- A list of namespaces to consult when resolving generalized field notation.
  This includes `structName` as well as the transitive closure of all parents. -/
  resolutionOrder : Array Name := #[]
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

/--
A descriptor for a structure, for constructing a `StructureInfo` via `Lean.registerStructure`.
-/
structure StructureDescr where
  /-- The name of the structure. -/
  structName  : Name
  /-- The fields should be in the order that they appear in the structure's constructor. -/
  fields      : Array StructureFieldInfo
  deriving Inhabited

/--
Create a new entry in the extension `structureExt`.
Every structure created by `structure` or `class` has such an entry.
This should be followed up with `setStructureParents` and `setStructureResolutionOrder`.
-/
def registerStructure (env : Environment) (e : StructureDescr) : Environment :=
  structureExt.addEntry env {
    structName := e.structName
    fieldNames := e.fields.map fun e => e.fieldName
    fieldInfo  := e.fields.qsort StructureFieldInfo.lt
  }

/--
Set parent projection info for a structure defined in the current module.
Throws an error if the structure has not already been registered.
-/
def setStructureParents [Monad m] [MonadEnv m] [MonadError m] (structName : Name) (parentInfo : Array StructureParentInfo) : m Unit := do
  let some info := structureExt.getState (← getEnv) |>.map.find? structName
    | throwError "cannot set structure parents for '{structName}', structure not defined in current module"
  modifyEnv fun env => structureExt.addEntry env { info with parentInfo }

/--
Set a method resolution order to a structure defined in the current module.
Throws an error if the structure has not already been registered.
-/
def setStructureResolutionOrder [Monad m] [MonadEnv m] [MonadError m] (structName : Name) (resolutionOrder : Array Name) : m Unit := do
  let some info := structureExt.getState (← getEnv) |>.map.find? structName
    | throwError "cannot set structure resolution order for '{structName}', structure not defined in current module"
  modifyEnv fun env => structureExt.addEntry env { info with resolutionOrder }

def getStructureInfo? (env : Environment) (structName : Name) : Option StructureInfo :=
  match env.getModuleIdxFor? structName with
  | some modIdx => structureExt.getModuleEntries env modIdx |>.binSearch { structName } StructureInfo.lt
  | none        => structureExt.getState env |>.map.find? structName

def getStructureInfo (env : Environment) (structName : Name) : Array Name :=
  if let some info := getStructureInfo? env structName then
    info.fieldNames
  else
    panic! "structure expected"

def getStructureCtor (env : Environment) (constName : Name) : ConstructorVal :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [ctorName], .. }) =>
    match env.find? ctorName with
    | some (ConstantInfo.ctorInfo val) => val
    | _ => panic! "ill-formed environment"
  | _ => panic! "structure expected"

/-- Get field names for direct fields of the given structure. This includes subobjects. -/
def getStructureFields (env : Environment) (structName : Name) : Array Name :=
  if let some info := getStructureInfo? env structName then
    info.fieldNames
  else
    panic! "structure expected"

/-- Get information for all the parents that appear in the `extends` clause. -/
def getStructureParentInfo (env : Environment) (structName : Name) : Array StructureParentInfo :=
  if let some info := getStructureInfo? env structName then
    info.parentInfo
  else
    panic! "structure expected"

/-- Get the resolution order for generalized field notation. -/
def getStructureResolutionOrder (env : Environment) (structName : Name) : Array Name :=
  if let some info := getStructureInfo? env structName then
    info.resolutionOrder
  else
    panic! "structure expected"

-- TODO(kmill) enable once resolution orders are computed
-- /--
-- Return the transitive closure of all parent structures of the structure.
-- This is the same as `Lean.getStructureResolutionOrder` but does not include `structName`.
-- -/
-- partial def getAllParentStructures (env : Environment) (structName : Name) : Array Name :=
--   (getStructureResolutionOrder env structName).erase structName

/-- Get the `StructureFieldInfo` for the given direct field of the structure. -/
def getFieldInfo? (env : Environment) (structName : Name) (fieldName : Name) : Option StructureFieldInfo :=
  if let some info := getStructureInfo? env structName then
    info.fieldInfo.binSearch { fieldName := fieldName, projFn := default, subobject? := none, binderInfo := default } StructureFieldInfo.lt
  else
    none

/-- If `fieldName` is a subobject (that it, if it is an embedded parent structure), then returns the name of that parent structure. -/
def isSubobjectField? (env : Environment) (structName : Name) (fieldName : Name) : Option Name :=
  if let some fieldInfo := getFieldInfo? env structName fieldName then
    fieldInfo.subobject?
  else
    none

/--
Return the parent structures that are embedded in the structure.
This is the array of all results from `Lean.isSubobjectField?` in order.

Note: this is *not* a subset of the parents from `getStructureParentInfo`.
If a direct parent cannot itself be represented as a subobject, there is a chance one of its parents (or one of their parents) can.
-/
def getStructureSubobjects (env : Environment) (structName : Name) : Array Name :=
  (getStructureFields env structName).filterMap (isSubobjectField? env structName)

/-- Return all parent structures -/
partial def getAllParentStructures (env : Environment) (structName : Name) : Array Name :=
  visit structName |>.run #[] |>.2
where
  visit (structName : Name) : StateT (Array Name) Id Unit := do
    for p in getStructureSubobjects env structName do
      modify fun s => s.push p
      visit p

/--
Return the name of the structure that contains the field relative to structure `structName`.
If `structName` contains the field itself, returns that,
and otherwise recursively looks into parents that are subobjects. -/
partial def findField? (env : Environment) (structName : Name) (fieldName : Name) : Option Name :=
  if (getStructureFields env structName).contains fieldName then
    some structName
  else
    getStructureSubobjects env structName |>.findSome? fun parentStructName => findField? env parentStructName fieldName

private partial def getStructureFieldsFlattenedAux (env : Environment) (structName : Name) (fullNames : Array Name) (includeSubobjectFields : Bool) : Array Name :=
  (getStructureFields env structName).foldl (init := fullNames) fun fullNames fieldName =>
    match isSubobjectField? env structName fieldName with
    | some parentStructName =>
      let fullNames := if includeSubobjectFields then fullNames.push fieldName else fullNames
      getStructureFieldsFlattenedAux env parentStructName fullNames includeSubobjectFields
    | none                  => fullNames.push fieldName

/--
Return the full set of field names for the given structure,
"flattening" all the parent structures that are subobject fields.
If `includeSubobjectFields` is true, then subobject `toParent` projections are included, and otherwise they are omitted.

For example, given `Bar` such that
```lean
structure Foo where a : Nat
structure Bar extends Foo where b : Nat
```
this returns ``#[`toFoo, `a, `b]``, or ``#[`a, `b]`` when `includeSubobjectFields := false`.
-/
def getStructureFieldsFlattened (env : Environment) (structName : Name) (includeSubobjectFields := true) : Array Name :=
  getStructureFieldsFlattenedAux env structName #[] includeSubobjectFields

/--
Return true if `constName` is the name of an inductive datatype
created using the `structure` or `class` commands.

See also `Lean.getStructureInfo?`.
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

partial def getPathToBaseStructureAux (env : Environment) (baseStructName : Name) (structName : Name) (path : List Name) : Option (List Name) :=
  if baseStructName == structName then
    some path.reverse
  else
    if let some info := getStructureInfo? env structName then
      -- Prefer subobject projections
      (info.fieldInfo.findSome? fun field =>
        match field.subobject? with
        | none                  => none
        | some parentStructName => getPathToBaseStructureAux env baseStructName parentStructName (field.projFn :: path))
      -- Otherwise, consider other parents
      <|> info.parentInfo.findSome? fun parent =>
        if parent.subobject then
          none
        else
          getPathToBaseStructureAux env baseStructName parent.structName (parent.projFn :: path)
    else none

/--
If `baseStructName` is an ancestor structure for `structName`, then return a sequence of projection functions
to go from `structName` to `baseStructName`. Returns `[]` if `baseStructName == structName`.
-/
def getPathToBaseStructure? (env : Environment) (baseStructName : Name) (structName : Name) : Option (List Name) :=
  getPathToBaseStructureAux env baseStructName structName []

/-- Get the name of the auxiliary definition that would have the default value for the structure field for the projection. -/
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

/-- Return true iff `constName` is the a non-recursive inductive datatype that has only one constructor. -/
def isStructureLike (env : Environment) (constName : Name) : Bool :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [_], numIndices := 0, .. }) => true
  | _ => false

/-- Return number of fields for a structure-like type -/
def getStructureLikeNumFields (env : Environment) (constName : Name) : Nat :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [ctor], numIndices := 0, .. }) =>
    match env.find? ctor with
    | some (.ctorInfo { numFields := n, .. }) => n
    | _ => 0
  | _ => 0

end Lean
