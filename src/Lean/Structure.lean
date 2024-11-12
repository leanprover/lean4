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
These are direct fields of a structure, including "subobject" fields for the embedded parents.
The full collection of fields is the transitive closure of fields through the subobject fields.
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
  /-- If set, the field is an autoparam (a field declared using `fld := by ...` syntax).
  The expression evaluates to a tactic `Syntax` object. Generally this is an `Expr.const` expression. -/
  autoParam? : Option Expr := none
  deriving Inhabited, Repr

def StructureFieldInfo.lt (i₁ i₂ : StructureFieldInfo) : Bool :=
  Name.quickLt i₁.fieldName i₂.fieldName

/--
Data for a direct parent of a structure.
Some structure parents are represented as subobjects (embedded structures),
and for these the parent projection is a true projection.
If a structure parent shares a field with a previous parent, it will become an implicit parent,
and all the fields of the structure parent that do not occur in earlier parents are fields of the new structure
-/
structure StructureParentInfo where
  /-- The name of the parent structure. -/
  structName : Name
  /-- Whether this parent structure is represented as a subobject. If so, then there is a `fieldInfo` entry with the same `projFn`. -/
  subobject  : Bool
  /-- The projection function associated to the field. For subobjects, this is the same as the `projFn` in its `fieldInfo` entry. -/
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
  deriving Inhabited

def StructureInfo.lt (i₁ i₂ : StructureInfo) : Bool :=
  Name.quickLt i₁.structName i₂.structName

def StructureInfo.getProjFn? (info : StructureInfo) (i : Nat) : Option Name :=
  if h : i < info.fieldNames.size then
    let fieldName := info.fieldNames[i]
    info.fieldInfo.binSearch { fieldName := fieldName, projFn := default, subobject? := none, binderInfo := default } StructureFieldInfo.lt |>.map (·.projFn)
  else
    none

/-- Auxiliary state for structures defined in the current module. -/
private structure StructureState where
  map : PersistentHashMap Name StructureInfo := {}
  deriving Inhabited

builtin_initialize structureExt : PersistentEnvExtension StructureInfo StructureInfo (Unit × StructureState) ← registerPersistentEnvExtension {
  mkInitial       := pure ((), {})
  addImportedFn   := fun _ => pure ((), {})
  addEntryFn      := fun (_, s) e => ((), { s with map := s.map.insert e.structName e })
  exportEntriesFn := fun (_, s) => s.map.toArray |>.map (·.snd) |>.qsort StructureInfo.lt
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
Declare a new structure to the elaborator.
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
Throws an error if the structure has not already been registered with `Lean.registerStructure`.
-/
def setStructureParents [Monad m] [MonadEnv m] [MonadError m] (structName : Name) (parentInfo : Array StructureParentInfo) : m Unit := do
  let some info := structureExt.getState (← getEnv) |>.snd.map.find? structName
    | throwError "cannot set structure parents for '{structName}', structure not defined in current module"
  modifyEnv fun env => structureExt.addEntry env { info with parentInfo }

/-- Gets the `StructureInfo` if `structName` has been declared as a structure to the elaborator. -/
def getStructureInfo? (env : Environment) (structName : Name) : Option StructureInfo :=
  match env.getModuleIdxFor? structName with
  | some modIdx => structureExt.getModuleEntries env modIdx |>.binSearch { structName } StructureInfo.lt
  | none        => structureExt.getState env |>.snd.map.find? structName

/--
Gets the `StructureInfo` for `structName`, which is assumed to have been declared as a structure to the elaborator.
Panics on failure.
-/
def getStructureInfo (env : Environment) (structName : Name) : StructureInfo :=
  if let some info := getStructureInfo? env structName then
    info
  else
    panic! "structure expected"

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
  (getStructureInfo env structName).fieldNames

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

/-- Get information for all the parents that appear in the `extends` clause. -/
def getStructureParentInfo (env : Environment) (structName : Name) : Array StructureParentInfo :=
  (getStructureInfo env structName).parentInfo

/--
Return the parent structures that are embedded in the structure.
This is the array of all results from `Lean.isSubobjectField?` in order.

Note: this is *not* a subset of the parents from `getStructureParentInfo`.
If a direct parent cannot itself be represented as a subobject,
sometimes one of its parents (or one of their parents, etc.) can.
-/
def getStructureSubobjects (env : Environment) (structName : Name) : Array Name :=
  (getStructureFields env structName).filterMap (isSubobjectField? env structName)

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
Returns the full set of field names for the given structure,
"flattening" all the parent structures that are subobject fields.
If `includeSubobjectFields` is true, then subobject `toParent` projections are included,
and otherwise they are omitted.

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
Returns true if `constName` is the name of an inductive datatype
created using the `structure` or `class` commands.

These are inductive types for which structure information has been registered with `registerStructure`.
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

/-- Get the name of the auxiliary definition that would have the default value for the structure field. -/
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

/--
Returns true iff `constName` is a non-recursive inductive datatype that has only one constructor and no indices.

Such types have special kernel support. This must be in sync with `is_structure_like`.
-/
def isStructureLike (env : Environment) (constName : Name) : Bool :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [_], numIndices := 0, .. }) => true
  | _ => false

/--
Returns the constructor of the structure named `constName` if it is a non-recursive single-constructor inductive type with no indices.
-/
def getStructureLikeCtor? (env : Environment) (constName : Name) : Option ConstructorVal :=
  match env.find? constName with
  | some (.inductInfo { isRec := false, ctors := [ctorName], numIndices := 0, .. }) =>
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

/-!
### Resolution orders

This section is for computations to determine which namespaces to visit when resolving field notation.
While the set of namespaces is clear (after a structure's namespace, it is the namespaces for *all* parents),
the question is the order to visit them in.

We use the C3 superclass linearization algorithm from Barrett et al., "A Monotonic Superclass Linearization for Dylan", OOPSLA 1996.
For reference, the C3 linearization is known as the "method resolution order" (MRO) [in Python](https://docs.python.org/3/howto/mro.html).

The basic idea is that we want to find a resolution order with the following property:
For each structure `S` that appears in the resolution order, if its direct parents are `P₁ .. Pₙ`,
then `S P₁ ... Pₙ` forms a subsequence of the resolution order.

This has a stability property where if `S` extends `S'`, then the resolution order of `S` contains the resolution order of `S'` as a subsequence.
It also has the key property that if `P` and `P'` are parents of `S`, then we visit `P` and `P'` before we visit the shared parents of `P` and `P'`.

Finding such a resolution order might not be possible.
Still, we can enable a relaxation of the algorithm by ignoring one or more parent resolution orders, starting from the end.

In Hivert and Thiéry "Controlling the C3 super class linearization algorithm for large hierarchies of classes"
https://arxiv.org/pdf/2401.12740 the authors discuss how in SageMath, which has thousands of classes,
C3 can be difficult to control, since maintaining correct direct parent orders is a burden.
They give suggestions that have worked for the SageMath project.
We may consider introducing an environment extension with ordering hints to help guide the algorithm if we see similar difficulties.
-/

structure StructureResolutionState where
  resolutions : PHashMap Name (Array Name) := {}
  deriving Inhabited

/--
We use an environment extension to cache resolution orders.
These are not expensive to compute, but worth caching, and we save olean storage space.
-/
builtin_initialize structureResolutionExt : EnvExtension StructureResolutionState ←
  registerEnvExtension (pure {})

/-- Gets the resolution order if it has already been cached. -/
private def getStructureResolutionOrder? (env : Environment) (structName : Name) : Option (Array Name) :=
  (structureResolutionExt.getState env).resolutions.find? structName

/-- Caches a structure's resolution order. -/
private def setStructureResolutionOrder [MonadEnv m] (structName : Name) (resolutionOrder : Array Name) : m Unit :=
  modifyEnv fun env => structureResolutionExt.modifyState env fun s =>
    { s with resolutions := s.resolutions.insert structName resolutionOrder }

/-- "The `badParent` must come after the `conflicts`. -/
structure StructureResolutionOrderConflict where
  isDirectParent : Bool
  badParent : Name
  /-- Conflicts that must come before `badParent`. The flag is whether it is a direct parent. -/
  conflicts : Array (Bool × Name)
  deriving Inhabited

structure StructureResolutionOrderResult where
  resolutionOrder : Array Name
  conflicts : Array StructureResolutionOrderConflict := #[]
  deriving Inhabited

/--
Computes and caches the C3 linearization. Assumes parents have already been set with `setStructureParents`.
If `relaxed` is false, then if the linearization cannot be computed, conflicts are recorded in the return value.
-/
partial def computeStructureResolutionOrder [Monad m] [MonadEnv m]
    (structName : Name) (relaxed : Bool) : m StructureResolutionOrderResult := do
  let env ← getEnv
  if let some resOrder := getStructureResolutionOrder? env structName then
    return { resolutionOrder := resOrder }
  let parentNames := getStructureParentInfo env structName |>.map (·.structName)
  -- Don't be strict about parents: if they were supposed to be checked, they were already checked.
  let parentResOrders ← parentNames.mapM fun parentName => return (← computeStructureResolutionOrder parentName true).resolutionOrder

  -- `resOrders` contains the resolution orders to merge.
  -- The parent list is inserted as a pseudo resolution order to ensure immediate parents come out in order,
  -- and it is added first to be the primary ordering constraint when there are ordering errors.
  let mut resOrders := parentResOrders.insertAt 0 parentNames |>.filter (!·.isEmpty)

  let mut resOrder : Array Name := #[structName]
  let mut defects : Array StructureResolutionOrderConflict := #[]
  -- Every iteration of the loop, the sum of the sizes of the arrays in `resOrders` decreases by at least one,
  -- so it terminates.
  while !resOrders.isEmpty do
    let (good, name) ← selectParent resOrders

    unless good || relaxed do
      let conflicts := resOrders |>.filter (·[1:].any (· == name)) |>.map (·[0]!) |>.qsort Name.lt |>.eraseReps
      defects := defects.push {
        isDirectParent := parentNames.contains name
        badParent := name
        conflicts := conflicts.map fun c => (parentNames.contains c, c)
      }

    resOrder := resOrder.push name
    resOrders := resOrders
      |>.map (fun resOrder => resOrder.filter (· != name))
      |>.filter (!·.isEmpty)

  setStructureResolutionOrder structName resOrder
  return { resolutionOrder := resOrder, conflicts := defects }
where
  selectParent (resOrders : Array (Array Name)) : m (Bool × Name) := do
    -- Assumption: every resOrder is nonempty.
    -- `n'` is for relaxation, to stop paying attention to end of `resOrders` when finding a good parent.
    for n' in [0 : resOrders.size] do
      let hi := resOrders.size - n'
      for i in [0 : hi] do
        let parent := resOrders[i]![0]!
        let consistent resOrder := resOrder[1:].all (· != parent)
        if resOrders[0:i].all consistent && resOrders[i+1:hi].all consistent then
          return (n' == 0, parent)
    -- unreachable, but correct default:
    return (false, resOrders[0]![0]!)

/--
Gets the resolution order for a structure.
-/
def getStructureResolutionOrder [Monad m] [MonadEnv m]
    (structName : Name) : m (Array Name) :=
  (·.resolutionOrder) <$> computeStructureResolutionOrder structName (relaxed := true)

/--
Returns the transitive closure of all parent structures of the structure.
This is the same as `Lean.getStructureResolutionOrder` but without including `structName`.
-/
partial def getAllParentStructures [Monad m] [MonadEnv m] (structName : Name) : m (Array Name) :=
  (·.erase structName) <$> getStructureResolutionOrder structName

end Lean
