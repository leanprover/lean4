/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Helper functions for retrieving structure information.
-/
import Lean.Environment
import Lean.ProjFns

/- TODO: We currently assume that the projection function for field `fieldName` at structure `structName` is
   `structName ++ fieldName`. This is incorrect for private projections.
   We will fix this by storing a mapping from `structure` + `fieldName` to projection function name in the environment.
   This modification will impact functions such as `getStructureFields` and `getProjFnForField?` -/

namespace Lean

/--
  Return true iff `constName` is the a non-recursive inductive
  datatype that has only one constructor. -/
def isStructureLike (env : Environment) (constName : Name) : Bool :=
  match env.find? constName with
  | some (ConstantInfo.inductInfo { isRec := false, ctors := [ctor], .. }) => true
  | _ => false

/-- We mark subobject fields by prefixing them with "_" in the structure's intro rule. -/
def mkInternalSubobjectFieldName (fieldName : Name) : Name :=
  fieldName.appendBefore "_"

def isInternalSubobjectFieldName : Name → Bool
  | Name.str _ s _ => s.length > 0 && s.get 0 == '_'
  | _              => false

def deinternalizeFieldName : Name → Name
  | n@(Name.str p s _) => if s.length > 0 && s.get 0 == '_' then Name.mkStr p (s.drop 1) else n
  | n                  => n

def getStructureCtor (env : Environment) (constName : Name) : ConstructorVal :=
  match env.find? constName with
  | some (ConstantInfo.inductInfo { isRec := false, ctors := [ctorName], .. }) =>
    match env.find? ctorName with
    | some (ConstantInfo.ctorInfo val) => val
    | _ => panic! "ill-formed environment"
  | _ => panic! "structure expected"

private def getStructureFieldsAux (numParams : Nat) : Nat → Expr → Array Name → Array Name
  | i, Expr.forallE n d b _, fieldNames =>
    if i < numParams then
      getStructureFieldsAux numParams (i+1) b fieldNames
    else
      getStructureFieldsAux numParams (i+1) b <| fieldNames.push <| deinternalizeFieldName n
  | _, _, fieldNames => fieldNames

-- TODO: fix. See comment in the beginning of the file
def getStructureFields (env : Environment) (structName : Name) : Array Name :=
  let ctor := getStructureCtor env structName;
  getStructureFieldsAux ctor.numParams 0 ctor.type #[]

private def isSubobjectFieldAux (numParams : Nat) (target : Name) : Nat → Expr → Option Name
  | i, Expr.forallE n d b _ =>
    if i < numParams then
      isSubobjectFieldAux numParams target (i+1) b
    else if n == target then
      match d.getAppFn with
      | Expr.const parentStructName _ _ => some parentStructName
      | _ => panic! "ill-formed structure"
    else
      isSubobjectFieldAux numParams target (i+1) b
  | _, _ => none

-- TODO: fix. See comment in the beginning of the file
/-- If `fieldName` represents the relation to a parent structure `S`, return `S` -/
def isSubobjectField? (env : Environment) (structName : Name) (fieldName : Name) : Option Name :=
  let ctor := getStructureCtor env structName;
  isSubobjectFieldAux ctor.numParams (mkInternalSubobjectFieldName fieldName) 0 ctor.type

/-- Return immediate parent structures -/
def getParentStructures (env : Environment) (structName : Name) : Array Name :=
  let fieldNames := getStructureFields env structName;
  fieldNames.foldl (init := #[]) fun acc fieldName =>
      match isSubobjectField? env structName fieldName with
      | some parentStructName => acc.push parentStructName
      | none                  => acc

/-- Return all parent structures -/
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

def getStructureFieldsFlattened (env : Environment) (structName : Name) (includeSubobjectFields := true) : Array Name :=
  getStructureFieldsFlattenedAux env structName #[] includeSubobjectFields

-- TODO: fix. See comment in the beginning of the file
private def hasProjFn (env : Environment) (structName : Name) (numParams : Nat) : Nat → Expr → Bool
  | i, Expr.forallE n d b _ =>
    if i < numParams then
      hasProjFn env structName numParams (i+1) b
    else
      let fullFieldName := structName ++ deinternalizeFieldName n;
      env.isProjectionFn fullFieldName
  | _, _ => false

/--
  Return true if `constName` is the name of an inductive datatype
  created using the `structure` or `class` commands.

  We perform the check by testing whether auxiliary projection functions
  have been created. -/
def isStructure (env : Environment) (constName : Name) : Bool :=
  if isStructureLike env constName then
    let ctor := getStructureCtor env constName;
    hasProjFn env constName ctor.numParams 0 ctor.type
  else
    false

-- TODO: fix. See comment in the beginning of the file
def getProjFnForField? (env : Environment) (structName : Name) (fieldName : Name) : Option Name :=
  let fieldNames := getStructureFields env structName;
  if fieldNames.any fun n => fieldName == n then
    some (structName ++ fieldName)
  else
    none

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
  If `baseStructName` is an ancestor structure for `structName`, then return a sequence of projection functions
  to go from `structName` to `baseStructName`. -/
def getPathToBaseStructure? (env : Environment) (baseStructName : Name) (structName : Name) : Option (List Name) :=
  getPathToBaseStructureAux env baseStructName structName []

end Lean
