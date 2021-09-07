/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Modifiers
import Lean.DocString
import Lean.Elab.Attributes
import Lean.Elab.Exception
import Lean.Elab.DeclUtil

namespace Lean.Elab

def checkNotAlreadyDeclared {m} [Monad m] [MonadEnv m] [MonadError m] (declName : Name) : m Unit := do
  let env ← getEnv
  if env.contains declName then
    match privateToUserName? declName with
    | none          => throwError "'{declName}' has already been declared"
    | some declName => throwError "private declaration '{declName}' has already been declared"
  if env.contains (mkPrivateName env declName) then
    throwError "a private declaration '{declName}' has already been declared"
  match privateToUserName? declName with
  | none => pure ()
  | some declName =>
    if env.contains declName then
      throwError "a non-private declaration '{declName}' has already been declared"

inductive Visibility where
  | regular | «protected» | «private»
  deriving Inhabited

instance : ToString Visibility := ⟨fun
  | Visibility.regular     => "regular"
  | Visibility.«private»   => "private"
  | Visibility.«protected» => "protected"⟩

inductive RecKind where
  | «partial» | «nonrec» | default
  deriving Inhabited

structure Modifiers where
  docString?      : Option String := none
  visibility      : Visibility := Visibility.regular
  isNoncomputable : Bool := false
  recKind         : RecKind := RecKind.default
  isUnsafe        : Bool := false
  attrs           : Array Attribute := #[]
  deriving Inhabited

def Modifiers.isPrivate : Modifiers → Bool
  | { visibility := Visibility.private, .. } => true
  | _                                        => false

def Modifiers.isProtected : Modifiers → Bool
  | { visibility := Visibility.protected, .. } => true
  | _                                          => false

def Modifiers.isPartial : Modifiers → Bool
  | { recKind := RecKind.partial, .. } => true
  | _                                  => false

def Modifiers.isNonrec : Modifiers → Bool
  | { recKind := RecKind.nonrec, .. } => true
  | _                                 => false

def Modifiers.addAttribute (modifiers : Modifiers) (attr : Attribute) : Modifiers :=
  { modifiers with attrs := modifiers.attrs.push attr }

instance : ToFormat Modifiers := ⟨fun m =>
  let components : List Format :=
    (match m.docString? with
     | some str => [f!"/--{str}-/"]
     | none     => [])
    ++ (match m.visibility with
     | Visibility.regular   => []
     | Visibility.protected => [f!"protected"]
     | Visibility.private   => [f!"private"])
    ++ (if m.isNoncomputable then [f!"noncomputable"] else [])
    ++ (match m.recKind with | RecKind.partial => [f!"partial"] | RecKind.nonrec => [f!"nonrec"] | _ => [])
    ++ (if m.isUnsafe then [f!"unsafe"] else [])
    ++ m.attrs.toList.map (fun attr => format attr)
  Format.bracket "{" (Format.joinSep components ("," ++ Format.line)) "}"⟩

instance : ToString Modifiers := ⟨toString ∘ format⟩

def expandOptDocComment? [Monad m] [MonadError m] (optDocComment : Syntax) : m (Option String) :=
  match optDocComment.getOptional? with
  | none   => pure none
  | some s => match s[1] with
    | Syntax.atom _ val => pure (some (val.extract 0 (val.bsize - 2)))
    | _                 => throwErrorAt s "unexpected doc string{indentD s[1]}"

section Methods

variable [Monad m] [MonadEnv m] [MonadResolveName m] [MonadError m] [MonadMacroAdapter m] [MonadRecDepth m] [MonadTrace m] [MonadOptions m] [AddMessageContext m]

def elabModifiers (stx : Syntax) : m Modifiers := do
  let docCommentStx := stx[0]
  let attrsStx      := stx[1]
  let visibilityStx := stx[2]
  let noncompStx    := stx[3]
  let unsafeStx     := stx[4]
  let recKind       :=
    if stx[5].isNone then
      RecKind.default
    else if stx[5][0].getKind == ``Parser.Command.partial then
      RecKind.partial
    else
      RecKind.nonrec
  let docString? ← match docCommentStx.getOptional? with
    | none   => pure none
    | some s => match s[1] with
      | Syntax.atom _ val => pure (some (val.extract 0 (val.bsize - 2)))
      | _                 => throwErrorAt s "unexpected doc string{indentD s[1]}"
  let visibility ← match visibilityStx.getOptional? with
    | none   => pure Visibility.regular
    | some v =>
      let kind := v.getKind
      if kind == `Lean.Parser.Command.private then pure Visibility.private
      else if kind == `Lean.Parser.Command.protected then pure Visibility.protected
      else throwErrorAt v "unexpected visibility modifier"
  let attrs ← match attrsStx.getOptional? with
    | none       => pure #[]
    | some attrs => elabDeclAttrs attrs
  return {
    docString?, visibility, recKind, attrs,
    isUnsafe        := !unsafeStx.isNone
    isNoncomputable := !noncompStx.isNone
  }

def applyVisibility (visibility : Visibility) (declName : Name) : m Name := do
  match visibility with
  | Visibility.private =>
    let env ← getEnv
    let declName := mkPrivateName env declName
    checkNotAlreadyDeclared declName
    pure declName
  | Visibility.protected =>
    checkNotAlreadyDeclared declName
    let env ← getEnv
    let env := addProtected env declName
    setEnv env
    pure declName
  | _ =>
    checkNotAlreadyDeclared declName
    pure declName

def checkIfShadowingStructureField (declName : Name) : m Unit := do
  match declName with
  | Name.str pre .. =>
    if isStructure (← getEnv) pre then
      let fieldNames := getStructureFieldsFlattened (← getEnv) pre
      for fieldName in fieldNames do
        if pre ++ fieldName == declName then
          throwError "invalid declaration name '{declName}', structure '{pre}' has field '{fieldName}'"
  | _ => pure ()

def mkDeclName (currNamespace : Name) (modifiers : Modifiers) (shortName : Name) : m (Name × Name) := do
  let name := (extractMacroScopes shortName).name
  unless name.isAtomic || isFreshInstanceName name do
    throwError "atomic identifier expected '{shortName}'"
  let declName := currNamespace ++ shortName
  checkIfShadowingStructureField declName
  let declName ← applyVisibility modifiers.visibility declName
  match modifiers.visibility with
  | Visibility.protected =>
    match currNamespace with
    | Name.str _ s _ => pure (declName, Name.mkSimple s ++ shortName)
    | _ => throwError "protected declarations must be in a namespace"
  | _ => pure (declName, shortName)

/-
  `declId` is of the form
  ```
  leading_parser ident >> optional (".{" >> sepBy1 ident ", " >> "}")
  ```
  but we also accept a single identifier to users to make macro writing more convenient .
-/
def expandDeclIdCore (declId : Syntax) : Name × Syntax :=
  if declId.isIdent then
    (declId.getId, mkNullNode)
  else
    let id             := declId[0].getId
    let optUnivDeclStx := declId[1]
    (id, optUnivDeclStx)

structure ExpandDeclIdResult where
  shortName  : Name
  declName   : Name
  levelNames : List Name

def expandDeclId (currNamespace : Name) (currLevelNames : List Name) (declId : Syntax) (modifiers : Modifiers) : m ExpandDeclIdResult := do
  -- ident >> optional (".{" >> sepBy1 ident ", " >> "}")
  let (shortName, optUnivDeclStx) := expandDeclIdCore declId
  let levelNames ←
    if optUnivDeclStx.isNone then
      pure currLevelNames
    else
      let extraLevels := optUnivDeclStx[1].getArgs.getEvenElems
      extraLevels.foldlM
        (fun levelNames idStx =>
          let id := idStx.getId
          if levelNames.elem id then
            withRef idStx $ throwAlreadyDeclaredUniverseLevel id
          else
            pure (id :: levelNames))
        currLevelNames
  let (declName, shortName) ← withRef declId $ mkDeclName currNamespace modifiers shortName
  addDocString' declName modifiers.docString?
  pure { shortName := shortName, declName := declName, levelNames := levelNames }

end Methods

end Lean.Elab
