/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Modifiers
import Lean.Elab.Attributes
import Lean.Elab.Exception
import Lean.Elab.DeclUtil

namespace Lean
namespace Elab

def checkNotAlreadyDeclared {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m]
     (declName : Name) : m Unit := do
env ← getEnv;
when (env.contains declName) $
  match privateToUserName? declName with
  | none          => throwError ("'" ++ declName ++ "' has already been declared")
  | some declName => throwError ("private declaration '" ++ declName ++ "' has already been declared");
when (env.contains (mkPrivateName env declName)) $
  throwError ("a private declaration '" ++ declName ++ "' has already been declared");
match privateToUserName? declName with
| none => pure ()
| some declName =>
  when (env.contains declName) $
    throwError ("a non-private declaration '" ++ declName ++ "' has already been declared")

inductive Visibility
| regular | «protected» | «private»

instance Visibility.hasToString : HasToString Visibility :=
⟨fun v => match v with
 | Visibility.regular   => "regular"
 | Visibility.private   => "private"
 | Visibility.protected => "protected"⟩

structure Modifiers :=
(docString       : Option String := none)
(visibility      : Visibility := Visibility.regular)
(isNoncomputable : Bool := false)
(isPartial       : Bool := false)
(isUnsafe        : Bool := false)
(attrs           : Array Attribute := #[])

def Modifiers.isPrivate : Modifiers → Bool
| { visibility := Visibility.private, .. } => true
| _                                        => false

def Modifiers.isProtected : Modifiers → Bool
| { visibility := Visibility.protected, .. } => true
| _                                          => false

def Modifiers.addAttribute (modifiers : Modifiers) (attr : Attribute) : Modifiers :=
{ modifiers with attrs := modifiers.attrs.push attr }

instance Modifiers.hasFormat : HasFormat Modifiers :=
⟨fun m =>
  let components : List Format :=
    (match m.docString with
     | some str => ["/--" ++ str ++ "-/"]
     | none     => [])
    ++ (match m.visibility with
     | Visibility.regular   => []
     | Visibility.protected => ["protected"]
     | Visibility.private   => ["private"])
    ++ (if m.isNoncomputable then ["noncomputable"] else [])
    ++ (if m.isPartial then ["partial"] else [])
    ++ (if m.isUnsafe then ["unsafe"] else [])
    ++ m.attrs.toList.map (fun attr => fmt attr);
  Format.bracket "{" (Format.joinSep components ("," ++ Format.line)) "}"⟩

instance Modifiers.hasToString : HasToString Modifiers := ⟨toString ∘ format⟩

section Methods

variables {m : Type → Type} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m]

def elabModifiers (stx : Syntax) : m Modifiers := do
let docCommentStx := stx.getArg 0;
let attrsStx      := stx.getArg 1;
let visibilityStx := stx.getArg 2;
let noncompStx    := stx.getArg 3;
let unsafeStx     := stx.getArg 4;
let partialStx    := stx.getArg 5;
docString ← match docCommentStx.getOptional? with
  | none   => pure none
  | some s => match s.getArg 1 with
    | Syntax.atom _ val => pure (some (val.extract 0 (val.bsize - 2)))
    | _                 => throwErrorAt s ("unexpected doc string " ++ toString (s.getArg 1));
visibility ← match visibilityStx.getOptional? with
  | none   => pure Visibility.regular
  | some v =>
    let kind := v.getKind;
    if kind == `Lean.Parser.Command.private then pure Visibility.private
    else if kind == `Lean.Parser.Command.protected then pure Visibility.protected
    else throwErrorAt v "unexpected visibility modifier";
attrs ← match attrsStx.getOptional? with
  | none       => pure #[]
  | some attrs => elabDeclAttrs attrs;
pure {
  docString       := docString,
  visibility      := visibility,
  isPartial       := !partialStx.isNone,
  isUnsafe        := !unsafeStx.isNone,
  isNoncomputable := !noncompStx.isNone,
  attrs           := attrs
}

def applyVisibility (visibility : Visibility) (declName : Name) : m Name :=
match visibility with
| Visibility.private => do
  env ← getEnv;
  let declName := mkPrivateName env declName;
  checkNotAlreadyDeclared declName;
  pure declName
| Visibility.protected => do
  checkNotAlreadyDeclared declName;
  env ← getEnv;
  let env := addProtected env declName;
  setEnv env;
  pure declName
| _                  => do
  checkNotAlreadyDeclared declName;
  pure declName

def mkDeclName (currNamespace : Name) (modifiers : Modifiers) (shortName : Name) : m (Name × Name) := do
let name := (extractMacroScopes shortName).name;
unless (name.isAtomic || isFreshInstanceName name) $
  throwError ("atomic identifier expected '" ++ shortName ++ "'");
let declName := currNamespace ++ shortName;
declName ← applyVisibility modifiers.visibility declName;
match modifiers.visibility with
| Visibility.protected =>
  match currNamespace with
  | Name.str _ s _ => pure (declName, mkNameSimple s ++ shortName)
  | _ => throwError ("protected declarations must be in a namespace")
| _ => pure (declName, shortName)

/-
  `declId` is of the form
  ```
  parser! ident >> optional (".{" >> sepBy1 ident ", " >> "}")
  ```
  but we also accept a single identifier to users to make macro writing more convenient .
-/
def expandDeclIdCore (declId : Syntax) : Name × Syntax :=
if declId.isIdent then
  (declId.getId, mkNullNode)
else
  let id             := declId.getIdAt 0;
  let optUnivDeclStx := declId.getArg 1;
  (id, optUnivDeclStx)

structure ExpandDeclIdResult :=
(shortName  : Name)
(declName   : Name)
(levelNames : List Name)

def expandDeclId (currNamespace : Name) (currLevelNames : List Name) (declId : Syntax) (modifiers : Modifiers) : m ExpandDeclIdResult := do
-- ident >> optional (".{" >> sepBy1 ident ", " >> "}")
let (shortName, optUnivDeclStx) := expandDeclIdCore declId;
levelNames      ←
  if optUnivDeclStx.isNone then
    pure currLevelNames
  else do {
    let extraLevels := (optUnivDeclStx.getArg 1).getArgs.getEvenElems;
    extraLevels.foldlM
      (fun levelNames idStx =>
        let id := idStx.getId;
        if levelNames.elem id then
          withRef idStx $ throwAlreadyDeclaredUniverseLevel id
        else
          pure (id :: levelNames))
      currLevelNames
  };
(declName, shortName) ← withRef declId $ mkDeclName currNamespace modifiers shortName;
pure { shortName := shortName, declName := declName, levelNames := levelNames }

end Methods

end Elab
end Lean
