/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
import Lean.Elab.Command
import Lean.Elab.Attributes

namespace Lean
namespace Elab
namespace Command

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

def elabModifiers (stx : Syntax) : CommandElabM Modifiers := do
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
  | some attrs => elabAttrs attrs;
pure {
  docString       := docString,
  visibility      := visibility,
  isPartial       := !partialStx.isNone,
  isUnsafe        := !unsafeStx.isNone,
  isNoncomputable := !noncompStx.isNone,
  attrs           := attrs
}

def checkNotAlreadyDeclared (declName : Name) : CommandElabM Unit := do
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

def applyVisibility (visibility : Visibility) (declName : Name) : CommandElabM Name :=
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

def mkDeclName (modifiers : Modifiers) (atomicName : Name) : CommandElabM Name := do
currNamespace ← getCurrNamespace;
let declName := currNamespace ++ atomicName;
applyVisibility modifiers.visibility declName

def applyAttributes (declName : Name) (attrs : Array Attribute) (applicationTime : AttributeApplicationTime) : CommandElabM Unit :=
attrs.forM $ fun attr => do
 env ← getEnv;
 match getAttributeImpl env attr.name with
 | Except.error errMsg => throwError errMsg
 | Except.ok attrImpl  =>
   when (attrImpl.applicationTime == applicationTime) do
     liftCoreM (attrImpl.add declName attr.args true)

end Command
end Elab
end Lean
