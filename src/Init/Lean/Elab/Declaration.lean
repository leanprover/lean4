/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Sebastian Ullrich
-/
prelude
import Init.Lean.Elab.Command

namespace Lean
namespace Elab
namespace Command

inductive AttributeArg
| str (val : String)
| num (val : Nat)
| id  (val : Name)

instance AttributeArg.hasToString : HasToString AttributeArg :=
⟨fun arg => match arg with
 | AttributeArg.str v => repr v
 | AttributeArg.num v => toString v
 | AttributeArg.id v  => toString v⟩

structure Attribute :=
(name : Name) (args : Array AttributeArg)

instance Attribute.hasFormat : HasFormat Attribute :=
⟨fun attr => Format.bracket "@[" (toString attr.name ++ (Format.prefixJoin " " attr.args.toList)) "]"⟩

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

def elabAttrArg (stx : Syntax) : CommandElabM AttributeArg := do
match stx.isStrLit? with
| some v => pure $ AttributeArg.str v
| _ =>
match stx.isNatLit? with
| some v => pure $ AttributeArg.num v
| _ =>
match stx with
| Syntax.ident _ _ v _ => pure $ AttributeArg.id v
| _ => throwError stx "unexpected attribute argument"

def elabAttr (stx : Syntax) : CommandElabM Attribute := do
-- rawIdent >> many attrArg
let nameStx := stx.getArg 0;
attrName ← match nameStx.isIdOrAtom? with
  | none     => throwError nameStx "identifier expected"
  | some str => pure $ mkNameSimple str;
unlessM (liftIO stx (isAttribute attrName)) $
  throwError stx ("unknown attribute [" ++ attrName ++ "]");
let argStxs := (stx.getArg 1).getArgs;
args ← argStxs.mapM elabAttrArg;
pure { name := attrName, args := args }

def elabAttrs (stx : Syntax) : CommandElabM (Array Attribute) :=
(stx.getArg 1).foldSepArgsM
  (fun stx attrs => do
    attr ← elabAttr stx;
    pure $ attrs.push attr)
  #[]

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
    | _                 => throwError s ("unexpected doc string " ++ toString (s.getArg 1));
visibility ← match visibilityStx.getOptional? with
  | none   => pure Visibility.regular
  | some v =>
    let kind := v.getKind;
    if kind == `Lean.Parser.Command.private then pure Visibility.private
    else if kind == `Lean.Parser.Command.protected then pure Visibility.protected
    else throwError v "unexpected visibility modifier";
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

@[builtinCommandElab declaration]
def elabDeclaration : CommandElab :=
fun stx => do
  modifiers ← elabModifiers (stx.getArg 0);
  throwError stx.val ("wip, modifiers: " ++ toString modifiers)

end Command
end Elab
end Lean
