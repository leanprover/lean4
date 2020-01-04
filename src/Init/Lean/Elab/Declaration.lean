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
(name : Name) (args : Array AttributeArg := #[])

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

def Modifiers.addAttribute (modifiers : Modifiers) (attr : Attribute) : Modifiers :=
{ attrs := modifiers.attrs.push attr, .. modifiers }

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

inductive DefKind
| «def» | «theorem» | «example» | «opaque» | «axiom»

@[inline] def withDeclId (declId : Syntax) (f : Name → List Name → CommandElabM Unit) : CommandElabM Unit := do
-- ident >> optional (".{" >> sepBy1 ident ", " >> "}")
let id             := declId.getIdAt 0;
let optUnivDeclStx := declId.getArg 1;
us ←
  if optUnivDeclStx.isNone then
    getUniverseNames
  else do {
    univs ← getUniverseNames;
    let univIds := (optUnivDeclStx.getArg 1).getArgs.getEvenElems;
    univIds.foldlM
      (fun univs idStx =>
        let id := idStx.getId;
        if univs.elem id then
          throwAlreadyDeclaredUniverse idStx id
        else
          pure (id :: univs))
      univs
  };
let us  := us.reverse;
let ref := declId;
match id with
| Name.str pre s _ => withNamespace ref pre (f (mkNameSimple s) us)
| _                => throwError ref "invalid declaration name"

def elabDefCore (ref : Syntax) (kind : DefKind) (modifiers : Modifiers)
    (declId : Syntax) (binders : Syntax) (type : Option Syntax) (val : Option Syntax) : CommandElabM Unit :=
withDeclId declId $ fun id us => do
  ns ← getCurrNamespace;
  dbgTrace (">> " ++ toString ns ++ " " ++ toString id ++ " " ++ toString us);
  pure () -- TODO

def expandOptDeclSig (stx : Syntax) : Syntax × Option Syntax :=
-- many Term.bracktedBinder >> Term.optType
let binders := stx.getArg 0;
let optType := stx.getArg 1; -- optional (parser! " : " >> termParser)
if optType.isNone then
  (binders, none)
else
  let typeSpec := optType.getArg 0;
  (binders, some $ typeSpec.getArg 1)

def expandDeclSig (stx : Syntax) : Syntax × Syntax :=
-- many Term.bracktedBinder >> Term.typeSpec
let binders := stx.getArg 0;
let typeSpec := stx.getArg 1;
(binders, typeSpec.getArg 1)

def elabAbbrev (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "abbrev " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `inline };
let modifiers       := modifiers.addAttribute { name := `reducible };
elabDefCore stx DefKind.def modifiers (stx.getArg 1) binders type (some (stx.getArg 3))

def elabDef (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "def " >> declId >> optDeclSig >> declVal
let (binders, type) := expandOptDeclSig (stx.getArg 2);
elabDefCore stx DefKind.def modifiers (stx.getArg 1) binders type (some (stx.getArg 3))

def elabTheorem (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "theorem " >> declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
elabDefCore stx DefKind.theorem modifiers (stx.getArg 1) binders (some type) (some (stx.getArg 3))

def elabConstant (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "constant " >> declId >> declSig >> optional declValSimple
let (binders, type) := expandDeclSig (stx.getArg 2);
elabDefCore stx DefKind.opaque modifiers (stx.getArg 1) binders (some type) (stx.getArg 3).getOptional?

def elabInstance (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
-- parser! "instance " >> optional declId >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 2);
let modifiers       := modifiers.addAttribute { name := `instance };
declId ← match (stx.getArg 1).getOptional? with
  | some declId => pure declId
  | none        => throwError stx "not implemented yet";
elabDefCore stx DefKind.def modifiers declId binders type (some (stx.getArg 3))

def elabAxiom (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "axiom " >> declId >> declSig
let (binders, type) := expandDeclSig (stx.getArg 2);
elabDefCore stx DefKind.axiom modifiers (stx.getArg 1) binders (some type) none

def elabExample (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
-- parser! "example " >> declSig >> declVal
let (binders, type) := expandDeclSig (stx.getArg 1);
let id              := mkIdentFrom stx `_example;
let declId          := Syntax.node `Lean.Parser.Command.declId #[id, mkNullNode];
elabDefCore stx DefKind.example modifiers declId binders (some type) (some (stx.getArg 2))

def elabInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
pure () -- TODO

def elabClassInductive (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
pure () -- TODO

def elabStructure (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit :=
pure () -- TODO

@[builtinCommandElab declaration]
def elabDeclaration : CommandElab :=
fun stx => do
  modifiers ← elabModifiers (stx.getArg 0);
  let decl     := stx.getArg 1;
  let declKind := decl.getKind;
  if declKind == `Lean.Parser.Command.abbrev then
    elabAbbrev modifiers decl
  else if declKind == `Lean.Parser.Command.def then
    elabDef modifiers decl
  else if declKind == `Lean.Parser.Command.theorem then
    elabTheorem modifiers decl
  else if declKind == `Lean.Parser.Command.constant then
    elabConstant modifiers decl
  else if declKind == `Lean.Parser.Command.instance then
    elabInstance modifiers decl
  else if declKind == `Lean.Parser.Command.axiom then
    elabAxiom modifiers decl
  else if declKind == `Lean.Parser.Command.example then
    elabExample modifiers decl
  else if declKind == `Lean.Parser.Command.inductive then
    elabInductive modifiers decl
  else if declKind == `Lean.Parser.Command.classInductive then
    elabClassInductive modifiers decl
  else if declKind == `Lean.Parser.Command.structure then
    elabStructure modifiers decl
  else
    throwError stx.val "unexpected declaration"

end Command
end Elab
end Lean
