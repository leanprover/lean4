/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Command
import Lean.Elab.DeclModifiers
import Lean.Elab.DeclUtil
import Lean.Elab.Inductive

namespace Lean
namespace Elab
namespace Command

/- Recall that the `structure command syntax is
```
parser! (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> " := " >> optional structCtor >> structFields
```
-/

structure StructCtorView :=
(ref       : Syntax)
(modifiers : Modifiers)
(inferMod  : Bool)  -- true if `{}` is used in the constructor declaration
(name      : Name)
(declName  : Name)

structure StructFieldView :=
(ref        : Syntax)
(modifiers  : Modifiers)
(binderInfo : BinderInfo)
(inferMod   : Bool)
(declName   : Name)
(name       : Name)
(binders    : Syntax)
(type       : Syntax)
(value?     : Option Syntax)

structure StructView :=
(ref               : Syntax)
(modifiers         : Modifiers)
(scopeLevelNames   : List Name)  -- All `universe` declarations in the current scope
(allUserLevelNames : List Name)  -- `scopeLevelNames` ++ explicit universe parameters provided in the `structure` command
(declName          : Name)
(scopeVars         : Array Expr) -- All `variable` declaration in the current scope
(params            : Array Expr) -- Explicit parameters provided in the `structure` command
(parents           : Array Syntax)
(ctor              : StructCtorView)
(fields            : Array StructFieldView)

structure ElabStructResult :=
(decl      : Declaration)

private def defaultCtorName := `mk

/-
The structore constructor syntax is
```
parser! try (declModifiers >> ident >> optional inferMod >> " :: ")
```
-/
private def expandCtor (structStx : Syntax) (structDeclName : Name) : CommandElabM StructCtorView :=
let optCtor := structStx.getArg 6;
if optCtor.isNone then
  pure { ref := structStx, modifiers := {}, inferMod := false, name := defaultCtorName, declName := structDeclName ++ defaultCtorName }
else do
  let ctor := optCtor.getArg 0;
  modifiers ← elabModifiers (ctor.getArg 0);
  checkValidCtorModifier ctor modifiers;
  let inferMod := !(ctor.getArg 2).isNone;
  let name := ctor.getIdAt 1;
  let declName := structDeclName ++ name;
  declName ← applyVisibility ctor modifiers.visibility declName;
  pure { ref := ctor, name := name, modifiers := modifiers, inferMod := inferMod, declName := declName }

def checkValidFieldModifier (ref : Syntax) (modifiers : Modifiers) : CommandElabM Unit := do
when modifiers.isNoncomputable $
  throwError ref "invalid use of 'noncomputable' in field declaration";
when modifiers.isPartial $
  throwError ref "invalid use of 'partial' in field declaration";
when modifiers.isUnsafe $
  throwError ref "invalid use of 'unsafe' in field declaration";
when (modifiers.attrs.size != 0) $
  throwError ref "invalid use of attributes in field declaration";
pure ()

/-
```
def structExplicitBinder := parser! try (declModifiers >> "(") >> many1 ident >> optional inferMod >> declSig >> optional Term.binderDefault >> ")"
def structImplicitBinder := parser! try (declModifiers >> "{") >> many1 ident >> optional inferMod >> declSig >> "}"
def structInstBinder     := parser! try (declModifiers >> "[") >> many1 ident >> optional inferMod >> declSig >> "]"
def structFields         := parser! many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
```
-/
private def expandFields (structStx : Syntax) (structDeclName : Name) : CommandElabM (Array StructFieldView) :=
let fieldBinders := (structStx.getArg 7).getArgs;
fieldBinders.foldlM
  (fun (views : Array StructFieldView) fieldBinder => do
    let k := fieldBinder.getKind;
    binfo ←
      if k == `Lean.Parser.Command.structExplicitBinder then pure BinderInfo.default
      else if k == `Lean.Parser.Command.structImplicitBinder then pure BinderInfo.implicit
      else if k == `Lean.Parser.Command.structInstBinder then pure BinderInfo.instImplicit
      else throwError fieldBinder "unexpected kind of structure field";
    modifiers ← elabModifiers (fieldBinder.getArg 0);
    checkValidFieldModifier fieldBinder modifiers;
    let inferMod        := !(fieldBinder.getArg 3).isNone;
    let (binders, type) := expandDeclSig (fieldBinder.getArg 4);
    let value? :=
      if binfo != BinderInfo.default then none
      else
        let optBinderDefault := fieldBinder.getArg 5;
        if optBinderDefault.isNone then none
        else
          -- binderDefault := parser! " := " >> termParser
          some $ (optBinderDefault.getArg 0).getArg 1;
    let idents := (fieldBinder.getArg 2).getArgs;
    idents.foldlM
      (fun (views : Array StructFieldView) ident => do
        let name     := ident.getId;
        let declName := structDeclName ++ name;
        declName ← applyVisibility ident modifiers.visibility declName;
        pure $ views.push {
          ref        := fieldBinder,
          modifiers  := modifiers,
          binderInfo := binfo,
          inferMod   := inferMod,
          declName   := declName,
          name       := name,
          binders    := binders,
          type       := type,
          value?     := value? })
      views)
  #[]

private def elabStructureView (view : StructView) : TermElabM ElabStructResult :=
throw $ arbitrary _ -- TODO

/-
parser! (structureTk <|> classTk) >> declId >> many Term.bracketedBinder >> optional «extends» >> Term.optType >> " := " >> optional structCtor >> structFields

where
def «extends» := parser! " extends " >> sepBy1 termParser ", "
def typeSpec := parser! " : " >> termParser
def optType : Parser := optional typeSpec

def structFields         := parser! many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
def structCtor           := parser! try (declModifiers >> ident >> optional inferMod >> " :: ")

-/
def elabStructure (modifiers : Modifiers) (stx : Syntax) : CommandElabM Unit := do
checkValidInductiveModifier stx modifiers;
let isClass   := (stx.getArg 0).getKind == `Lean.Parser.Command.classTk;
let modifiers := if isClass then modifiers.addAttribute { name := `class } else modifiers;
let declId    := stx.getArg 1;
let params    := (stx.getArg 2).getArgs;
let exts      := stx.getArg 3;
let parents   := if exts.isNone then #[] else (exts.getArg 1).getArgs.getSepElems;
let optType   := stx.getArg 4;
type ← if optType.isNone then `(Type _) else pure $ (optType.getArg 0).getArg 1;
scopeLevelNames ← getLevelNames;
withDeclId declId $ fun name => do
  declName ← mkDeclName declId modifiers name;
  allUserLevelNames ← getLevelNames;
  ctor ← expandCtor stx declName;
  fields ← expandFields stx declName;
  r ← runTermElabM declName $ fun scopeVars => Term.elabBinders params $ fun params => elabStructureView {
    ref               := stx,
    modifiers         := modifiers,
    scopeLevelNames   := scopeLevelNames,
    allUserLevelNames := allUserLevelNames,
    declName          := declName,
    scopeVars         := scopeVars,
    params            := params,
    parents           := parents,
    ctor              := ctor,
    fields            := fields
  };
  pure () -- TODO

end Command
end Elab
end Lean
