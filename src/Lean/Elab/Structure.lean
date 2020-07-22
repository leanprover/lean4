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
(type?      : Option Syntax)
(value?     : Option Syntax)

structure StructView :=
(ref               : Syntax)
(modifiers         : Modifiers)
(scopeLevelNames   : List Name)  -- All `universe` declarations in the current scope
(allUserLevelNames : List Name)  -- `scopeLevelNames` ++ explicit universe parameters provided in the `structure` command
(isClass           : Bool)
(declName          : Name)
(scopeVars         : Array Expr) -- All `variable` declaration in the current scope
(params            : Array Expr) -- Explicit parameters provided in the `structure` command
(parents           : Array Syntax)
(type              : Syntax)
(ctor              : StructCtorView)
(fields            : Array StructFieldView)

inductive StructFieldKind
| newField | fromParent | subobject

structure StructFieldInfo :=
(name   : Name)
(fvar   : Expr)
(kind   : StructFieldKind)
(value? : Option Expr := none)

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
when modifiers.isPrivate $
  throwError ref "private fields are not supported yet";
pure ()

/-
```
def structExplicitBinder := parser! try (declModifiers >> "(") >> many1 ident >> optional inferMod >> optDeclSig >> optional Term.binderDefault >> ")"
def structImplicitBinder := parser! try (declModifiers >> "{") >> many1 ident >> optional inferMod >> declSig >> "}"
def structInstBinder     := parser! try (declModifiers >> "[") >> many1 ident >> optional inferMod >> declSig >> "]"
def structFields         := parser! many (structExplicitBinder <|> structImplicitBinder <|> structInstBinder)
```
-/
private def expandFields (structStx : Syntax) (structDeclName : Name) : CommandElabM (Array StructFieldView) :=
let fieldBinders := ((structStx.getArg 7).getArg 0).getArgs;
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
    let inferMod         := !(fieldBinder.getArg 3).isNone;
    let (binders, type?) :=
      if binfo == BinderInfo.default then
         expandOptDeclSig (fieldBinder.getArg 4)
      else
         let (binders, type) := expandDeclSig (fieldBinder.getArg 4);
         (binders, some type);
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
        when (isInternalSubobjectFieldName name) $
          throwError ident ("invalid field name '" ++ name ++ "', identifiers starting with '_' are reserved to the system");
        let declName := structDeclName ++ name;
        declName ← applyVisibility ident modifiers.visibility declName;
        pure $ views.push {
          ref        := ident,
          modifiers  := modifiers,
          binderInfo := binfo,
          inferMod   := inferMod,
          declName   := declName,
          name       := name,
          binders    := binders,
          type?      := type?,
          value?     := value? })
      views)
  #[]

private def validStructType (type : Expr) : Bool :=
match type with
| Expr.sort (Level.succ _ _) _ => true
| _                            => false

private def checkParentIsStructure (ref : Syntax) (parent : Expr) : TermElabM Name :=
match parent.getAppFn with
| Expr.const c _ _ => do
  env ← Term.getEnv;
  unless (isStructure env c) $
    Term.throwError ref $ "'" ++ toString c ++ "' is not a structure";
  pure c
| _ => Term.throwError ref $ "expected structure"

private def findFieldInfo? (infos : Array StructFieldInfo) (fieldName : Name) : Option StructFieldInfo :=
infos.find? fun info => info.name == fieldName

private def containsFieldName (infos : Array StructFieldInfo) (fieldName : Name) : Bool :=
(findFieldInfo? infos fieldName).isSome

private partial def processSubfields {α} (ref : Syntax) (parentFVar : Expr) (parentStructName : Name) (subfieldNames : Array Name)
    : Nat → Array StructFieldInfo → (Array StructFieldInfo → TermElabM α) → TermElabM α
| i, infos, k =>
  if h : i < subfieldNames.size then do
    let subfieldName := subfieldNames.get ⟨i, h⟩;
    env ← Term.getEnv;
    when (containsFieldName infos subfieldName) $
      Term.throwError ref ("field '" ++ subfieldName ++ "' from '" ++ parentStructName ++ "' has already been declared");
    val  ← Term.liftMetaM ref $ Meta.mkProjection parentFVar subfieldName;
    type ← Term.inferType ref val;
    Term.withLetDecl ref subfieldName type val fun subfieldFVar =>
      let infos := infos.push { name := subfieldName, fvar := subfieldFVar, kind := StructFieldKind.fromParent };
      processSubfields (i+1) infos k
  else
    k infos

private partial def withParents {α} (view : StructView) : Nat → Array StructFieldInfo → (Array StructFieldInfo → TermElabM α) → TermElabM α
| i, infos, k =>
  if h : i < view.parents.size then do
    let parentStx := view.parents.get ⟨i, h⟩;
    parent ← Term.elabType parentStx;
    parentName ← checkParentIsStructure parentStx parent;
    let toParentName := mkNameSimple $ "to" ++ parentName.eraseMacroScopes.getString!; -- erase macro scopes?
    when (containsFieldName infos toParentName) $
      Term.throwError parentStx ("field '" ++ toParentName ++ "' has already been declared");
    env ← Term.getEnv;
    let binfo := if view.isClass && isClass env parentName then BinderInfo.instImplicit else BinderInfo.default;
    Term.withLocalDecl parentStx toParentName binfo parent $ fun parentFVar =>
      let infos := infos.push { name := toParentName, fvar := parentFVar, kind := StructFieldKind.subobject };
      let subfieldNames := getStructureFieldsFlattened env parentName;
      processSubfields parentStx parentFVar parentName subfieldNames 0 infos fun infos => withParents (i+1) infos k
  else
    k infos

private partial def withFields {α} (views : Array StructFieldView) : Nat → Array StructFieldInfo → (Array StructFieldInfo → TermElabM α) → TermElabM α
| i, infos, k =>
  if h : i < views.size then do
    let view := views.get ⟨i, h⟩;
    (type?, value?) ← Term.elabBinders view.binders.getArgs $ fun params => do {
      type? ← match view.type? with
        | none         => pure none
        | some typeStx => do { type ← Term.elabType typeStx; type ← Term.mkForall typeStx params type; pure $ some type };
      value? ← match view.value? with
        | none        => pure none
        | some valStx => do {
          value ← Term.elabTerm valStx type?;
          value ← Term.mkLambda valStx params value;
          value ← Term.ensureHasType valStx type? value;
          pure $ some value
        };
      pure (type?, value?)
    };
    match findFieldInfo? infos view.name with
    | none      => do
      match type?, value? with
      | none,      none => Term.throwError view.ref "invalid field, type expected"
      | some type, _    =>
        Term.withLocalDecl view.ref view.name view.binderInfo type $ fun fieldFVar =>
          let infos := infos.push { name := view.name, fvar := fieldFVar, value? := value?, kind := StructFieldKind.newField };
          withFields (i+1) infos k
      | none, some value => do
        type ← Term.inferType view.ref value;
        Term.withLocalDecl view.ref view.name view.binderInfo type $ fun fieldFVar =>
          let infos := infos.push { name := view.name, fvar := fieldFVar, kind := StructFieldKind.newField };
          withFields (i+1) infos k
    | some info =>
      match info.kind with
      | StructFieldKind.newField   => Term.throwError view.ref ("field '" ++ view.name ++ "' has already been declared")
      | StructFieldKind.fromParent =>
        match value?, type? with
        | none,       _      => Term.throwError view.ref ("field '" ++ view.name ++ "' has been declared in parent structure")
        | _,          some _ => Term.throwError view.type?.get! ("omit field '" ++ view.name ++ "' type to set default value")
        | some value, none   => do
          fvarType ← Term.inferType view.ref info.fvar;
          value    ← Term.ensureHasType view.value?.get! fvarType value;
          let infos := infos.push { info with value? := value };
          withFields (i+1) infos k
      | StructFieldKind.subobject => unreachable!
  else
    k infos

private def getResultUniverse (ref : Syntax) (type : Expr) : TermElabM Level := do
type ← Term.whnf ref type;
match type with
| Expr.sort u _ => pure u
| _             => Term.throwError ref "unexpected structure resulting type"

private def removeUnused (ref : Syntax) (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo)
    : TermElabM (LocalContext × LocalInstances × Array Expr) := do
used ← params.foldlM
   (fun (used : CollectFVars.State) p => do
     type ← Term.inferType ref p;
     Term.collectUsedFVars ref used type)
   {};
used ← fieldInfos.foldlM
  (fun (used : CollectFVars.State) info => do
    fvarType ← Term.inferType ref info.fvar;
    used ← Term.collectUsedFVars ref used fvarType;
    match info.value? with
    | none       => pure used
    | some value => Term.collectUsedFVars ref used value)
  used;
Term.removeUnused ref scopeVars used

private def withUsed {α} (ref : Syntax) (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo) (k : Array Expr → TermElabM α)
    : TermElabM α := do
(lctx, localInsts, vars) ← removeUnused ref scopeVars params fieldInfos;
Term.withLCtx lctx localInsts $ k vars

private def levelMVarToParamFVar (ref : Syntax) (fvar : Expr) : StateT Nat TermElabM Unit := do
type ← liftM $ Term.inferType ref fvar;
_ ← Term.levelMVarToParam' type;
pure ()

private def levelMVarToParamFVars (ref : Syntax) (fvars : Array Expr) : StateT Nat TermElabM Unit :=
fvars.forM (levelMVarToParamFVar ref)

private def levelMVarToParamAux (ref : Syntax) (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo)
    : StateT Nat TermElabM (Array StructFieldInfo) := do
levelMVarToParamFVars ref scopeVars;
levelMVarToParamFVars ref params;
fieldInfos.mapM fun info => do
  levelMVarToParamFVar ref info.fvar;
  match info.value? with
  | none       => pure info
  | some value => do
    value ← Term.levelMVarToParam' value;
    pure { info with value? := value }

private def levelMVarToParam (ref : Syntax) (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo) : TermElabM (Array StructFieldInfo) :=
(levelMVarToParamAux ref scopeVars params fieldInfos).run' 1

private partial def collectUniversesFromFields (ref : Syntax) (r : Level) (rOffset : Nat) (fieldInfos : Array StructFieldInfo) : TermElabM (Array Level) := do
fieldInfos.foldlM
  (fun (us : Array Level) (info : StructFieldInfo) => do
    type ← Term.inferType ref info.fvar;
    u ← Term.getLevel ref type;
    u ← Term.instantiateLevelMVars ref u;
    match accLevelAtCtor u r rOffset us with
    | Except.error msg => Term.throwError ref msg
    | Except.ok us     => pure us)
  #[]

private def updateResultingUniverse (ref : Syntax) (fieldInfos : Array StructFieldInfo) (type : Expr) : TermElabM Expr := do
r ← getResultUniverse ref type;
let rOffset : Nat   := r.getOffset;
let r       : Level := r.getLevelOffset;
match r with
| Level.mvar mvarId _ => do
  us ← collectUniversesFromFields ref r rOffset fieldInfos;
  _root_.dbgTrace ("us: " ++ toString us) fun _ => do
  let rNew := Level.mkNaryMax us.toList;
  Term.assignLevelMVar mvarId rNew;
  Term.instantiateMVars ref type
| _ => Term.throwError ref "failed to compute resulting universe level of structure, provide universe explicitly"

private def elabStructureView (view : StructView) : TermElabM ElabStructResult := do
let numExplicitParams := view.params.size;
type ← Term.elabType view.type;
unless (validStructType type) $ Term.throwError view.type "expected Type";
let ref := view.ref;
withParents view 0 #[] fun fieldInfos =>
withFields view.fields 0 fieldInfos fun fieldInfos => do
  Term.synthesizeSyntheticMVars false;  -- resolve pending
  u ← getResultUniverse ref type;
  inferLevel ← shouldInferResultUniverse ref u;
  withUsed ref view.scopeVars view.params fieldInfos $ fun scopeVars => do
    let numParams := scopeVars.size + numExplicitParams;
    fieldInfos ← levelMVarToParam ref scopeVars view.params fieldInfos;
    type ← if inferLevel then updateResultingUniverse ref fieldInfos type else pure type;
    -- TODO
    Term.throwError view.ref ("WIP " ++ type)

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
let parents   := if exts.isNone then #[] else ((exts.getArg 0).getArg 1).getArgs.getSepElems;
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
    isClass           := isClass,
    scopeVars         := scopeVars,
    params            := params,
    parents           := parents,
    type              := type,
    ctor              := ctor,
    fields            := fields
  };
  pure () -- TODO

end Command
end Elab
end Lean
