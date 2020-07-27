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
(name     : Name)
(declName : Name) -- Remark: this field value doesn't matter for fromParent fields.
(fvar     : Expr)
(kind     : StructFieldKind)
(inferMod : Bool := false)
(value?   : Option Expr := none)

instance StructFieldInfo.inhabited : Inhabited StructFieldInfo :=
⟨{ name := arbitrary _, declName := arbitrary _, fvar := arbitrary _, kind := StructFieldKind.newField }⟩

def StructFieldInfo.isFromParent (info : StructFieldInfo) : Bool :=
match info.kind with
| StructFieldKind.fromParent => true
| _                          => false

def StructFieldInfo.isSubobject (info : StructFieldInfo) : Bool :=
match info.kind with
| StructFieldKind.subobject => true
| _                         => false

/- Auxiliary declaration for `mkProjections` -/
structure ProjectionInfo :=
(declName : Name)
(inferMod : Bool)

structure ElabStructResult :=
(decl            : Declaration)
(projInfos       : List ProjectionInfo)
(projInstances   : List Name) -- projections (to parent classes) that must be marked as instances.
(mctx            : MetavarContext)
(lctx            : LocalContext)
(localInsts      : LocalInstances)
(defaultAuxDecls : Array (Name × Expr × Expr))

private def defaultCtorName := `mk

/-
The structore constructor syntax is
```
parser! try (declModifiers >> ident >> optional inferMod >> " :: ")
```
-/
private def expandCtor (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : CommandElabM StructCtorView :=
let optCtor := structStx.getArg 6;
if optCtor.isNone then
  pure { ref := structStx, modifiers := {}, inferMod := false, name := defaultCtorName, declName := structDeclName ++ defaultCtorName }
else do
  let ctor := optCtor.getArg 0;
  ctorModifiers ← elabModifiers (ctor.getArg 0);
  checkValidCtorModifier ctor ctorModifiers;
  when (ctorModifiers.isPrivate && structModifiers.isPrivate) $
    throwError ctor "invalid 'private' constructor in a 'private' structure";
  when (ctorModifiers.isProtected && structModifiers.isPrivate) $
    throwError ctor "invalid 'protected' constructor in a 'private' structure";
  let inferMod := !(ctor.getArg 2).isNone;
  let name := ctor.getIdAt 1;
  let declName := structDeclName ++ name;
  declName ← applyVisibility ctor ctorModifiers.visibility declName;
  pure { ref := ctor, name := name, modifiers := ctorModifiers, inferMod := inferMod, declName := declName }

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
private def expandFields (structStx : Syntax) (structModifiers : Modifiers) (structDeclName : Name) : CommandElabM (Array StructFieldView) :=
let fieldBinders := ((structStx.getArg 7).getArg 0).getArgs;
fieldBinders.foldlM
  (fun (views : Array StructFieldView) fieldBinder => do
    let k := fieldBinder.getKind;
    binfo ←
      if k == `Lean.Parser.Command.structExplicitBinder then pure BinderInfo.default
      else if k == `Lean.Parser.Command.structImplicitBinder then pure BinderInfo.implicit
      else if k == `Lean.Parser.Command.structInstBinder then pure BinderInfo.instImplicit
      else throwError fieldBinder "unexpected kind of structure field";
    fieldModifiers ← elabModifiers (fieldBinder.getArg 0);
    checkValidFieldModifier fieldBinder fieldModifiers;
    when (fieldModifiers.isPrivate && structModifiers.isPrivate) $
      throwError fieldBinder "invalid 'private' field in a 'private' structure";
    when (fieldModifiers.isProtected && structModifiers.isPrivate) $
      throwError fieldBinder "invalid 'protected' field in a 'private' structure";
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
        declName ← applyVisibility ident fieldModifiers.visibility declName;
        pure $ views.push {
          ref        := ident,
          modifiers  := fieldModifiers,
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

private partial def processSubfields {α} (ref : Syntax) (structDeclName : Name) (parentFVar : Expr) (parentStructName : Name) (subfieldNames : Array Name)
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
      /- The following `declName` is only used for creating the `_default` auxiliary declaration name when
         its default value is overwritten in the structure. -/
      let declName := structDeclName ++ subfieldName;
      let infos := infos.push { name := subfieldName, declName := declName, fvar := subfieldFVar, kind := StructFieldKind.fromParent };
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
      let infos := infos.push { name := toParentName, declName := view.declName ++ toParentName, fvar := parentFVar, kind := StructFieldKind.subobject };
      let subfieldNames := getStructureFieldsFlattened env parentName;
      processSubfields parentStx view.declName parentFVar parentName subfieldNames 0 infos fun infos => withParents (i+1) infos k
  else
    k infos

private partial def withFields {α} (views : Array StructFieldView) : Nat → Array StructFieldInfo → (Array StructFieldInfo → TermElabM α) → TermElabM α
| i, infos, k =>
  if h : i < views.size then do
    let view := views.get ⟨i, h⟩;
    match findFieldInfo? infos view.name with
    | none      => do
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
      match type?, value? with
      | none,      none => Term.throwError view.ref "invalid field, type expected"
      | some type, _    =>
        Term.withLocalDecl view.ref view.name view.binderInfo type $ fun fieldFVar =>
          let infos := infos.push { name := view.name, declName := view.declName, fvar := fieldFVar, value? := value?,
                                    kind := StructFieldKind.newField, inferMod := view.inferMod };
          withFields (i+1) infos k
      | none, some value => do
        type ← Term.inferType view.ref value;
        Term.withLocalDecl view.ref view.name view.binderInfo type $ fun fieldFVar =>
          let infos := infos.push { name := view.name, declName := view.declName, fvar := fieldFVar, kind := StructFieldKind.newField, inferMod := view.inferMod };
          withFields (i+1) infos k
    | some info =>
      match info.kind with
      | StructFieldKind.newField   => Term.throwError view.ref ("field '" ++ view.name ++ "' has already been declared")
      | StructFieldKind.fromParent =>
        match view.value? with
        | none       => Term.throwError view.ref ("field '" ++ view.name ++ "' has been declared in parent structure")
        | some valStx => do
          when (!view.binders.getArgs.isEmpty || view.type?.isSome) $
            Term.throwError view.type?.get! ("omit field '" ++ view.name ++ "' type to set default value");
          fvarType ← Term.inferType view.ref info.fvar;
          value ← Term.elabTerm valStx fvarType;
          value ← Term.ensureHasType valStx fvarType value;
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
  let rNew := Level.mkNaryMax us.toList;
  Term.assignLevelMVar mvarId rNew;
  Term.instantiateMVars ref type
| _ => Term.throwError ref "failed to compute resulting universe level of structure, provide universe explicitly"

private def collectLevelParamsInFVar (ref : Syntax) (s : CollectLevelParams.State) (fvar : Expr) : TermElabM CollectLevelParams.State := do
type ← Term.inferType ref fvar;
type ← Term.instantiateMVars ref type;
pure $ collectLevelParams s type

private def collectLevelParamsInFVars (ref : Syntax) (fvars : Array Expr) (s : CollectLevelParams.State) : TermElabM CollectLevelParams.State :=
fvars.foldlM (collectLevelParamsInFVar ref) s

private def collectLevelParamsInStructure (ref : Syntax) (scopeVars : Array Expr) (params : Array Expr) (fieldInfos : Array StructFieldInfo) : TermElabM (Array Name) := do
s ← collectLevelParamsInFVars ref scopeVars {};
s ← collectLevelParamsInFVars ref params s;
s ← fieldInfos.foldlM (fun (s : CollectLevelParams.State) info => collectLevelParamsInFVar ref s info.fvar) s;
pure s.params

private def addCtorFields (ref : Syntax) (fieldInfos : Array StructFieldInfo) : Nat → Expr → TermElabM Expr
| 0,   type => pure type
| i+1, type => do
  let info := fieldInfos.get! i;
  decl ← Term.getFVarLocalDecl! info.fvar;
  let type := type.abstract #[info.fvar];
  match info.kind with
  | StructFieldKind.fromParent =>
    let val := decl.value;
    addCtorFields i (type.instantiate1 val)
  | StructFieldKind.subobject =>
    let n := mkInternalSubobjectFieldName $ decl.userName;
    addCtorFields i (mkForall n decl.binderInfo decl.type type)
  | StructFieldKind.newField =>
    addCtorFields i (mkForall decl.userName decl.binderInfo decl.type type)

private def mkCtor (view : StructView) (levelParams : List Name) (params : Array Expr) (fieldInfos : Array StructFieldInfo) : TermElabM Constructor := do
let type := mkAppN (mkConst view.declName (levelParams.map mkLevelParam)) params;
type ← addCtorFields view.ref fieldInfos fieldInfos.size type;
type ← Term.mkForall view.ref params type;
type ← Term.instantiateMVars view.ref type;
let type := type.inferImplicit params.size !view.ctor.inferMod;
pure { name := view.ctor.declName, type := type }

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
    usedLevelNames ← collectLevelParamsInStructure ref scopeVars view.params fieldInfos;
    match sortDeclLevelParams view.scopeLevelNames view.allUserLevelNames usedLevelNames with
    | Except.error msg      => Term.throwError ref msg
    | Except.ok levelParams => do
      let params := scopeVars ++ view.params;
      ctor ← mkCtor view levelParams params fieldInfos;
      type ← Term.mkForall ref params type;
      type ← Term.instantiateMVars ref type;
      let indType := { name := view.declName, type := type, ctors := [ctor] : InductiveType };
      let decl    := Declaration.inductDecl levelParams params.size [indType] view.modifiers.isUnsafe;
      let projInfos := (fieldInfos.filter fun (info : StructFieldInfo) => !info.isFromParent).toList.map fun (info : StructFieldInfo) =>
        { declName := info.declName, inferMod := info.inferMod : ProjectionInfo };
      instParents ← fieldInfos.filterM fun info => do {
        decl ← Term.getFVarLocalDecl! info.fvar;
        pure (info.isSubobject && decl.binderInfo.isInstImplicit)
      };
      let projInstances := instParents.toList.map fun info => info.declName;
      mctx ← Term.getMCtx;
      lctx ← Term.getLCtx;
      localInsts ← Term.getLocalInsts;
      let fieldsWithDefault := fieldInfos.filter fun info => info.value?.isSome;
      defaultAuxDecls ← fieldsWithDefault.mapM fun info => do {
        type ← Term.inferType ref info.fvar;
        pure (info.declName ++ `_default, type, info.value?.get!)
      };
      /- The `mctx`, `lctx`, `localInsts` and `defaultAuxDecls` are used to create the auxiliary `_default` declarations *after* the structure has been declarated.
         The parameters `params` for these definitions must be marked as implicit, and all others as explicit. -/
      let lctx := params.foldl
        (fun (lctx : LocalContext) (p : Expr) =>
          lctx.updateBinderInfo p.fvarId! BinderInfo.implicit)
        lctx;
      let lctx := fieldInfos.foldl
        (fun (lctx : LocalContext) (info : StructFieldInfo) =>
          if info.isFromParent then lctx -- `fromParent` fields are elaborated as let-decls, and are zeta-expanded when creating `_default`.
          else lctx.updateBinderInfo info.fvar.fvarId! BinderInfo.default)
        lctx;
      pure { decl := decl, projInfos := projInfos, projInstances := projInstances,
             mctx := mctx, lctx := lctx, localInsts := localInsts, defaultAuxDecls := defaultAuxDecls }

@[extern "lean_mk_projections"]
private constant mkProjections (env : Environment) (structName : @& Name) (projs : @& List ProjectionInfo) (isClass : Bool) : Except String Environment := arbitrary _

private def addProjections (ref : Syntax) (structName : Name) (projs : List ProjectionInfo) (isClass : Bool) : CommandElabM Unit := do
env ← getEnv;
match mkProjections env structName projs isClass with
| Except.ok env    => setEnv env
| Except.error msg => throwError ref msg

private def mkAuxConstructions (declName : Name) : CommandElabM Unit := do
env ← getEnv;
let hasUnit := env.contains `PUnit;
let hasEq   := env.contains `Eq;
let hasHEq  := env.contains `HEq;
modifyEnv fun env => mkRecOn env declName;
when hasUnit $ modifyEnv fun env => mkCasesOn env declName;
when (hasUnit && hasEq && hasHEq) $ modifyEnv fun env => mkNoConfusion env declName

private def addDefaults (ref : Syntax) (mctx : MetavarContext) (lctx : LocalContext) (localInsts : LocalInstances)
    (defaultAuxDecls : Array (Name × Expr × Expr)) : CommandElabM Unit :=
liftTermElabM none $ Term.withLocalContext lctx localInsts do
  Term.setMCtx mctx;
  defaultAuxDecls.forM fun ⟨declName, type, value⟩ => do
    /- The identity function is used as "marker". -/
    value ← Term.liftMetaM ref $ Meta.mkId value;
    let zeta := true; -- expand `let-declarations`
    _ ← Term.mkAuxDefinition ref declName type value zeta;
    Term.modifyEnv fun env => setReducibilityStatus env declName ReducibilityStatus.reducible;
    pure ()

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
  ctor ← expandCtor stx modifiers declName;
  fields ← expandFields stx modifiers declName;
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
  let ref := declId;
  addDecl ref r.decl;
  addProjections ref declName r.projInfos isClass;
  mkAuxConstructions declName;
  applyAttributes ref declName modifiers.attrs AttributeApplicationTime.afterTypeChecking;
  r.projInstances.forM $ addInstance ref;
  addDefaults ref r.mctx r.lctx r.localInsts r.defaultAuxDecls;
  pure ()

end Command
end Elab
end Lean
