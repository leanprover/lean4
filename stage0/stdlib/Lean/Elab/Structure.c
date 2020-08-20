// Lean compiler output
// Module: Lean.Elab.Structure
// Imports: Init Lean.Elab.Command Lean.Elab.DeclModifiers Lean.Elab.DeclUtil Lean.Elab.Inductive
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
extern lean_object* l_Lean_mkHole___closed__3;
extern lean_object* l_Lean_Core_getConstInfo___closed__5;
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__collectUniversesFromFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Elab_Command_StructFieldInfo_inhabited;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__11;
lean_object* l___private_Lean_Elab_Structure_24__addCtorFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__2(lean_object*);
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__4;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInStructure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_29__mkAuxConstructions___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_19__collectUniversesFromFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__14;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l___private_Lean_Elab_Structure_13__removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__3;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__4;
lean_object* l_Lean_Elab_Command_withDeclId___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_setMCtx___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInFVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_13__removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParamAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_24__addCtorFields___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_3__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_3__expandFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInternalSubobjectFieldName(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_28__addProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__7;
lean_object* l_Lean_Elab_Term_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields(lean_object*);
lean_object* l_Lean_Elab_Term_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structExplicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_applyVisibility(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_4__validStructType___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___closed__3;
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__4;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__collectUniversesFromFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__2;
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__collectLevelParamsInStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Structure_30__addDefaults___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__12;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2;
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l___private_Lean_Elab_Structure_14__withUsed(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__10;
lean_object* l___private_Lean_Elab_Structure_10__elabFieldTypeValue___closed__1;
lean_object* l___private_Lean_Elab_Structure_9__withParents(lean_object*);
uint8_t l___private_Lean_Elab_Structure_7__containsFieldName(lean_object*, lean_object*);
lean_object* l_Lean_Level_getLevelOffset___main(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__1;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_io_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields(lean_object*);
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__5;
uint8_t l_Lean_Elab_Command_StructFieldInfo_isSubobject(lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
lean_object* l_Lean_Elab_Command_elabStructure___closed__8;
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___closed__1;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__10;
lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__7;
lean_object* l_Lean_Elab_Command_StructFieldInfo_inhabited___closed__1;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_addGlobalInstance___spec__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__15;
lean_object* l_Lean_Elab_Command_elabStructure___closed__4;
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___closed__2;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParamAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_30__addDefaults___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_projections(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkId(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Structure_1__defaultCtorName;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_Structure_14__withUsed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_io_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__1;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__4(lean_object*);
lean_object* l___private_Lean_Elab_Structure_18__levelMVarToParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux___main(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__5;
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main(lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* lean_mk_no_confusion(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__9;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__5;
uint8_t l___private_Lean_Elab_Structure_4__validStructType(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__3;
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__5;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__5;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7;
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3;
extern lean_object* l_Lean_registerClassAttr___closed__2;
lean_object* l___private_Lean_Elab_Structure_20__updateResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_updateBinderInfo(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_24__addCtorFields___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__11;
lean_object* l___private_Lean_Elab_Structure_18__levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Quotation_5__explodeHeadPat___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__5;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3;
extern lean_object* l_Lean_Parser_Level_hole___elambda__1___closed__1;
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8;
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l___private_Lean_Elab_Structure_24__addCtorFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l___private_Lean_Elab_Structure_20__updateResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__6;
lean_object* l___private_Lean_Elab_Structure_3__expandFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l___private_Lean_Elab_Command_4__mkTermState(lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6;
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse___closed__1;
lean_object* l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse___closed__2;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Structure_27__mkProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__8;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_19__collectUniversesFromFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1;
lean_object* l_Lean_Elab_Command_elabStructure___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__4;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__1;
lean_object* l_Lean_Elab_Command_Modifiers_addAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getEnv___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structInstBinder___elambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_30__addDefaults(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__6;
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_set_reducibility_status(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l___private_Lean_Elab_Structure_10__elabFieldTypeValue(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_StructFieldInfo_isFromParent(lean_object*);
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_prodToExpr___rarg___lambda__1___closed__3;
lean_object* lean_mk_rec_on(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_5__getVarDecls(lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
extern lean_object* l_Lean_Elab_Command_CtorView_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__13;
lean_object* l___private_Lean_Elab_Structure_25__mkCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setEnv(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkProjection___main___closed__7;
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__2;
uint8_t l_Lean_Elab_Command_Modifiers_isProtected(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__1;
uint8_t l_Lean_Elab_Command_Modifiers_isPrivate(lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendBefore(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__2;
lean_object* l_Lean_Expr_inferImplicit___main(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Structure_28__addProjections(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamFVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__3;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__8;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__7;
lean_object* l_Lean_Level_mkNaryMax___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_structImplicitBinder___elambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4;
lean_object* l_Lean_Meta_mkProjection___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_7__containsFieldName___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__1;
lean_object* l___private_Lean_Elab_Structure_25__mkCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__3;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__4;
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_classTk___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__6;
lean_object* l_Lean_Elab_Term_getMCtx___rarg(lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_14__withUsed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__collectLevelParamsInStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_29__mkAuxConstructions(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse___closed__3;
lean_object* _init_l_Lean_Elab_Command_StructFieldInfo_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Expr_Inhabited___closed__1;
x_4 = 0;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*4 + 1, x_5);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_StructFieldInfo_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_StructFieldInfo_inhabited___closed__1;
return x_1;
}
}
uint8_t l_Lean_Elab_Command_StructFieldInfo_isFromParent(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 1)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_StructFieldInfo_isFromParent(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_Elab_Command_StructFieldInfo_isSubobject(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
x_3 = lean_box(x_2);
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 0;
return x_5;
}
}
}
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_StructFieldInfo_isSubobject(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_prodToExpr___rarg___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_1__defaultCtorName() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'protected' constructor in a 'private' structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_2__expandCtor___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_2__expandCtor___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'private' constructor in a 'private' structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_2__expandCtor___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_2__expandCtor___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_2__expandCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(6u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = l_Lean_Syntax_isNone(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_8, x_10);
lean_dec(x_8);
x_12 = l_Lean_Syntax_getArg(x_11, x_10);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 6);
x_15 = l_Lean_Elab_replaceRef(x_11, x_14);
lean_dec(x_14);
lean_ctor_set(x_4, 6, x_15);
lean_inc(x_4);
x_16 = l_Lean_Elab_Command_elabModifiers(x_12, x_4, x_5, x_6);
lean_dec(x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_97; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_4);
x_97 = l_Lean_Elab_Command_checkValidCtorModifier(x_17, x_4, x_5, x_18);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_Lean_Elab_Command_Modifiers_isPrivate(x_17);
if (x_99 == 0)
{
x_19 = x_98;
goto block_96;
}
else
{
uint8_t x_100; 
x_100 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
if (x_100 == 0)
{
x_19 = x_98;
goto block_96;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_17);
lean_dec(x_11);
x_101 = l___private_Lean_Elab_Structure_2__expandCtor___closed__6;
x_102 = l_Lean_Elab_Command_throwError___rarg(x_101, x_4, x_5, x_98);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_102);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_11);
x_107 = !lean_is_exclusive(x_97);
if (x_107 == 0)
{
return x_97;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_97, 0);
x_109 = lean_ctor_get(x_97, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_97);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
block_96:
{
uint8_t x_20; 
x_20 = l_Lean_Elab_Command_Modifiers_isProtected(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Syntax_getArg(x_11, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
lean_dec(x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = l_Lean_Syntax_getIdAt(x_11, x_24);
lean_inc(x_25);
x_26 = l_Lean_Name_append___main(x_3, x_25);
x_27 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
x_28 = l_Lean_Elab_Command_applyVisibility(x_27, x_26, x_4, x_5, x_19);
if (x_23 == 0)
{
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = 1;
x_32 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_32, 0, x_11);
lean_ctor_set(x_32, 1, x_17);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_36, 0, x_11);
lean_ctor_set(x_36, 1, x_17);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*4, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_11);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_28, 0);
x_40 = lean_ctor_get(x_28, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_28);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_28);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_28, 0);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_45, 0, x_11);
lean_ctor_set(x_45, 1, x_17);
lean_ctor_set(x_45, 2, x_25);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_44);
lean_ctor_set(x_28, 0, x_45);
return x_28;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_28, 0);
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_28);
x_48 = 0;
x_49 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_49, 0, x_11);
lean_ctor_set(x_49, 1, x_17);
lean_ctor_set(x_49, 2, x_25);
lean_ctor_set(x_49, 3, x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_11);
x_51 = !lean_is_exclusive(x_28);
if (x_51 == 0)
{
return x_28;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
x_55 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_56 = lean_unsigned_to_nat(2u);
x_57 = l_Lean_Syntax_getArg(x_11, x_56);
x_58 = l_Lean_Syntax_isNone(x_57);
lean_dec(x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = l_Lean_Syntax_getIdAt(x_11, x_59);
lean_inc(x_60);
x_61 = l_Lean_Name_append___main(x_3, x_60);
x_62 = lean_ctor_get_uint8(x_17, sizeof(void*)*2);
x_63 = l_Lean_Elab_Command_applyVisibility(x_62, x_61, x_4, x_5, x_19);
if (x_58 == 0)
{
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = 1;
x_67 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_67, 0, x_11);
lean_ctor_set(x_67, 1, x_17);
lean_ctor_set(x_67, 2, x_60);
lean_ctor_set(x_67, 3, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*4, x_66);
lean_ctor_set(x_63, 0, x_67);
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_63);
x_70 = 1;
x_71 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_71, 0, x_11);
lean_ctor_set(x_71, 1, x_17);
lean_ctor_set(x_71, 2, x_60);
lean_ctor_set(x_71, 3, x_68);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_60);
lean_dec(x_17);
lean_dec(x_11);
x_73 = !lean_is_exclusive(x_63);
if (x_73 == 0)
{
return x_63;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_63, 0);
x_75 = lean_ctor_get(x_63, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_63);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_63);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_63, 0);
x_79 = 0;
x_80 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_80, 0, x_11);
lean_ctor_set(x_80, 1, x_17);
lean_ctor_set(x_80, 2, x_60);
lean_ctor_set(x_80, 3, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_79);
lean_ctor_set(x_63, 0, x_80);
return x_63;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_63, 0);
x_82 = lean_ctor_get(x_63, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_63);
x_83 = 0;
x_84 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_84, 0, x_11);
lean_ctor_set(x_84, 1, x_17);
lean_ctor_set(x_84, 2, x_60);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set_uint8(x_84, sizeof(void*)*4, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_60);
lean_dec(x_17);
lean_dec(x_11);
x_86 = !lean_is_exclusive(x_63);
if (x_86 == 0)
{
return x_63;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_63, 0);
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_63);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_17);
lean_dec(x_11);
x_90 = l___private_Lean_Elab_Structure_2__expandCtor___closed__3;
x_91 = l_Lean_Elab_Command_throwError___rarg(x_90, x_4, x_5, x_19);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
return x_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_91);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_4);
lean_dec(x_11);
x_111 = !lean_is_exclusive(x_16);
if (x_111 == 0)
{
return x_16;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_16, 0);
x_113 = lean_ctor_get(x_16, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_16);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_115 = lean_ctor_get(x_4, 0);
x_116 = lean_ctor_get(x_4, 1);
x_117 = lean_ctor_get(x_4, 2);
x_118 = lean_ctor_get(x_4, 3);
x_119 = lean_ctor_get(x_4, 4);
x_120 = lean_ctor_get(x_4, 5);
x_121 = lean_ctor_get(x_4, 6);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_4);
x_122 = l_Lean_Elab_replaceRef(x_11, x_121);
lean_dec(x_121);
x_123 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_123, 0, x_115);
lean_ctor_set(x_123, 1, x_116);
lean_ctor_set(x_123, 2, x_117);
lean_ctor_set(x_123, 3, x_118);
lean_ctor_set(x_123, 4, x_119);
lean_ctor_set(x_123, 5, x_120);
lean_ctor_set(x_123, 6, x_122);
lean_inc(x_123);
x_124 = l_Lean_Elab_Command_elabModifiers(x_12, x_123, x_5, x_6);
lean_dec(x_12);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_193; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_123);
x_193 = l_Lean_Elab_Command_checkValidCtorModifier(x_125, x_123, x_5, x_126);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; uint8_t x_195; 
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = l_Lean_Elab_Command_Modifiers_isPrivate(x_125);
if (x_195 == 0)
{
x_127 = x_194;
goto block_192;
}
else
{
uint8_t x_196; 
x_196 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
if (x_196 == 0)
{
x_127 = x_194;
goto block_192;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_125);
lean_dec(x_11);
x_197 = l___private_Lean_Elab_Structure_2__expandCtor___closed__6;
x_198 = l_Lean_Elab_Command_throwError___rarg(x_197, x_123, x_5, x_194);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_11);
x_203 = lean_ctor_get(x_193, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_193, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_205 = x_193;
} else {
 lean_dec_ref(x_193);
 x_205 = lean_box(0);
}
if (lean_is_scalar(x_205)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_205;
}
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_204);
return x_206;
}
block_192:
{
uint8_t x_128; 
x_128 = l_Lean_Elab_Command_Modifiers_isProtected(x_125);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_129 = lean_unsigned_to_nat(2u);
x_130 = l_Lean_Syntax_getArg(x_11, x_129);
x_131 = l_Lean_Syntax_isNone(x_130);
lean_dec(x_130);
x_132 = lean_unsigned_to_nat(1u);
x_133 = l_Lean_Syntax_getIdAt(x_11, x_132);
lean_inc(x_133);
x_134 = l_Lean_Name_append___main(x_3, x_133);
x_135 = lean_ctor_get_uint8(x_125, sizeof(void*)*2);
x_136 = l_Lean_Elab_Command_applyVisibility(x_135, x_134, x_123, x_5, x_127);
if (x_131 == 0)
{
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_139 = x_136;
} else {
 lean_dec_ref(x_136);
 x_139 = lean_box(0);
}
x_140 = 1;
x_141 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_141, 0, x_11);
lean_ctor_set(x_141, 1, x_125);
lean_ctor_set(x_141, 2, x_133);
lean_ctor_set(x_141, 3, x_137);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_140);
if (lean_is_scalar(x_139)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_139;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_138);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_133);
lean_dec(x_125);
lean_dec(x_11);
x_143 = lean_ctor_get(x_136, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_136, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_145 = x_136;
} else {
 lean_dec_ref(x_136);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_136, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_136, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_149 = x_136;
} else {
 lean_dec_ref(x_136);
 x_149 = lean_box(0);
}
x_150 = 0;
x_151 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_151, 0, x_11);
lean_ctor_set(x_151, 1, x_125);
lean_ctor_set(x_151, 2, x_133);
lean_ctor_set(x_151, 3, x_147);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_150);
if (lean_is_scalar(x_149)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_149;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_148);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_133);
lean_dec(x_125);
lean_dec(x_11);
x_153 = lean_ctor_get(x_136, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_136, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_155 = x_136;
} else {
 lean_dec_ref(x_136);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
}
else
{
uint8_t x_157; 
x_157 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; 
x_158 = lean_unsigned_to_nat(2u);
x_159 = l_Lean_Syntax_getArg(x_11, x_158);
x_160 = l_Lean_Syntax_isNone(x_159);
lean_dec(x_159);
x_161 = lean_unsigned_to_nat(1u);
x_162 = l_Lean_Syntax_getIdAt(x_11, x_161);
lean_inc(x_162);
x_163 = l_Lean_Name_append___main(x_3, x_162);
x_164 = lean_ctor_get_uint8(x_125, sizeof(void*)*2);
x_165 = l_Lean_Elab_Command_applyVisibility(x_164, x_163, x_123, x_5, x_127);
if (x_160 == 0)
{
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_169 = 1;
x_170 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_170, 0, x_11);
lean_ctor_set(x_170, 1, x_125);
lean_ctor_set(x_170, 2, x_162);
lean_ctor_set(x_170, 3, x_166);
lean_ctor_set_uint8(x_170, sizeof(void*)*4, x_169);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_168;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_167);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_162);
lean_dec(x_125);
lean_dec(x_11);
x_172 = lean_ctor_get(x_165, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_165, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_174 = x_165;
} else {
 lean_dec_ref(x_165);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_165, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_165, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_178 = x_165;
} else {
 lean_dec_ref(x_165);
 x_178 = lean_box(0);
}
x_179 = 0;
x_180 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_180, 0, x_11);
lean_ctor_set(x_180, 1, x_125);
lean_ctor_set(x_180, 2, x_162);
lean_ctor_set(x_180, 3, x_176);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_179);
if (lean_is_scalar(x_178)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_178;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_177);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_162);
lean_dec(x_125);
lean_dec(x_11);
x_182 = lean_ctor_get(x_165, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_165, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_184 = x_165;
} else {
 lean_dec_ref(x_165);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_125);
lean_dec(x_11);
x_186 = l___private_Lean_Elab_Structure_2__expandCtor___closed__3;
x_187 = l_Lean_Elab_Command_throwError___rarg(x_186, x_123, x_5, x_127);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_190 = x_187;
} else {
 lean_dec_ref(x_187);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_123);
lean_dec(x_11);
x_207 = lean_ctor_get(x_124, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_124, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_209 = x_124;
} else {
 lean_dec_ref(x_124);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(1, 2, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
return x_210;
}
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_8);
lean_dec(x_4);
x_211 = l___private_Lean_Elab_Structure_1__defaultCtorName;
x_212 = l_Lean_Name_append___main(x_3, x_211);
x_213 = l_Lean_Elab_Command_CtorView_inhabited___closed__1;
x_214 = 0;
x_215 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_215, 0, x_1);
lean_ctor_set(x_215, 1, x_213);
lean_ctor_set(x_215, 2, x_211);
lean_ctor_set(x_215, 3, x_212);
lean_ctor_set_uint8(x_215, sizeof(void*)*4, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_6);
return x_216;
}
}
}
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_2__expandCtor(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in field declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private fields are not supported yet");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'unsafe' in field declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in field declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in field declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidFieldModifier___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_26; uint8_t x_42; 
x_42 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_42 == 0)
{
x_26 = x_4;
goto block_41;
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_Elab_Command_checkValidFieldModifier___closed__15;
x_44 = l_Lean_Elab_Command_throwError___rarg(x_43, x_2, x_3, x_4);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
block_25:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Elab_Command_checkValidFieldModifier___closed__3;
x_11 = l_Lean_Elab_Command_throwError___rarg(x_10, x_2, x_3, x_5);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = l_Lean_Elab_Command_Modifiers_isPrivate(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Elab_Command_checkValidFieldModifier___closed__6;
x_20 = l_Lean_Elab_Command_throwError___rarg(x_19, x_2, x_3, x_5);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
block_41:
{
uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_28 == 0)
{
x_5 = x_26;
goto block_25;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Elab_Command_checkValidFieldModifier___closed__9;
x_30 = l_Lean_Elab_Command_throwError___rarg(x_29, x_2, x_3, x_26);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Lean_Elab_Command_checkValidFieldModifier___closed__12;
x_36 = l_Lean_Elab_Command_throwError___rarg(x_35, x_2, x_3, x_26);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidFieldModifier(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', identifiers starting with '_' are reserved to the system");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_9);
x_16 = lean_nat_dec_lt(x_10, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_array_fget(x_9, x_10);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_10, x_19);
lean_dec(x_10);
x_21 = l_Lean_Syntax_getId(x_18);
x_22 = l_Lean_isInternalSubobjectFieldName(x_21);
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
x_25 = lean_ctor_get(x_12, 2);
x_26 = lean_ctor_get(x_12, 3);
x_27 = lean_ctor_get(x_12, 4);
x_28 = lean_ctor_get(x_12, 5);
x_29 = lean_ctor_get(x_12, 6);
x_30 = l_Lean_Elab_replaceRef(x_18, x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_31 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set(x_31, 4, x_27);
lean_ctor_set(x_31, 5, x_28);
lean_ctor_set(x_31, 6, x_30);
if (x_22 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
lean_inc(x_21);
x_32 = l_Lean_Name_append___main(x_1, x_21);
x_33 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_34 = l_Lean_Elab_Command_applyVisibility(x_33, x_32, x_31, x_13, x_14);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_37 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_37, 0, x_18);
lean_ctor_set(x_37, 1, x_4);
lean_ctor_set(x_37, 2, x_35);
lean_ctor_set(x_37, 3, x_21);
lean_ctor_set(x_37, 4, x_6);
lean_ctor_set(x_37, 5, x_7);
lean_ctor_set(x_37, 6, x_8);
lean_ctor_set_uint8(x_37, sizeof(void*)*7, x_3);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 1, x_5);
x_38 = lean_array_push(x_11, x_37);
x_10 = x_20;
x_11 = x_38;
x_14 = x_36;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_34);
if (x_40 == 0)
{
return x_34;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_34, 0);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_34);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_44 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_44, 0, x_21);
x_45 = l_Lean_Meta_mkProjection___main___closed__7;
x_46 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3;
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Elab_Command_throwError___rarg(x_48, x_31, x_13, x_14);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
return x_49;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'protected' field in a 'private' structure");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'private' field in a 'private' structure");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of structure field");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_13 = lean_array_fget(x_4, x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
lean_inc(x_13);
x_25 = l_Lean_Syntax_getKind(x_13);
x_26 = l_Lean_Parser_Command_structExplicitBinder___elambda__1___closed__2;
x_27 = lean_name_eq(x_25, x_26);
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
x_30 = lean_ctor_get(x_7, 2);
x_31 = lean_ctor_get(x_7, 3);
x_32 = lean_ctor_get(x_7, 4);
x_33 = lean_ctor_get(x_7, 5);
x_34 = lean_ctor_get(x_7, 6);
x_35 = l_Lean_Elab_replaceRef(x_13, x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_36 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set(x_36, 6, x_35);
if (x_27 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = l_Lean_Parser_Command_structImplicitBinder___elambda__1___closed__2;
x_111 = lean_name_eq(x_25, x_110);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = l_Lean_Parser_Command_structInstBinder___elambda__1___closed__2;
x_113 = lean_name_eq(x_25, x_112);
lean_dec(x_25);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_13);
lean_dec(x_6);
x_114 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9;
x_115 = l_Lean_Elab_Command_throwError___rarg(x_114, x_36, x_8, x_9);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
x_16 = x_115;
goto block_24;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_115);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_16 = x_119;
goto block_24;
}
}
else
{
uint8_t x_120; 
x_120 = 3;
x_37 = x_120;
x_38 = x_9;
goto block_109;
}
}
else
{
uint8_t x_121; 
lean_dec(x_25);
x_121 = 1;
x_37 = x_121;
x_38 = x_9;
goto block_109;
}
}
else
{
uint8_t x_122; 
lean_dec(x_25);
x_122 = 0;
x_37 = x_122;
x_38 = x_9;
goto block_109;
}
block_24:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_5 = x_15;
x_6 = x_17;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_15);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
block_109:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = l_Lean_Syntax_getArg(x_13, x_39);
lean_inc(x_36);
x_41 = l_Lean_Elab_Command_elabModifiers(x_40, x_36, x_8, x_38);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_83; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_36);
x_83 = l_Lean_Elab_Command_checkValidFieldModifier(x_42, x_36, x_8, x_43);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Lean_Elab_Command_Modifiers_isPrivate(x_42);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_Lean_Elab_Command_Modifiers_isProtected(x_42);
if (x_86 == 0)
{
x_44 = x_84;
goto block_82;
}
else
{
uint8_t x_87; 
x_87 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
if (x_87 == 0)
{
x_44 = x_84;
goto block_82;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_42);
lean_dec(x_13);
lean_dec(x_6);
x_88 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3;
x_89 = l_Lean_Elab_Command_throwError___rarg(x_88, x_36, x_8, x_84);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
x_16 = x_89;
goto block_24;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
x_92 = lean_ctor_get(x_89, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_16 = x_93;
goto block_24;
}
}
}
}
else
{
uint8_t x_94; 
x_94 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
if (x_94 == 0)
{
x_44 = x_84;
goto block_82;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_42);
lean_dec(x_13);
lean_dec(x_6);
x_95 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6;
x_96 = l_Lean_Elab_Command_throwError___rarg(x_95, x_36, x_8, x_84);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
x_16 = x_96;
goto block_24;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_16 = x_100;
goto block_24;
}
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_42);
lean_dec(x_36);
lean_dec(x_13);
lean_dec(x_6);
x_101 = !lean_is_exclusive(x_83);
if (x_101 == 0)
{
x_16 = x_83;
goto block_24;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_83, 0);
x_103 = lean_ctor_get(x_83, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_83);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_16 = x_104;
goto block_24;
}
}
block_82:
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; 
x_45 = lean_unsigned_to_nat(3u);
x_46 = l_Lean_Syntax_getArg(x_13, x_45);
x_47 = l_Lean_Syntax_isNone(x_46);
lean_dec(x_46);
x_48 = 0;
x_49 = l_Lean_BinderInfo_beq(x_37, x_48);
if (x_47 == 0)
{
uint8_t x_80; 
x_80 = 1;
x_50 = x_80;
goto block_79;
}
else
{
uint8_t x_81; 
x_81 = 0;
x_50 = x_81;
goto block_79;
}
block_79:
{
lean_object* x_51; lean_object* x_52; 
if (x_49 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_unsigned_to_nat(4u);
x_69 = l_Lean_Syntax_getArg(x_13, x_68);
x_70 = l_Lean_Elab_expandDeclSig(x_69);
lean_dec(x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_51 = x_71;
x_52 = x_73;
goto block_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_unsigned_to_nat(4u);
x_75 = l_Lean_Syntax_getArg(x_13, x_74);
x_76 = l_Lean_Elab_expandOptDeclSig(x_75);
lean_dec(x_75);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_51 = x_77;
x_52 = x_78;
goto block_67;
}
block_67:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_unsigned_to_nat(2u);
x_54 = l_Lean_Syntax_getArg(x_13, x_53);
x_55 = l_Lean_Syntax_getArgs(x_54);
lean_dec(x_54);
if (x_49 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_13, x_37, x_42, x_50, x_51, x_52, x_56, x_55, x_39, x_6, x_36, x_8, x_44);
lean_dec(x_36);
lean_dec(x_55);
lean_dec(x_13);
x_16 = x_57;
goto block_24;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_unsigned_to_nat(5u);
x_59 = l_Lean_Syntax_getArg(x_13, x_58);
x_60 = l_Lean_Syntax_isNone(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = l_Lean_Syntax_getArg(x_59, x_39);
lean_dec(x_59);
x_62 = l_Lean_Syntax_getArg(x_61, x_14);
lean_dec(x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_13, x_37, x_42, x_50, x_51, x_52, x_63, x_55, x_39, x_6, x_36, x_8, x_44);
lean_dec(x_36);
lean_dec(x_55);
lean_dec(x_13);
x_16 = x_64;
goto block_24;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
x_65 = lean_box(0);
x_66 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_13, x_37, x_42, x_50, x_51, x_52, x_65, x_55, x_39, x_6, x_36, x_8, x_44);
lean_dec(x_36);
lean_dec(x_55);
lean_dec(x_13);
x_16 = x_66;
goto block_24;
}
}
}
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_36);
lean_dec(x_13);
lean_dec(x_6);
x_105 = !lean_is_exclusive(x_41);
if (x_105 == 0)
{
x_16 = x_41;
goto block_24;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_41, 0);
x_107 = lean_ctor_get(x_41, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_41);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_16 = x_108;
goto block_24;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_3__expandFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_unsigned_to_nat(7u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = l_Array_empty___closed__1;
x_13 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(x_1, x_2, x_3, x_11, x_9, x_12, x_4, x_5, x_6);
lean_dec(x_11);
return x_13;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_1, x_2, x_15, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_3__expandFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_3__expandFields(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
uint8_t l___private_Lean_Elab_Structure_4__validStructType(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
lean_object* l___private_Lean_Elab_Structure_4__validStructType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Elab_Structure_4__validStructType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_Elab_Term_getEnv___rarg(x_3);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_5);
x_10 = l_Lean_isStructure(x_8, x_5);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_6);
x_11 = l_Lean_Name_toString___closed__1;
x_12 = l_Lean_Name_toStringWithSep___main(x_11, x_5);
x_13 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Core_getConstInfo___closed__5;
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Term_throwError___rarg(x_18, x_2, x_9);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_dec(x_2);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
lean_inc(x_5);
x_26 = l_Lean_isStructure(x_24, x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = l_Lean_Name_toString___closed__1;
x_28 = l_Lean_Name_toStringWithSep___main(x_27, x_5);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_Core_getConstInfo___closed__5;
x_32 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_Term_throwError___rarg(x_34, x_2, x_25);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
if (lean_is_scalar(x_38)) {
 x_39 = lean_alloc_ctor(1, 2, 0);
} else {
 x_39 = x_38;
}
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_25);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_4);
x_41 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3;
x_42 = l_Lean_Elab_Term_throwError___rarg(x_41, x_2, x_3);
return x_42;
}
}
}
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_name_eq(x_8, x_1);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_7);
return x_13;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Elab_Structure_6__findFieldInfo_x3f(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l___private_Lean_Elab_Structure_7__containsFieldName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(x_2, x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Structure_7__containsFieldName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Elab_Structure_7__containsFieldName(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
x_12 = l_Lean_Name_append___main(x_1, x_2);
x_13 = lean_box(0);
x_14 = 1;
x_15 = 0;
x_16 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*4 + 1, x_15);
x_17 = lean_array_push(x_3, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
x_20 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(x_1, x_5, x_6, x_7, x_19, x_17, x_8, x_10, x_11);
return x_20;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("field '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' from '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_nat_dec_lt(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_apply_3(x_7, x_6, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_13 = lean_array_fget(x_4, x_5);
x_72 = l_Lean_Elab_Term_getEnv___rarg(x_9);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l___private_Lean_Elab_Structure_7__containsFieldName(x_6, x_13);
if (x_74 == 0)
{
x_14 = x_73;
goto block_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_75, 0, x_13);
x_76 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_77 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
x_78 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6;
x_79 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_80, 0, x_3);
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_83 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Elab_Term_throwError___rarg(x_83, x_8, x_73);
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
return x_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_84);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
block_71:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 4);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
x_19 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_15, 4, x_19);
lean_inc(x_13);
lean_inc(x_2);
x_20 = l_Lean_Meta_mkProjection___main(x_2, x_13, x_18, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
x_23 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_14, x_22, x_17);
lean_inc(x_8);
lean_inc(x_21);
x_24 = l_Lean_Elab_Term_inferType(x_21, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_13);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed), 11, 8);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_13);
lean_closure_set(x_27, 2, x_6);
lean_closure_set(x_27, 3, x_5);
lean_closure_set(x_27, 4, x_2);
lean_closure_set(x_27, 5, x_3);
lean_closure_set(x_27, 6, x_4);
lean_closure_set(x_27, 7, x_7);
x_28 = l_Lean_Elab_Term_withLetDecl___rarg(x_13, x_25, x_21, x_27, x_8, x_26);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
return x_24;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_8);
x_36 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_34);
x_37 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_14, x_35, x_17);
lean_ctor_set(x_20, 1, x_37);
lean_ctor_set(x_20, 0, x_36);
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
lean_inc(x_8);
x_40 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_38);
x_41 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_14, x_39, x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
x_45 = lean_ctor_get(x_15, 2);
x_46 = lean_ctor_get(x_15, 3);
x_47 = lean_ctor_get(x_15, 4);
x_48 = lean_ctor_get(x_15, 5);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_49 = lean_ctor_get(x_8, 0);
lean_inc(x_49);
x_50 = l_Lean_TraceState_Inhabited___closed__1;
x_51 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_46);
lean_ctor_set(x_51, 4, x_50);
lean_ctor_set(x_51, 5, x_48);
lean_inc(x_13);
lean_inc(x_2);
x_52 = l_Lean_Meta_mkProjection___main(x_2, x_13, x_49, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_8);
x_55 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_14, x_54, x_47);
lean_inc(x_8);
lean_inc(x_53);
x_56 = l_Lean_Elab_Term_inferType(x_53, x_8, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_13);
x_59 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed), 11, 8);
lean_closure_set(x_59, 0, x_1);
lean_closure_set(x_59, 1, x_13);
lean_closure_set(x_59, 2, x_6);
lean_closure_set(x_59, 3, x_5);
lean_closure_set(x_59, 4, x_2);
lean_closure_set(x_59, 5, x_3);
lean_closure_set(x_59, 6, x_4);
lean_closure_set(x_59, 7, x_7);
x_60 = l_Lean_Elab_Term_withLetDecl___rarg(x_13, x_57, x_53, x_59, x_8, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_53);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_63 = x_56;
} else {
 lean_dec_ref(x_56);
 x_63 = lean_box(0);
}
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_52, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_67 = x_52;
} else {
 lean_dec_ref(x_52);
 x_67 = lean_box(0);
}
lean_inc(x_8);
x_68 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_65);
x_69 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_14, x_66, x_47);
if (lean_is_scalar(x_67)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_67;
}
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_2, x_8, x_4, x_3, x_5, x_6);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_inc(x_2);
x_12 = l_Lean_Name_append___main(x_11, x_2);
x_13 = lean_box(0);
x_14 = 2;
x_15 = 0;
lean_inc(x_8);
x_16 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_8);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*4, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*4 + 1, x_15);
x_17 = lean_array_push(x_3, x_16);
lean_inc(x_5);
x_18 = l_Lean_getStructureFieldsFlattened(x_4, x_5);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1___boxed), 6, 3);
lean_closure_set(x_19, 0, x_6);
lean_closure_set(x_19, 1, x_1);
lean_closure_set(x_19, 2, x_7);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(x_11, x_8, x_5, x_18, x_20, x_17, x_19, x_9, x_10);
return x_21;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("to");
return x_1;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 7);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_apply_3(x_4, x_3, x_5, x_6);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_fget(x_7, x_2);
lean_dec(x_7);
x_12 = !lean_is_exclusive(x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_5, 9);
x_14 = l_Lean_Elab_replaceRef(x_11, x_13);
lean_dec(x_13);
lean_ctor_set(x_5, 9, x_14);
lean_inc(x_5);
lean_inc(x_11);
x_15 = l_Lean_Elab_Term_elabType(x_11, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_5);
x_18 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_16, x_5, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Name_eraseMacroScopes(x_19);
x_22 = l_Lean_Name_getString_x21(x_21);
lean_dec(x_21);
x_23 = l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
x_24 = lean_string_append(x_23, x_22);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = lean_name_mk_string(x_25, x_24);
x_27 = l___private_Lean_Elab_Structure_7__containsFieldName(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
lean_dec(x_11);
x_28 = l_Lean_Elab_Term_getEnv___rarg(x_20);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_19);
lean_inc(x_29);
lean_inc(x_26);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2), 10, 7);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_26);
lean_closure_set(x_32, 2, x_3);
lean_closure_set(x_32, 3, x_29);
lean_closure_set(x_32, 4, x_19);
lean_closure_set(x_32, 5, x_2);
lean_closure_set(x_32, 6, x_4);
if (x_31 == 0)
{
uint8_t x_33; lean_object* x_34; 
lean_dec(x_29);
lean_dec(x_19);
x_33 = 0;
x_34 = l_Lean_Elab_Term_withLocalDecl___rarg(x_26, x_33, x_16, x_32, x_5, x_30);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_is_class(x_29, x_19);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; 
x_36 = 0;
x_37 = l_Lean_Elab_Term_withLocalDecl___rarg(x_26, x_36, x_16, x_32, x_5, x_30);
return x_37;
}
else
{
uint8_t x_38; lean_object* x_39; 
x_38 = 3;
x_39 = l_Lean_Elab_Term_withLocalDecl___rarg(x_26, x_38, x_16, x_32, x_5, x_30);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_40, 0, x_26);
x_41 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Elab_Term_throwErrorAt___rarg(x_11, x_44, x_5, x_20);
lean_dec(x_11);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_18);
if (x_50 == 0)
{
return x_18;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_18, 0);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_18);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_5);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
return x_15;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_15);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_58 = lean_ctor_get(x_5, 0);
x_59 = lean_ctor_get(x_5, 1);
x_60 = lean_ctor_get(x_5, 2);
x_61 = lean_ctor_get(x_5, 3);
x_62 = lean_ctor_get(x_5, 4);
x_63 = lean_ctor_get(x_5, 5);
x_64 = lean_ctor_get(x_5, 6);
x_65 = lean_ctor_get(x_5, 7);
x_66 = lean_ctor_get(x_5, 8);
x_67 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_68 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_70 = lean_ctor_get(x_5, 9);
lean_inc(x_70);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_5);
x_71 = l_Lean_Elab_replaceRef(x_11, x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_59);
lean_ctor_set(x_72, 2, x_60);
lean_ctor_set(x_72, 3, x_61);
lean_ctor_set(x_72, 4, x_62);
lean_ctor_set(x_72, 5, x_63);
lean_ctor_set(x_72, 6, x_64);
lean_ctor_set(x_72, 7, x_65);
lean_ctor_set(x_72, 8, x_66);
lean_ctor_set(x_72, 9, x_71);
lean_ctor_set_uint8(x_72, sizeof(void*)*10, x_67);
lean_ctor_set_uint8(x_72, sizeof(void*)*10 + 1, x_68);
lean_ctor_set_uint8(x_72, sizeof(void*)*10 + 2, x_69);
lean_inc(x_72);
lean_inc(x_11);
x_73 = l_Lean_Elab_Term_elabType(x_11, x_72, x_6);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_72);
x_76 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_74, x_72, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Name_eraseMacroScopes(x_77);
x_80 = l_Lean_Name_getString_x21(x_79);
lean_dec(x_79);
x_81 = l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
x_82 = lean_string_append(x_81, x_80);
lean_dec(x_80);
x_83 = lean_box(0);
x_84 = lean_name_mk_string(x_83, x_82);
x_85 = l___private_Lean_Elab_Structure_7__containsFieldName(x_3, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
lean_dec(x_11);
x_86 = l_Lean_Elab_Term_getEnv___rarg(x_78);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_77);
lean_inc(x_87);
lean_inc(x_84);
x_90 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2), 10, 7);
lean_closure_set(x_90, 0, x_1);
lean_closure_set(x_90, 1, x_84);
lean_closure_set(x_90, 2, x_3);
lean_closure_set(x_90, 3, x_87);
lean_closure_set(x_90, 4, x_77);
lean_closure_set(x_90, 5, x_2);
lean_closure_set(x_90, 6, x_4);
if (x_89 == 0)
{
uint8_t x_91; lean_object* x_92; 
lean_dec(x_87);
lean_dec(x_77);
x_91 = 0;
x_92 = l_Lean_Elab_Term_withLocalDecl___rarg(x_84, x_91, x_74, x_90, x_72, x_88);
return x_92;
}
else
{
uint8_t x_93; 
x_93 = lean_is_class(x_87, x_77);
if (x_93 == 0)
{
uint8_t x_94; lean_object* x_95; 
x_94 = 0;
x_95 = l_Lean_Elab_Term_withLocalDecl___rarg(x_84, x_94, x_74, x_90, x_72, x_88);
return x_95;
}
else
{
uint8_t x_96; lean_object* x_97; 
x_96 = 3;
x_97 = l_Lean_Elab_Term_withLocalDecl___rarg(x_84, x_96, x_74, x_90, x_72, x_88);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_77);
lean_dec(x_74);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_98, 0, x_84);
x_99 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_100 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
x_101 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_102 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = l_Lean_Elab_Term_throwErrorAt___rarg(x_11, x_102, x_72, x_78);
lean_dec(x_11);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_106 = x_103;
} else {
 lean_dec_ref(x_103);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = lean_ctor_get(x_76, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_76, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_110 = x_76;
} else {
 lean_dec_ref(x_76);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_ctor_get(x_73, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_73, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_114 = x_73;
} else {
 lean_dec_ref(x_73);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___rarg), 6, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__elabFieldTypeValue___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_10__elabFieldTypeValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 5);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 6);
lean_inc(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = l___private_Lean_Elab_Structure_10__elabFieldTypeValue___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_box(0);
x_12 = 1;
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_elabTerm(x_10, x_11, x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Elab_Term_mkLambda(x_2, x_14, x_3, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_6, 0, x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_6);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
lean_ctor_set(x_6, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_6);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_6);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_free_object(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_13);
if (x_28 == 0)
{
return x_13;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_13, 0);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = lean_box(0);
x_34 = 1;
lean_inc(x_3);
x_35 = l_Lean_Elab_Term_elabTerm(x_32, x_33, x_34, x_3, x_4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Elab_Term_mkLambda(x_2, x_36, x_3, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
if (lean_is_scalar(x_41)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_41;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_38, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_47 = x_38;
} else {
 lean_dec_ref(x_38);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_35, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_51 = x_35;
} else {
 lean_dec_ref(x_35);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_5);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_5, 0);
lean_inc(x_3);
x_55 = l_Lean_Elab_Term_elabType(x_54, x_3, x_4);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_1, 6);
lean_inc(x_56);
lean_dec(x_1);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
lean_dec(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 0);
lean_ctor_set(x_5, 0, x_58);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_5);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_55, 0, x_60);
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
lean_ctor_set(x_5, 0, x_61);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_5);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_ctor_get(x_55, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_dec(x_55);
x_68 = !lean_is_exclusive(x_56);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_56, 0);
lean_inc(x_66);
lean_ctor_set(x_56, 0, x_66);
lean_inc(x_3);
x_70 = l_Lean_Elab_Term_elabTermEnsuringType(x_69, x_56, x_3, x_67);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_3);
lean_inc(x_2);
x_73 = l_Lean_Elab_Term_mkForall(x_2, x_66, x_3, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Elab_Term_mkLambda(x_2, x_71, x_3, x_75);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
lean_ctor_set(x_5, 0, x_74);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_76, 0, x_80);
return x_76;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_76, 0);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_76);
lean_ctor_set(x_5, 0, x_74);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_5);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_74);
lean_free_object(x_5);
x_86 = !lean_is_exclusive(x_76);
if (x_86 == 0)
{
return x_76;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_76, 0);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_76);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_71);
lean_free_object(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_90 = !lean_is_exclusive(x_73);
if (x_90 == 0)
{
return x_73;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_73, 0);
x_92 = lean_ctor_get(x_73, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_73);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_66);
lean_free_object(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_70);
if (x_94 == 0)
{
return x_70;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_70, 0);
x_96 = lean_ctor_get(x_70, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_70);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_56, 0);
lean_inc(x_98);
lean_dec(x_56);
lean_inc(x_66);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_66);
lean_inc(x_3);
x_100 = l_Lean_Elab_Term_elabTermEnsuringType(x_98, x_99, x_3, x_67);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_3);
lean_inc(x_2);
x_103 = l_Lean_Elab_Term_mkForall(x_2, x_66, x_3, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lean_Elab_Term_mkLambda(x_2, x_101, x_3, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
lean_ctor_set(x_5, 0, x_104);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_107);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_5);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_104);
lean_free_object(x_5);
x_113 = lean_ctor_get(x_106, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_106, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_115 = x_106;
} else {
 lean_dec_ref(x_106);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_101);
lean_free_object(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_ctor_get(x_103, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_103, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_119 = x_103;
} else {
 lean_dec_ref(x_103);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_66);
lean_free_object(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_121 = lean_ctor_get(x_100, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_100, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_123 = x_100;
} else {
 lean_dec_ref(x_100);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
lean_free_object(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_55);
if (x_125 == 0)
{
return x_55;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_55, 0);
x_127 = lean_ctor_get(x_55, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_55);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_5, 0);
lean_inc(x_129);
lean_dec(x_5);
lean_inc(x_3);
x_130 = l_Lean_Elab_Term_elabType(x_129, x_3, x_4);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_1, 6);
lean_inc(x_131);
lean_dec(x_1);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_3);
lean_dec(x_2);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_132);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
if (lean_is_scalar(x_134)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_134;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_133);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_130, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_130, 1);
lean_inc(x_140);
lean_dec(x_130);
x_141 = lean_ctor_get(x_131, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_142 = x_131;
} else {
 lean_dec_ref(x_131);
 x_142 = lean_box(0);
}
lean_inc(x_139);
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_139);
lean_inc(x_3);
x_144 = l_Lean_Elab_Term_elabTermEnsuringType(x_141, x_143, x_3, x_140);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_3);
lean_inc(x_2);
x_147 = l_Lean_Elab_Term_mkForall(x_2, x_139, x_3, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lean_Elab_Term_mkLambda(x_2, x_145, x_3, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_153 = x_150;
} else {
 lean_dec_ref(x_150);
 x_153 = lean_box(0);
}
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_148);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_151);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_148);
x_158 = lean_ctor_get(x_150, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_150, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_160 = x_150;
} else {
 lean_dec_ref(x_150);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_145);
lean_dec(x_3);
lean_dec(x_2);
x_162 = lean_ctor_get(x_147, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_147, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_164 = x_147;
} else {
 lean_dec_ref(x_147);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_139);
lean_dec(x_3);
lean_dec(x_2);
x_166 = lean_ctor_get(x_144, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_144, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_168 = x_144;
} else {
 lean_dec_ref(x_144);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_ctor_get(x_130, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_130, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_172 = x_130;
} else {
 lean_dec_ref(x_130);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 2);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_13 = 0;
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_8);
lean_ctor_set(x_14, 3, x_3);
lean_ctor_set_uint8(x_14, sizeof(void*)*4, x_13);
lean_ctor_set_uint8(x_14, sizeof(void*)*4 + 1, x_12);
x_15 = lean_array_push(x_4, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
x_18 = l___private_Lean_Elab_Structure_11__withFields___main___rarg(x_6, x_17, x_15, x_7, x_9, x_10);
return x_18;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field, type expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has been declared in parent structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("omit field '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' type to set default value");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_apply_3(x_4, x_3, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_array_fget(x_1, x_2);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(x_12, x_3, x_13);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 9);
x_17 = l_Lean_Elab_replaceRef(x_11, x_16);
lean_dec(x_16);
lean_dec(x_11);
lean_ctor_set(x_5, 9, x_17);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_10, 4);
lean_inc(x_18);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
lean_inc(x_10);
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__elabFieldTypeValue), 4, 1);
lean_closure_set(x_20, 0, x_10);
lean_inc(x_5);
x_21 = l_Lean_Elab_Term_elabBinders___rarg(x_19, x_20, x_5, x_6);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3;
x_27 = l_Lean_Elab_Term_throwError___rarg(x_26, x_5, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
lean_inc(x_5);
x_30 = l_Lean_Elab_Term_inferType(x_29, x_5, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_inc(x_12);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed), 10, 7);
lean_closure_set(x_34, 0, x_10);
lean_closure_set(x_34, 1, x_12);
lean_closure_set(x_34, 2, x_23);
lean_closure_set(x_34, 3, x_3);
lean_closure_set(x_34, 4, x_2);
lean_closure_set(x_34, 5, x_1);
lean_closure_set(x_34, 6, x_4);
x_35 = l_Lean_Elab_Term_withLocalDecl___rarg(x_12, x_33, x_31, x_34, x_5, x_32);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_30);
if (x_36 == 0)
{
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_21, 1);
lean_inc(x_40);
lean_dec(x_21);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_dec(x_22);
x_42 = lean_ctor_get(x_23, 0);
lean_inc(x_42);
lean_dec(x_23);
x_43 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_inc(x_12);
x_44 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed), 10, 7);
lean_closure_set(x_44, 0, x_10);
lean_closure_set(x_44, 1, x_12);
lean_closure_set(x_44, 2, x_41);
lean_closure_set(x_44, 3, x_3);
lean_closure_set(x_44, 4, x_2);
lean_closure_set(x_44, 5, x_1);
lean_closure_set(x_44, 6, x_4);
x_45 = l_Lean_Elab_Term_withLocalDecl___rarg(x_12, x_43, x_42, x_44, x_5, x_40);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_21);
if (x_46 == 0)
{
return x_21;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_21, 0);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_21);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_14);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_14, 0);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*4);
switch (x_52) {
case 0:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_14);
lean_dec(x_51);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_12);
x_54 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Term_throwError___rarg(x_57, x_5, x_6);
return x_58;
}
case 1:
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_10, 6);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_14);
lean_dec(x_51);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_60, 0, x_12);
x_61 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_62 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6;
x_64 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Elab_Term_throwError___rarg(x_64, x_5, x_6);
return x_65;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_51);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_51, 0);
x_68 = lean_ctor_get(x_51, 1);
x_69 = lean_ctor_get(x_51, 2);
x_70 = lean_ctor_get(x_51, 3);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_59);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_59, 0);
x_73 = lean_ctor_get(x_10, 4);
lean_inc(x_73);
x_74 = l_Lean_Syntax_getArgs(x_73);
lean_dec(x_73);
x_75 = l_Array_isEmpty___rarg(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_free_object(x_59);
lean_dec(x_72);
lean_free_object(x_51);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_ctor_get(x_10, 5);
lean_inc(x_76);
lean_dec(x_10);
x_77 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_77, 0, x_12);
x_78 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_79 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_81 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_82 = l_Lean_Syntax_inhabited;
x_83 = l_Option_get_x21___rarg___closed__3;
x_84 = lean_panic_fn(x_82, x_83);
x_85 = l_Lean_Elab_Term_throwErrorAt___rarg(x_84, x_81, x_5, x_6);
lean_dec(x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
return x_85;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_85);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_76, 0);
lean_inc(x_90);
lean_dec(x_76);
x_91 = l_Lean_Elab_Term_throwErrorAt___rarg(x_90, x_81, x_5, x_6);
lean_dec(x_90);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
return x_91;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_91);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_10, 5);
lean_inc(x_96);
lean_dec(x_10);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_69);
x_97 = l_Lean_Elab_Term_inferType(x_69, x_5, x_6);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_ctor_set(x_59, 0, x_98);
lean_inc(x_5);
x_100 = l_Lean_Elab_Term_elabTermEnsuringType(x_72, x_59, x_5, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_ctor_set(x_14, 0, x_101);
lean_ctor_set(x_51, 3, x_14);
x_103 = lean_array_push(x_3, x_51);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_2, x_104);
lean_dec(x_2);
x_2 = x_105;
x_3 = x_103;
x_6 = x_102;
goto _start;
}
else
{
uint8_t x_107; 
lean_free_object(x_51);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_100);
if (x_107 == 0)
{
return x_100;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_100, 0);
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_100);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_free_object(x_59);
lean_dec(x_72);
lean_free_object(x_51);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_97);
if (x_111 == 0)
{
return x_97;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_97, 0);
x_113 = lean_ctor_get(x_97, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_97);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_free_object(x_59);
lean_dec(x_72);
lean_free_object(x_51);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = lean_ctor_get(x_96, 0);
lean_inc(x_115);
lean_dec(x_96);
x_116 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_116, 0, x_12);
x_117 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_118 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_120 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Elab_Term_throwErrorAt___rarg(x_115, x_120, x_5, x_6);
lean_dec(x_115);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_121);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_59, 0);
lean_inc(x_126);
lean_dec(x_59);
x_127 = lean_ctor_get(x_10, 4);
lean_inc(x_127);
x_128 = l_Lean_Syntax_getArgs(x_127);
lean_dec(x_127);
x_129 = l_Array_isEmpty___rarg(x_128);
lean_dec(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_126);
lean_free_object(x_51);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = lean_ctor_get(x_10, 5);
lean_inc(x_130);
lean_dec(x_10);
x_131 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_131, 0, x_12);
x_132 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_133 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_135 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = l_Lean_Syntax_inhabited;
x_137 = l_Option_get_x21___rarg___closed__3;
x_138 = lean_panic_fn(x_136, x_137);
x_139 = l_Lean_Elab_Term_throwErrorAt___rarg(x_138, x_135, x_5, x_6);
lean_dec(x_138);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_130, 0);
lean_inc(x_144);
lean_dec(x_130);
x_145 = l_Lean_Elab_Term_throwErrorAt___rarg(x_144, x_135, x_5, x_6);
lean_dec(x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_10, 5);
lean_inc(x_150);
lean_dec(x_10);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_69);
x_151 = l_Lean_Elab_Term_inferType(x_69, x_5, x_6);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_152);
lean_inc(x_5);
x_155 = l_Lean_Elab_Term_elabTermEnsuringType(x_126, x_154, x_5, x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
lean_ctor_set(x_14, 0, x_156);
lean_ctor_set(x_51, 3, x_14);
x_158 = lean_array_push(x_3, x_51);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_add(x_2, x_159);
lean_dec(x_2);
x_2 = x_160;
x_3 = x_158;
x_6 = x_157;
goto _start;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_free_object(x_51);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_155, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_155, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_164 = x_155;
} else {
 lean_dec_ref(x_155);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_126);
lean_free_object(x_51);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_166 = lean_ctor_get(x_151, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_151, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_168 = x_151;
} else {
 lean_dec_ref(x_151);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_126);
lean_free_object(x_51);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_free_object(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = lean_ctor_get(x_150, 0);
lean_inc(x_170);
lean_dec(x_150);
x_171 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_171, 0, x_12);
x_172 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_173 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_171);
x_174 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_175 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_Elab_Term_throwErrorAt___rarg(x_170, x_175, x_5, x_6);
lean_dec(x_170);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_181 = lean_ctor_get(x_51, 0);
x_182 = lean_ctor_get(x_51, 1);
x_183 = lean_ctor_get(x_51, 2);
x_184 = lean_ctor_get_uint8(x_51, sizeof(void*)*4 + 1);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_51);
x_185 = lean_ctor_get(x_59, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 x_186 = x_59;
} else {
 lean_dec_ref(x_59);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_10, 4);
lean_inc(x_187);
x_188 = l_Lean_Syntax_getArgs(x_187);
lean_dec(x_187);
x_189 = l_Array_isEmpty___rarg(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_free_object(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_ctor_get(x_10, 5);
lean_inc(x_190);
lean_dec(x_10);
x_191 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_191, 0, x_12);
x_192 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_193 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
x_194 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_195 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_196 = l_Lean_Syntax_inhabited;
x_197 = l_Option_get_x21___rarg___closed__3;
x_198 = lean_panic_fn(x_196, x_197);
x_199 = l_Lean_Elab_Term_throwErrorAt___rarg(x_198, x_195, x_5, x_6);
lean_dec(x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_202 = x_199;
} else {
 lean_dec_ref(x_199);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_204 = lean_ctor_get(x_190, 0);
lean_inc(x_204);
lean_dec(x_190);
x_205 = l_Lean_Elab_Term_throwErrorAt___rarg(x_204, x_195, x_5, x_6);
lean_dec(x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_10, 5);
lean_inc(x_210);
lean_dec(x_10);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; 
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_183);
x_211 = l_Lean_Elab_Term_inferType(x_183, x_5, x_6);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
if (lean_is_scalar(x_186)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_186;
}
lean_ctor_set(x_214, 0, x_212);
lean_inc(x_5);
x_215 = l_Lean_Elab_Term_elabTermEnsuringType(x_185, x_214, x_5, x_213);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
lean_ctor_set(x_14, 0, x_216);
x_218 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_218, 0, x_181);
lean_ctor_set(x_218, 1, x_182);
lean_ctor_set(x_218, 2, x_183);
lean_ctor_set(x_218, 3, x_14);
lean_ctor_set_uint8(x_218, sizeof(void*)*4, x_52);
lean_ctor_set_uint8(x_218, sizeof(void*)*4 + 1, x_184);
x_219 = lean_array_push(x_3, x_218);
x_220 = lean_unsigned_to_nat(1u);
x_221 = lean_nat_add(x_2, x_220);
lean_dec(x_2);
x_2 = x_221;
x_3 = x_219;
x_6 = x_217;
goto _start;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_223 = lean_ctor_get(x_215, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_215, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_225 = x_215;
} else {
 lean_dec_ref(x_215);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_free_object(x_14);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_227 = lean_ctor_get(x_211, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_211, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_229 = x_211;
} else {
 lean_dec_ref(x_211);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_free_object(x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = lean_ctor_get(x_210, 0);
lean_inc(x_231);
lean_dec(x_210);
x_232 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_232, 0, x_12);
x_233 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_234 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
x_235 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_236 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lean_Elab_Term_throwErrorAt___rarg(x_231, x_236, x_5, x_6);
lean_dec(x_231);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_240 = x_237;
} else {
 lean_dec_ref(x_237);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
}
}
}
default: 
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_free_object(x_14);
lean_dec(x_51);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_242 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_243 = l_unreachable_x21___rarg(x_242);
x_244 = lean_apply_2(x_243, x_5, x_6);
return x_244;
}
}
}
else
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_14, 0);
lean_inc(x_245);
lean_dec(x_14);
x_246 = lean_ctor_get_uint8(x_245, sizeof(void*)*4);
switch (x_246) {
case 0:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_245);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_247 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_247, 0, x_12);
x_248 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_249 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_247);
x_250 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_251 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = l_Lean_Elab_Term_throwError___rarg(x_251, x_5, x_6);
return x_252;
}
case 1:
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_10, 6);
lean_inc(x_253);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_245);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_254 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_254, 0, x_12);
x_255 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_256 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_254);
x_257 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6;
x_258 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_259 = l_Lean_Elab_Term_throwError___rarg(x_258, x_5, x_6);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_260 = lean_ctor_get(x_245, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_245, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_245, 2);
lean_inc(x_262);
x_263 = lean_ctor_get_uint8(x_245, sizeof(void*)*4 + 1);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 lean_ctor_release(x_245, 2);
 lean_ctor_release(x_245, 3);
 x_264 = x_245;
} else {
 lean_dec_ref(x_245);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_253, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 x_266 = x_253;
} else {
 lean_dec_ref(x_253);
 x_266 = lean_box(0);
}
x_267 = lean_ctor_get(x_10, 4);
lean_inc(x_267);
x_268 = l_Lean_Syntax_getArgs(x_267);
lean_dec(x_267);
x_269 = l_Array_isEmpty___rarg(x_268);
lean_dec(x_268);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = lean_ctor_get(x_10, 5);
lean_inc(x_270);
lean_dec(x_10);
x_271 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_271, 0, x_12);
x_272 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_273 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_271);
x_274 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_275 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_276 = l_Lean_Syntax_inhabited;
x_277 = l_Option_get_x21___rarg___closed__3;
x_278 = lean_panic_fn(x_276, x_277);
x_279 = l_Lean_Elab_Term_throwErrorAt___rarg(x_278, x_275, x_5, x_6);
lean_dec(x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_282 = x_279;
} else {
 lean_dec_ref(x_279);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_284 = lean_ctor_get(x_270, 0);
lean_inc(x_284);
lean_dec(x_270);
x_285 = l_Lean_Elab_Term_throwErrorAt___rarg(x_284, x_275, x_5, x_6);
lean_dec(x_284);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
if (lean_is_scalar(x_288)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_288;
}
lean_ctor_set(x_289, 0, x_286);
lean_ctor_set(x_289, 1, x_287);
return x_289;
}
}
else
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_10, 5);
lean_inc(x_290);
lean_dec(x_10);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; 
lean_dec(x_12);
lean_inc(x_5);
lean_inc(x_262);
x_291 = l_Lean_Elab_Term_inferType(x_262, x_5, x_6);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
if (lean_is_scalar(x_266)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_266;
}
lean_ctor_set(x_294, 0, x_292);
lean_inc(x_5);
x_295 = l_Lean_Elab_Term_elabTermEnsuringType(x_265, x_294, x_5, x_293);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_296);
if (lean_is_scalar(x_264)) {
 x_299 = lean_alloc_ctor(0, 4, 2);
} else {
 x_299 = x_264;
}
lean_ctor_set(x_299, 0, x_260);
lean_ctor_set(x_299, 1, x_261);
lean_ctor_set(x_299, 2, x_262);
lean_ctor_set(x_299, 3, x_298);
lean_ctor_set_uint8(x_299, sizeof(void*)*4, x_246);
lean_ctor_set_uint8(x_299, sizeof(void*)*4 + 1, x_263);
x_300 = lean_array_push(x_3, x_299);
x_301 = lean_unsigned_to_nat(1u);
x_302 = lean_nat_add(x_2, x_301);
lean_dec(x_2);
x_2 = x_302;
x_3 = x_300;
x_6 = x_297;
goto _start;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_304 = lean_ctor_get(x_295, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_295, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_306 = x_295;
} else {
 lean_dec_ref(x_295);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_308 = lean_ctor_get(x_291, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_291, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_310 = x_291;
} else {
 lean_dec_ref(x_291);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_312 = lean_ctor_get(x_290, 0);
lean_inc(x_312);
lean_dec(x_290);
x_313 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_313, 0, x_12);
x_314 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_315 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
x_316 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_317 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_317, 0, x_315);
lean_ctor_set(x_317, 1, x_316);
x_318 = l_Lean_Elab_Term_throwErrorAt___rarg(x_312, x_317, x_5, x_6);
lean_dec(x_312);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_321 = x_318;
} else {
 lean_dec_ref(x_318);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_320);
return x_322;
}
}
}
}
default: 
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_245);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_323 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_324 = l_unreachable_x21___rarg(x_323);
x_325 = lean_apply_2(x_324, x_5, x_6);
return x_325;
}
}
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; uint8_t x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_326 = lean_ctor_get(x_5, 0);
x_327 = lean_ctor_get(x_5, 1);
x_328 = lean_ctor_get(x_5, 2);
x_329 = lean_ctor_get(x_5, 3);
x_330 = lean_ctor_get(x_5, 4);
x_331 = lean_ctor_get(x_5, 5);
x_332 = lean_ctor_get(x_5, 6);
x_333 = lean_ctor_get(x_5, 7);
x_334 = lean_ctor_get(x_5, 8);
x_335 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_336 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_337 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_338 = lean_ctor_get(x_5, 9);
lean_inc(x_338);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_5);
x_339 = l_Lean_Elab_replaceRef(x_11, x_338);
lean_dec(x_338);
lean_dec(x_11);
x_340 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_340, 0, x_326);
lean_ctor_set(x_340, 1, x_327);
lean_ctor_set(x_340, 2, x_328);
lean_ctor_set(x_340, 3, x_329);
lean_ctor_set(x_340, 4, x_330);
lean_ctor_set(x_340, 5, x_331);
lean_ctor_set(x_340, 6, x_332);
lean_ctor_set(x_340, 7, x_333);
lean_ctor_set(x_340, 8, x_334);
lean_ctor_set(x_340, 9, x_339);
lean_ctor_set_uint8(x_340, sizeof(void*)*10, x_335);
lean_ctor_set_uint8(x_340, sizeof(void*)*10 + 1, x_336);
lean_ctor_set_uint8(x_340, sizeof(void*)*10 + 2, x_337);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_341 = lean_ctor_get(x_10, 4);
lean_inc(x_341);
x_342 = l_Lean_Syntax_getArgs(x_341);
lean_dec(x_341);
lean_inc(x_10);
x_343 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__elabFieldTypeValue), 4, 1);
lean_closure_set(x_343, 0, x_10);
lean_inc(x_340);
x_344 = l_Lean_Elab_Term_elabBinders___rarg(x_342, x_343, x_340, x_6);
lean_dec(x_342);
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_345; lean_object* x_346; 
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; 
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_348 = lean_ctor_get(x_344, 1);
lean_inc(x_348);
lean_dec(x_344);
x_349 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3;
x_350 = l_Lean_Elab_Term_throwError___rarg(x_349, x_340, x_348);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_344, 1);
lean_inc(x_351);
lean_dec(x_344);
x_352 = lean_ctor_get(x_347, 0);
lean_inc(x_352);
lean_dec(x_347);
lean_inc(x_340);
x_353 = l_Lean_Elab_Term_inferType(x_352, x_340, x_351);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; lean_object* x_358; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_inc(x_12);
x_357 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed), 10, 7);
lean_closure_set(x_357, 0, x_10);
lean_closure_set(x_357, 1, x_12);
lean_closure_set(x_357, 2, x_346);
lean_closure_set(x_357, 3, x_3);
lean_closure_set(x_357, 4, x_2);
lean_closure_set(x_357, 5, x_1);
lean_closure_set(x_357, 6, x_4);
x_358 = l_Lean_Elab_Term_withLocalDecl___rarg(x_12, x_356, x_354, x_357, x_340, x_355);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_340);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_359 = lean_ctor_get(x_353, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_353, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_361 = x_353;
} else {
 lean_dec_ref(x_353);
 x_361 = lean_box(0);
}
if (lean_is_scalar(x_361)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_361;
}
lean_ctor_set(x_362, 0, x_359);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_ctor_get(x_344, 1);
lean_inc(x_363);
lean_dec(x_344);
x_364 = lean_ctor_get(x_345, 1);
lean_inc(x_364);
lean_dec(x_345);
x_365 = lean_ctor_get(x_346, 0);
lean_inc(x_365);
lean_dec(x_346);
x_366 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_inc(x_12);
x_367 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed), 10, 7);
lean_closure_set(x_367, 0, x_10);
lean_closure_set(x_367, 1, x_12);
lean_closure_set(x_367, 2, x_364);
lean_closure_set(x_367, 3, x_3);
lean_closure_set(x_367, 4, x_2);
lean_closure_set(x_367, 5, x_1);
lean_closure_set(x_367, 6, x_4);
x_368 = l_Lean_Elab_Term_withLocalDecl___rarg(x_12, x_366, x_365, x_367, x_340, x_363);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_340);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_369 = lean_ctor_get(x_344, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_344, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 x_371 = x_344;
} else {
 lean_dec_ref(x_344);
 x_371 = lean_box(0);
}
if (lean_is_scalar(x_371)) {
 x_372 = lean_alloc_ctor(1, 2, 0);
} else {
 x_372 = x_371;
}
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_370);
return x_372;
}
}
else
{
lean_object* x_373; lean_object* x_374; uint8_t x_375; 
x_373 = lean_ctor_get(x_14, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_374 = x_14;
} else {
 lean_dec_ref(x_14);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get_uint8(x_373, sizeof(void*)*4);
switch (x_375) {
case 0:
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_376 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_376, 0, x_12);
x_377 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_378 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_380 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = l_Lean_Elab_Term_throwError___rarg(x_380, x_340, x_6);
return x_381;
}
case 1:
{
lean_object* x_382; 
x_382 = lean_ctor_get(x_10, 6);
lean_inc(x_382);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_383 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_383, 0, x_12);
x_384 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_385 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6;
x_387 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = l_Lean_Elab_Term_throwError___rarg(x_387, x_340, x_6);
return x_388;
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_389 = lean_ctor_get(x_373, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_373, 1);
lean_inc(x_390);
x_391 = lean_ctor_get(x_373, 2);
lean_inc(x_391);
x_392 = lean_ctor_get_uint8(x_373, sizeof(void*)*4 + 1);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 lean_ctor_release(x_373, 2);
 lean_ctor_release(x_373, 3);
 x_393 = x_373;
} else {
 lean_dec_ref(x_373);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_382, 0);
lean_inc(x_394);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 x_395 = x_382;
} else {
 lean_dec_ref(x_382);
 x_395 = lean_box(0);
}
x_396 = lean_ctor_get(x_10, 4);
lean_inc(x_396);
x_397 = l_Lean_Syntax_getArgs(x_396);
lean_dec(x_396);
x_398 = l_Array_isEmpty___rarg(x_397);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_374);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_399 = lean_ctor_get(x_10, 5);
lean_inc(x_399);
lean_dec(x_10);
x_400 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_400, 0, x_12);
x_401 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_402 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_400);
x_403 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_404 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_405 = l_Lean_Syntax_inhabited;
x_406 = l_Option_get_x21___rarg___closed__3;
x_407 = lean_panic_fn(x_405, x_406);
x_408 = l_Lean_Elab_Term_throwErrorAt___rarg(x_407, x_404, x_340, x_6);
lean_dec(x_407);
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_411 = x_408;
} else {
 lean_dec_ref(x_408);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_410);
return x_412;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_413 = lean_ctor_get(x_399, 0);
lean_inc(x_413);
lean_dec(x_399);
x_414 = l_Lean_Elab_Term_throwErrorAt___rarg(x_413, x_404, x_340, x_6);
lean_dec(x_413);
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_414, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_417 = x_414;
} else {
 lean_dec_ref(x_414);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
return x_418;
}
}
else
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_10, 5);
lean_inc(x_419);
lean_dec(x_10);
if (lean_obj_tag(x_419) == 0)
{
lean_object* x_420; 
lean_dec(x_12);
lean_inc(x_340);
lean_inc(x_391);
x_420 = l_Lean_Elab_Term_inferType(x_391, x_340, x_6);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
if (lean_is_scalar(x_395)) {
 x_423 = lean_alloc_ctor(1, 1, 0);
} else {
 x_423 = x_395;
}
lean_ctor_set(x_423, 0, x_421);
lean_inc(x_340);
x_424 = l_Lean_Elab_Term_elabTermEnsuringType(x_394, x_423, x_340, x_422);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
if (lean_is_scalar(x_374)) {
 x_427 = lean_alloc_ctor(1, 1, 0);
} else {
 x_427 = x_374;
}
lean_ctor_set(x_427, 0, x_425);
if (lean_is_scalar(x_393)) {
 x_428 = lean_alloc_ctor(0, 4, 2);
} else {
 x_428 = x_393;
}
lean_ctor_set(x_428, 0, x_389);
lean_ctor_set(x_428, 1, x_390);
lean_ctor_set(x_428, 2, x_391);
lean_ctor_set(x_428, 3, x_427);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_375);
lean_ctor_set_uint8(x_428, sizeof(void*)*4 + 1, x_392);
x_429 = lean_array_push(x_3, x_428);
x_430 = lean_unsigned_to_nat(1u);
x_431 = lean_nat_add(x_2, x_430);
lean_dec(x_2);
x_2 = x_431;
x_3 = x_429;
x_5 = x_340;
x_6 = x_426;
goto _start;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_374);
lean_dec(x_340);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_433 = lean_ctor_get(x_424, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_424, 1);
lean_inc(x_434);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 x_435 = x_424;
} else {
 lean_dec_ref(x_424);
 x_435 = lean_box(0);
}
if (lean_is_scalar(x_435)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_435;
}
lean_ctor_set(x_436, 0, x_433);
lean_ctor_set(x_436, 1, x_434);
return x_436;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_374);
lean_dec(x_340);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_437 = lean_ctor_get(x_420, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_420, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_439 = x_420;
} else {
 lean_dec_ref(x_420);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_437);
lean_ctor_set(x_440, 1, x_438);
return x_440;
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_395);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_374);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_441 = lean_ctor_get(x_419, 0);
lean_inc(x_441);
lean_dec(x_419);
x_442 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_442, 0, x_12);
x_443 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_444 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_442);
x_445 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_446 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
x_447 = l_Lean_Elab_Term_throwErrorAt___rarg(x_441, x_446, x_340, x_6);
lean_dec(x_441);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_450 = x_447;
} else {
 lean_dec_ref(x_447);
 x_450 = lean_box(0);
}
if (lean_is_scalar(x_450)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_450;
}
lean_ctor_set(x_451, 0, x_448);
lean_ctor_set(x_451, 1, x_449);
return x_451;
}
}
}
}
default: 
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_452 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_453 = l_unreachable_x21___rarg(x_452);
x_454 = lean_apply_2(x_453, x_340, x_6);
return x_454;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_11__withFields___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___rarg), 6, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_12__getResultUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected structure resulting type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_12__getResultUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_12__getResultUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_12__getResultUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_12__getResultUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Term_whnf(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 3)
{
uint8_t x_6; 
lean_dec(x_2);
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l___private_Lean_Elab_Structure_12__getResultUniverse___closed__3;
x_14 = l_Lean_Elab_Term_throwError___rarg(x_13, x_2, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_4);
if (x_15 == 0)
{
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_5);
x_13 = l_Lean_Elab_Term_inferType(x_10, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_collectUsedFVars(x_4, x_14, x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_3 = x_12;
x_4 = x_17;
x_6 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_inferType(x_13, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
x_17 = l_Lean_Elab_Term_collectUsedFVars(x_4, x_15, x_5, x_16);
x_18 = lean_ctor_get(x_10, 3);
lean_inc(x_18);
lean_dec(x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_3 = x_12;
x_4 = x_19;
x_6 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
lean_inc(x_5);
x_25 = l_Lean_Elab_Term_collectUsedFVars(x_22, x_24, x_5, x_23);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_3 = x_12;
x_4 = x_26;
x_6 = x_27;
goto _start;
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_13__removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_inc(x_4);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__1(x_2, x_2, x_6, x_7, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_4);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__2(x_3, x_3, x_6, x_9, x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_removeUnused(x_1, x_12, x_4, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_13__removeUnused___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_13__removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_13__removeUnused(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_14__withUsed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l___private_Lean_Elab_Structure_13__removeUnused(x_1, x_2, x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_dec(x_16);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 2);
lean_dec(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_dec(x_19);
lean_ctor_set(x_10, 2, x_13);
lean_ctor_set(x_10, 1, x_12);
x_20 = lean_apply_3(x_4, x_14, x_5, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 3);
x_23 = lean_ctor_get(x_10, 4);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_12);
lean_ctor_set(x_24, 2, x_13);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
lean_ctor_set(x_5, 0, x_24);
x_25 = lean_apply_3(x_4, x_14, x_5, x_11);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_5, 1);
x_27 = lean_ctor_get(x_5, 2);
x_28 = lean_ctor_get(x_5, 3);
x_29 = lean_ctor_get(x_5, 4);
x_30 = lean_ctor_get(x_5, 5);
x_31 = lean_ctor_get(x_5, 6);
x_32 = lean_ctor_get(x_5, 7);
x_33 = lean_ctor_get(x_5, 8);
x_34 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_37 = lean_ctor_get(x_5, 9);
lean_inc(x_37);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_10, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_10, 4);
lean_inc(x_40);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_41 = x_10;
} else {
 lean_dec_ref(x_10);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 5, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_12);
lean_ctor_set(x_42, 2, x_13);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_40);
x_43 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_26);
lean_ctor_set(x_43, 2, x_27);
lean_ctor_set(x_43, 3, x_28);
lean_ctor_set(x_43, 4, x_29);
lean_ctor_set(x_43, 5, x_30);
lean_ctor_set(x_43, 6, x_31);
lean_ctor_set(x_43, 7, x_32);
lean_ctor_set(x_43, 8, x_33);
lean_ctor_set(x_43, 9, x_37);
lean_ctor_set_uint8(x_43, sizeof(void*)*10, x_34);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 1, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 2, x_36);
x_44 = lean_apply_3(x_4, x_14, x_43, x_11);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_14__withUsed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_14__withUsed___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_14__withUsed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_14__withUsed___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_levelMVarToParam_x27(x_6, x_2, x_3, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_8, 0, x_16);
return x_8;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = lean_box(0);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_1, x_2);
lean_inc(x_4);
x_12 = l___private_Lean_Elab_Structure_15__levelMVarToParamFVar(x_11, x_3, x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_15;
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_4);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamFVars___spec__1(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamFVars___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_16__levelMVarToParamFVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_11 = lean_array_fget(x_2, x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fset(x_2, x_1, x_12);
x_14 = x_11;
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*4);
x_19 = lean_ctor_get_uint8(x_14, sizeof(void*)*4 + 1);
x_20 = lean_ctor_get(x_14, 3);
lean_inc(x_20);
lean_inc(x_4);
lean_inc(x_17);
x_21 = l___private_Lean_Elab_Structure_15__levelMVarToParamFVar(x_17, x_3, x_4, x_5);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
x_27 = x_14;
x_28 = lean_array_fset(x_13, x_1, x_27);
lean_dec(x_1);
x_1 = x_26;
x_2 = x_28;
x_3 = x_24;
x_5 = x_23;
goto _start;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_14);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_14, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_14, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_14, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_14, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_20, 0);
lean_inc(x_4);
x_39 = l_Lean_Elab_Term_levelMVarToParam_x27(x_38, x_36, x_4, x_35);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
lean_ctor_set(x_20, 0, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_1, x_44);
x_46 = x_14;
x_47 = lean_array_fset(x_13, x_1, x_46);
lean_dec(x_1);
x_1 = x_45;
x_2 = x_47;
x_3 = x_43;
x_5 = x_41;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_ctor_get(x_20, 0);
lean_inc(x_49);
lean_dec(x_20);
lean_inc(x_4);
x_50 = l_Lean_Elab_Term_levelMVarToParam_x27(x_49, x_36, x_4, x_35);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_14, 3, x_55);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_1, x_56);
x_58 = x_14;
x_59 = lean_array_fset(x_13, x_1, x_58);
lean_dec(x_1);
x_1 = x_57;
x_2 = x_59;
x_3 = x_54;
x_5 = x_52;
goto _start;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_14);
x_61 = lean_ctor_get(x_21, 1);
lean_inc(x_61);
lean_dec(x_21);
x_62 = lean_ctor_get(x_22, 1);
lean_inc(x_62);
lean_dec(x_22);
x_63 = lean_ctor_get(x_20, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_64 = x_20;
} else {
 lean_dec_ref(x_20);
 x_64 = lean_box(0);
}
lean_inc(x_4);
x_65 = l_Lean_Elab_Term_levelMVarToParam_x27(x_63, x_62, x_4, x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
if (lean_is_scalar(x_64)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_64;
}
lean_ctor_set(x_70, 0, x_68);
x_71 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_71, 0, x_15);
lean_ctor_set(x_71, 1, x_16);
lean_ctor_set(x_71, 2, x_17);
lean_ctor_set(x_71, 3, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*4, x_18);
lean_ctor_set_uint8(x_71, sizeof(void*)*4 + 1, x_19);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_add(x_1, x_72);
x_74 = x_71;
x_75 = lean_array_fset(x_13, x_1, x_74);
lean_dec(x_1);
x_1 = x_73;
x_2 = x_75;
x_3 = x_69;
x_5 = x_67;
goto _start;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_21);
if (x_77 == 0)
{
return x_21;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_21, 0);
x_79 = lean_ctor_get(x_21, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_21);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_8 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamFVars___spec__1(x_1, x_7, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
x_12 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamFVars___spec__1(x_2, x_7, x_11, x_5, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = x_3;
x_17 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamAux___spec__1), 5, 2);
lean_closure_set(x_17, 0, x_7);
lean_closure_set(x_17, 1, x_16);
x_18 = x_17;
x_19 = lean_apply_3(x_18, x_15, x_5, x_14);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_17__levelMVarToParamAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_18__levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l___private_Lean_Elab_Structure_17__levelMVarToParamAux(x_1, x_2, x_3, x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_10);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_7);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_18__levelMVarToParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_18__levelMVarToParam(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_19__collectUniversesFromFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_7);
x_16 = l_Lean_Elab_Term_inferType(x_15, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
x_19 = l_Lean_Elab_Term_getLevel(x_17, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_7);
x_22 = l_Lean_Elab_Term_instantiateLevelMVars(x_20, x_7, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_2);
x_25 = l_Lean_Elab_Command_accLevelAtCtor___main(x_23, x_1, x_2, x_6);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_14);
lean_dec(x_2);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_Elab_Term_throwError___rarg(x_28, x_7, x_24);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_5 = x_14;
x_6 = x_34;
x_8 = x_24;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_19, 0);
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_16);
if (x_40 == 0)
{
return x_16;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_19__collectUniversesFromFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_empty___closed__1;
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_19__collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_3, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_19__collectUniversesFromFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_19__collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Structure_19__collectUniversesFromFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_19__collectUniversesFromFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compute resulting universe level of structure, provide universe explicitly");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_20__updateResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l___private_Lean_Elab_Structure_12__getResultUniverse(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Level_getOffsetAux___main(x_6, x_8);
x_10 = l_Lean_Level_getLevelOffset___main(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_inc(x_3);
x_12 = l___private_Lean_Elab_Structure_19__collectUniversesFromFields(x_10, x_9, x_1, x_3, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_toList___rarg(x_13);
lean_dec(x_13);
x_16 = l_Lean_Level_mkNaryMax___main(x_15);
x_17 = l_Lean_Elab_Term_assignLevelMVar(x_11, x_16, x_3, x_14);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Elab_Term_instantiateMVars(x_2, x_3, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_24 = l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__3;
x_25 = l_Lean_Elab_Term_throwError___rarg(x_24, x_3, x_7);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
return x_5;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 0);
x_28 = lean_ctor_get(x_5, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_5);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_20__updateResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_20__updateResultingUniverse(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_inferType(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_instantiateMVars(x_6, x_3, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_CollectLevelParams_main___main(x_10, x_1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Lean_CollectLevelParams_main___main(x_12, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_5);
x_13 = l___private_Lean_Elab_Structure_21__collectLevelParamsInFVar(x_4, x_10, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_3 = x_12;
x_4 = x_14;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___spec__1(x_1, x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_22__collectLevelParamsInFVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInStructure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 2);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_5);
x_14 = l___private_Lean_Elab_Structure_21__collectLevelParamsInFVar(x_4, x_13, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_3 = x_12;
x_4 = x_15;
x_6 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_12);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_23__collectLevelParamsInStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Elab_Command_mkDef___lambda__1___closed__1;
lean_inc(x_4);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___spec__1(x_1, x_1, x_6, x_7, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_4);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInFVars___spec__1(x_2, x_2, x_6, x_9, x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInStructure___spec__1(x_3, x_3, x_6, x_12, x_4, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_11);
if (x_26 == 0)
{
return x_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_11, 0);
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_8);
if (x_30 == 0)
{
return x_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_8, 0);
x_32 = lean_ctor_get(x_8, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_8);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInStructure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInStructure___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_23__collectLevelParamsInStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_23__collectLevelParamsInStructure(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_24__addCtorFields___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_10 = l_Lean_Elab_Command_StructFieldInfo_inhabited;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_inc(x_4);
x_13 = l_Lean_Elab_Term_getFVarLocalDecl_x21(x_12, x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_4);
x_16 = l_Lean_Elab_Term_instantiateMVars(x_3, x_4, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_mkOptionalNode___closed__2;
x_20 = lean_array_push(x_19, x_12);
x_21 = lean_expr_abstract(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
x_22 = lean_ctor_get_uint8(x_11, sizeof(void*)*4);
lean_dec(x_11);
switch (x_22) {
case 0:
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_LocalDecl_userName(x_14);
x_24 = l_Lean_LocalDecl_binderInfo(x_14);
x_25 = l_Lean_LocalDecl_type(x_14);
lean_dec(x_14);
x_26 = l_Lean_mkForall(x_23, x_24, x_25, x_21);
lean_dec(x_23);
x_2 = x_9;
x_3 = x_26;
x_5 = x_18;
goto _start;
}
case 1:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_LocalDecl_value(x_14);
lean_dec(x_14);
x_29 = lean_expr_instantiate1(x_21, x_28);
lean_dec(x_28);
lean_dec(x_21);
x_2 = x_9;
x_3 = x_29;
x_5 = x_18;
goto _start;
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_31 = l_Lean_LocalDecl_userName(x_14);
x_32 = l_Lean_mkHole___closed__3;
x_33 = l_Lean_Name_appendBefore(x_31, x_32);
x_34 = l_Lean_LocalDecl_binderInfo(x_14);
x_35 = l_Lean_LocalDecl_type(x_14);
lean_dec(x_14);
x_36 = l_Lean_mkForall(x_33, x_34, x_35, x_21);
lean_dec(x_33);
x_2 = x_9;
x_3 = x_36;
x_5 = x_18;
goto _start;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_13);
if (x_38 == 0)
{
return x_13;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_13, 0);
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_13);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_4);
lean_dec(x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_5);
return x_42;
}
}
}
lean_object* l___private_Lean_Elab_Structure_24__addCtorFields___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_24__addCtorFields___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_24__addCtorFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_24__addCtorFields___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_24__addCtorFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_24__addCtorFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_25__mkCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = l_List_map___main___at_Lean_Meta_addGlobalInstance___spec__1(x_2);
x_10 = l_Lean_mkConst(x_8, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_11, x_10);
x_13 = lean_array_get_size(x_4);
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 9);
x_16 = l_Lean_Elab_replaceRef(x_7, x_15);
lean_dec(x_15);
lean_dec(x_7);
lean_ctor_set(x_5, 9, x_16);
lean_inc(x_5);
x_17 = l___private_Lean_Elab_Structure_24__addCtorFields___main(x_4, x_13, x_12, x_5, x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_3);
x_20 = l_Lean_Elab_Term_mkForall(x_3, x_18, x_5, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Term_instantiateMVars(x_21, x_5, x_22);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_array_get_size(x_3);
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 9);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*4);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 3);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = l_Lean_Expr_inferImplicit___main(x_25, x_26, x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_23, 0, x_32);
return x_23;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 3);
lean_inc(x_33);
lean_dec(x_27);
x_34 = 0;
x_35 = l_Lean_Expr_inferImplicit___main(x_25, x_26, x_34);
lean_dec(x_26);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_23, 0, x_36);
return x_23;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_array_get_size(x_3);
lean_dec(x_3);
x_40 = lean_ctor_get(x_1, 9);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*4);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_40, 3);
lean_inc(x_42);
lean_dec(x_40);
x_43 = 1;
x_44 = l_Lean_Expr_inferImplicit___main(x_37, x_39, x_43);
lean_dec(x_39);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_38);
return x_46;
}
else
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_40, 3);
lean_inc(x_47);
lean_dec(x_40);
x_48 = 0;
x_49 = l_Lean_Expr_inferImplicit___main(x_37, x_39, x_48);
lean_dec(x_39);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_38);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_20);
if (x_52 == 0)
{
return x_20;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_20, 0);
x_54 = lean_ctor_get(x_20, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_20);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_17);
if (x_56 == 0)
{
return x_17;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_17, 0);
x_58 = lean_ctor_get(x_17, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_17);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_60 = lean_ctor_get(x_5, 0);
x_61 = lean_ctor_get(x_5, 1);
x_62 = lean_ctor_get(x_5, 2);
x_63 = lean_ctor_get(x_5, 3);
x_64 = lean_ctor_get(x_5, 4);
x_65 = lean_ctor_get(x_5, 5);
x_66 = lean_ctor_get(x_5, 6);
x_67 = lean_ctor_get(x_5, 7);
x_68 = lean_ctor_get(x_5, 8);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_70 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_71 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
x_72 = lean_ctor_get(x_5, 9);
lean_inc(x_72);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_5);
x_73 = l_Lean_Elab_replaceRef(x_7, x_72);
lean_dec(x_72);
lean_dec(x_7);
x_74 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_74, 0, x_60);
lean_ctor_set(x_74, 1, x_61);
lean_ctor_set(x_74, 2, x_62);
lean_ctor_set(x_74, 3, x_63);
lean_ctor_set(x_74, 4, x_64);
lean_ctor_set(x_74, 5, x_65);
lean_ctor_set(x_74, 6, x_66);
lean_ctor_set(x_74, 7, x_67);
lean_ctor_set(x_74, 8, x_68);
lean_ctor_set(x_74, 9, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*10, x_69);
lean_ctor_set_uint8(x_74, sizeof(void*)*10 + 1, x_70);
lean_ctor_set_uint8(x_74, sizeof(void*)*10 + 2, x_71);
lean_inc(x_74);
x_75 = l___private_Lean_Elab_Structure_24__addCtorFields___main(x_4, x_13, x_12, x_74, x_6);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_74);
lean_inc(x_3);
x_78 = l_Lean_Elab_Term_mkForall(x_3, x_76, x_74, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Elab_Term_instantiateMVars(x_79, x_74, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_array_get_size(x_3);
lean_dec(x_3);
x_86 = lean_ctor_get(x_1, 9);
lean_inc(x_86);
lean_dec(x_1);
x_87 = lean_ctor_get_uint8(x_86, sizeof(void*)*4);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_86, 3);
lean_inc(x_88);
lean_dec(x_86);
x_89 = 1;
x_90 = l_Lean_Expr_inferImplicit___main(x_82, x_85, x_89);
lean_dec(x_85);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
if (lean_is_scalar(x_84)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_84;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_83);
return x_92;
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_86, 3);
lean_inc(x_93);
lean_dec(x_86);
x_94 = 0;
x_95 = l_Lean_Expr_inferImplicit___main(x_82, x_85, x_94);
lean_dec(x_85);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
if (lean_is_scalar(x_84)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_84;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_83);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_74);
lean_dec(x_3);
lean_dec(x_1);
x_98 = lean_ctor_get(x_78, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_78, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_100 = x_78;
} else {
 lean_dec_ref(x_78);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_74);
lean_dec(x_3);
lean_dec(x_1);
x_102 = lean_ctor_get(x_75, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_75, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_104 = x_75;
} else {
 lean_dec_ref(x_75);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_25__mkCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_25__mkCtor(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = l_Lean_Elab_Command_StructFieldInfo_isFromParent(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_array_fswap(x_1, x_2, x_3);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_1 = x_14;
x_2 = x_16;
x_3 = x_17;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*4 + 1);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_7);
x_9 = l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__2(x_5);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_8);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*4 + 1);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__2(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_filterMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_array_fget(x_1, x_2);
x_27 = lean_ctor_get(x_26, 2);
lean_inc(x_27);
lean_inc(x_4);
x_28 = l_Lean_Elab_Term_getFVarLocalDecl_x21(x_27, x_4, x_5);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_Elab_Command_StructFieldInfo_isSubobject(x_26);
lean_dec(x_26);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_29);
x_32 = 0;
x_10 = x_32;
x_11 = x_30;
goto block_25;
}
else
{
uint8_t x_33; uint8_t x_34; 
x_33 = l_Lean_LocalDecl_binderInfo(x_29);
lean_dec(x_29);
x_34 = l_Lean_BinderInfo_isInstImplicit(x_33);
x_10 = x_34;
x_11 = x_30;
goto block_25;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
block_25:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
x_5 = x_11;
goto _start;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_18 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_2 = x_17;
x_3 = x_18;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_array_fswap(x_1, x_2, x_3);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_23 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_1 = x_20;
x_2 = x_22;
x_3 = x_23;
x_5 = x_11;
goto _start;
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__4(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__4(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__4(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_array_fget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = lean_nat_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
lean_dec(x_2);
x_15 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_fswap(x_1, x_2, x_3);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_20 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_1 = x_17;
x_2 = x_19;
x_3 = x_20;
goto _start;
}
}
}
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_default");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = x_2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
x_13 = lean_ctor_get(x_12, 2);
lean_inc(x_13);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_inferType(x_13, x_3, x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__2;
x_19 = l_Lean_Name_append___main(x_17, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_12, 3);
lean_inc(x_20);
lean_dec(x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = l_Lean_Expr_Inhabited;
x_22 = l_Option_get_x21___rarg___closed__3;
x_23 = lean_panic_fn(x_21, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_1, x_26);
x_28 = x_25;
x_29 = lean_array_fset(x_11, x_1, x_28);
lean_dec(x_1);
x_1 = x_27;
x_2 = x_29;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_19);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_1, x_34);
x_36 = x_33;
x_37 = lean_array_fset(x_11, x_1, x_36);
lean_dec(x_1);
x_1 = x_35;
x_2 = x_37;
x_4 = x_16;
goto _start;
}
}
else
{
uint8_t x_39; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = l_Lean_LocalContext_updateBinderInfo(x_5, x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_Elab_Command_StructFieldInfo_isFromParent(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
if (x_8 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 2);
lean_inc(x_11);
lean_dec(x_7);
x_12 = l_Lean_Expr_fvarId_x21(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Lean_LocalContext_updateBinderInfo(x_4, x_12, x_13);
x_3 = x_10;
x_4 = x_14;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_10;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
x_9 = l___private_Lean_Elab_Structure_18__levelMVarToParam(x_6, x_1, x_2, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
if (x_4 == 0)
{
x_12 = x_5;
x_13 = x_11;
goto block_98;
}
else
{
lean_object* x_99; 
lean_inc(x_7);
x_99 = l___private_Lean_Elab_Structure_20__updateResultingUniverse(x_10, x_5, x_7, x_11);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_12 = x_100;
x_13 = x_101;
goto block_98;
}
else
{
uint8_t x_102; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_99);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
block_98:
{
lean_object* x_14; 
lean_inc(x_7);
x_14 = l___private_Lean_Elab_Structure_23__collectLevelParamsInStructure(x_6, x_1, x_10, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 3);
lean_inc(x_18);
x_19 = l_Lean_Elab_Command_sortDeclLevelParams(x_17, x_18, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Elab_Term_throwError___rarg(x_22, x_7, x_16);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_26 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_25, x_6);
lean_inc(x_7);
lean_inc(x_26);
lean_inc(x_24);
lean_inc(x_3);
x_27 = l___private_Lean_Elab_Structure_25__mkCtor(x_3, x_24, x_26, x_10, x_7, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_26);
x_30 = l_Lean_Elab_Term_mkForall(x_26, x_12, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_7);
x_33 = l_Lean_Elab_Term_instantiateMVars(x_31, x_7, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_3, 4);
lean_inc(x_36);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_get_size(x_26);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_37);
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*2 + 3);
lean_dec(x_42);
x_44 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*3, x_43);
lean_inc(x_10);
x_45 = l_Array_filterAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__1(x_10, x_25, x_25);
x_46 = l_Array_toList___rarg(x_45);
lean_dec(x_45);
x_47 = l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__2(x_46);
lean_inc(x_7);
lean_inc(x_10);
x_48 = l_Array_filterMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__3(x_10, x_25, x_25, x_7, x_35);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Array_toList___rarg(x_49);
lean_dec(x_49);
x_52 = l_List_map___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__4(x_51);
x_53 = l_Lean_Elab_Term_getMCtx___rarg(x_50);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Elab_Term_getLCtx(x_7, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Elab_Term_getLocalInsts(x_7, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_10);
x_62 = l_Array_filterAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__5(x_10, x_25, x_25);
x_63 = x_62;
x_64 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6), 4, 2);
lean_closure_set(x_64, 0, x_25);
lean_closure_set(x_64, 1, x_63);
x_65 = x_64;
x_66 = lean_apply_2(x_65, x_7, x_61);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__7(x_3, x_6, x_26, x_25, x_57);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_3);
x_70 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__8(x_10, x_10, x_25, x_69);
lean_dec(x_10);
x_71 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_71, 0, x_44);
lean_ctor_set(x_71, 1, x_47);
lean_ctor_set(x_71, 2, x_52);
lean_ctor_set(x_71, 3, x_54);
lean_ctor_set(x_71, 4, x_70);
lean_ctor_set(x_71, 5, x_60);
lean_ctor_set(x_71, 6, x_68);
lean_ctor_set(x_66, 0, x_71);
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_66, 0);
x_73 = lean_ctor_get(x_66, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_66);
x_74 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__7(x_3, x_6, x_26, x_25, x_57);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_3);
x_75 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__8(x_10, x_10, x_25, x_74);
lean_dec(x_10);
x_76 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_76, 0, x_44);
lean_ctor_set(x_76, 1, x_47);
lean_ctor_set(x_76, 2, x_52);
lean_ctor_set(x_76, 3, x_54);
lean_ctor_set(x_76, 4, x_75);
lean_ctor_set(x_76, 5, x_60);
lean_ctor_set(x_76, 6, x_72);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_73);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
x_78 = !lean_is_exclusive(x_66);
if (x_78 == 0)
{
return x_66;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_66, 0);
x_80 = lean_ctor_get(x_66, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_66);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_26);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_48);
if (x_82 == 0)
{
return x_48;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_48, 0);
x_84 = lean_ctor_get(x_48, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_48);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_30);
if (x_86 == 0)
{
return x_30;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_30, 0);
x_88 = lean_ctor_get(x_30, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_30);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_90 = !lean_is_exclusive(x_27);
if (x_90 == 0)
{
return x_27;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_27, 0);
x_92 = lean_ctor_get(x_27, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_27);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_94 = !lean_is_exclusive(x_14);
if (x_94 == 0)
{
return x_14;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_14, 0);
x_96 = lean_ctor_get(x_14, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_14);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_9);
if (x_106 == 0)
{
return x_9;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_9, 0);
x_108 = lean_ctor_get(x_9, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_9);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(0);
lean_inc(x_5);
x_9 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_7, x_8, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_5);
lean_inc(x_1);
x_11 = l___private_Lean_Elab_Structure_12__getResultUniverse(x_1, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
x_14 = l_Lean_Elab_Command_shouldInferResultUniverse(x_12, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_2, 5);
lean_inc(x_17);
lean_inc(x_4);
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_26__elabStructureView___lambda__1___boxed), 8, 5);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_4);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_15);
lean_closure_set(x_18, 4, x_1);
x_19 = l___private_Lean_Elab_Structure_14__withUsed___rarg(x_17, x_3, x_4, x_18, x_5, x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
return x_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
return x_11;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 10);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_26__elabStructureView___lambda__2), 6, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Elab_Structure_11__withFields___main___rarg(x_7, x_9, x_4, x_8, x_5, x_6);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_26__elabStructureView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected Type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_26__elabStructureView___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_26__elabStructureView___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_26__elabStructureView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_26__elabStructureView___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 6);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 8);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_5);
x_6 = l_Lean_Elab_Term_elabType(x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_37; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_37 = l___private_Lean_Elab_Structure_4__validStructType(x_7);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_38 = l___private_Lean_Elab_Structure_26__elabStructureView___closed__3;
x_39 = l_Lean_Elab_Term_throwErrorAt___rarg(x_5, x_38, x_2, x_8);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
lean_dec(x_5);
x_9 = x_8;
goto block_36;
}
block_36:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_26__elabStructureView___lambda__3), 6, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_4);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 9);
x_14 = l_Lean_Elab_replaceRef(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
lean_ctor_set(x_2, 9, x_14);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_empty___closed__1;
x_17 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_1, x_15, x_16, x_11, x_2, x_9);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_ctor_get(x_2, 4);
x_23 = lean_ctor_get(x_2, 5);
x_24 = lean_ctor_get(x_2, 6);
x_25 = lean_ctor_get(x_2, 7);
x_26 = lean_ctor_get(x_2, 8);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*10);
x_28 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*10 + 2);
x_30 = lean_ctor_get(x_2, 9);
lean_inc(x_30);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_31 = l_Lean_Elab_replaceRef(x_10, x_30);
lean_dec(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_20);
lean_ctor_set(x_32, 3, x_21);
lean_ctor_set(x_32, 4, x_22);
lean_ctor_set(x_32, 5, x_23);
lean_ctor_set(x_32, 6, x_24);
lean_ctor_set(x_32, 7, x_25);
lean_ctor_set(x_32, 8, x_26);
lean_ctor_set(x_32, 9, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*10, x_27);
lean_ctor_set_uint8(x_32, sizeof(void*)*10 + 1, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*10 + 2, x_29);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Array_empty___closed__1;
x_35 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_1, x_33, x_34, x_11, x_32, x_9);
return x_35;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
return x_6;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_6, 0);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_6);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Structure_26__elabStructureView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l___private_Lean_Elab_Structure_26__elabStructureView___lambda__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_27__mkProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = lean_mk_projections(x_1, x_2, x_3, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_28__addProjections(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Elab_Command_getEnv___rarg(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_mk_projections(x_8, x_1, x_2, x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_Command_throwError___rarg(x_13, x_4, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_Elab_Command_setEnv(x_15, x_4, x_5, x_9);
lean_dec(x_4);
return x_16;
}
}
}
lean_object* l___private_Lean_Elab_Structure_28__addProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l___private_Lean_Elab_Structure_28__addProjections(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_29__mkAuxConstructions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_5 = l_Lean_Elab_Command_getEnv___rarg(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
lean_inc(x_6);
x_10 = l_Lean_Environment_contains(x_6, x_9);
x_11 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_6);
x_12 = l_Lean_Environment_contains(x_6, x_11);
x_13 = l_Lean_Expr_heq_x3f___closed__2;
x_14 = l_Lean_Environment_contains(x_6, x_13);
x_49 = lean_io_ref_take(x_3, x_7);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_50, 0);
x_54 = lean_mk_rec_on(x_53, x_1);
lean_ctor_set(x_50, 0, x_54);
x_55 = lean_io_ref_set(x_3, x_50, x_51);
if (x_10 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_15 = x_56;
goto block_48;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_io_ref_take(x_3, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = !lean_is_exclusive(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_59, 0);
x_63 = lean_mk_cases_on(x_62, x_1);
lean_ctor_set(x_59, 0, x_63);
x_64 = lean_io_ref_set(x_3, x_59, x_60);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_15 = x_65;
goto block_48;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 1);
x_68 = lean_ctor_get(x_59, 2);
x_69 = lean_ctor_get(x_59, 3);
x_70 = lean_ctor_get(x_59, 4);
x_71 = lean_ctor_get(x_59, 5);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_72 = lean_mk_cases_on(x_66, x_1);
x_73 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_68);
lean_ctor_set(x_73, 3, x_69);
lean_ctor_set(x_73, 4, x_70);
lean_ctor_set(x_73, 5, x_71);
x_74 = lean_io_ref_set(x_3, x_73, x_60);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_15 = x_75;
goto block_48;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_50, 0);
x_77 = lean_ctor_get(x_50, 1);
x_78 = lean_ctor_get(x_50, 2);
x_79 = lean_ctor_get(x_50, 3);
x_80 = lean_ctor_get(x_50, 4);
x_81 = lean_ctor_get(x_50, 5);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_50);
x_82 = lean_mk_rec_on(x_76, x_1);
x_83 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set(x_83, 4, x_80);
lean_ctor_set(x_83, 5, x_81);
x_84 = lean_io_ref_set(x_3, x_83, x_51);
if (x_10 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_15 = x_85;
goto block_48;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_io_ref_take(x_3, x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_88, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_88, 3);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 4);
lean_inc(x_94);
x_95 = lean_ctor_get(x_88, 5);
lean_inc(x_95);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 lean_ctor_release(x_88, 3);
 lean_ctor_release(x_88, 4);
 lean_ctor_release(x_88, 5);
 x_96 = x_88;
} else {
 lean_dec_ref(x_88);
 x_96 = lean_box(0);
}
x_97 = lean_mk_cases_on(x_90, x_1);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 6, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_91);
lean_ctor_set(x_98, 2, x_92);
lean_ctor_set(x_98, 3, x_93);
lean_ctor_set(x_98, 4, x_94);
lean_ctor_set(x_98, 5, x_95);
x_99 = lean_io_ref_set(x_3, x_98, x_89);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_15 = x_100;
goto block_48;
}
}
block_48:
{
if (x_10 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_17 = lean_alloc_ctor(0, 2, 0);
} else {
 x_17 = x_8;
}
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
if (x_12 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_8;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
if (x_14 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
if (lean_is_scalar(x_8)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_8;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_8);
x_22 = lean_io_ref_take(x_3, x_15);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_mk_no_confusion(x_26, x_1);
lean_ctor_set(x_23, 0, x_27);
x_28 = lean_io_ref_set(x_3, x_23, x_24);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_23, 0);
x_36 = lean_ctor_get(x_23, 1);
x_37 = lean_ctor_get(x_23, 2);
x_38 = lean_ctor_get(x_23, 3);
x_39 = lean_ctor_get(x_23, 4);
x_40 = lean_ctor_get(x_23, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_23);
x_41 = lean_mk_no_confusion(x_35, x_1);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set(x_42, 4, x_39);
lean_ctor_set(x_42, 5, x_40);
x_43 = lean_io_ref_set(x_3, x_42, x_24);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_29__mkAuxConstructions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_29__mkAuxConstructions(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_11, 4);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_11, 4, x_18);
x_19 = l_Lean_Meta_mkId(x_14, x_17, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_21, x_16);
x_23 = 1;
lean_inc(x_3);
lean_inc(x_12);
x_24 = l_Lean_Elab_Term_mkAuxDefinition(x_12, x_13, x_20, x_23, x_3, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = 0;
x_31 = lean_set_reducibility_status(x_29, x_12, x_30);
lean_ctor_set(x_27, 0, x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_2, x_32);
lean_dec(x_2);
x_2 = x_33;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
x_37 = lean_ctor_get(x_27, 2);
x_38 = lean_ctor_get(x_27, 3);
x_39 = lean_ctor_get(x_27, 4);
x_40 = lean_ctor_get(x_27, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_41 = 0;
x_42 = lean_set_reducibility_status(x_35, x_12, x_41);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_40);
lean_ctor_set(x_25, 0, x_43);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_2, x_44);
lean_dec(x_2);
x_2 = x_45;
x_4 = x_25;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
x_49 = lean_ctor_get(x_25, 2);
x_50 = lean_ctor_get(x_25, 3);
x_51 = lean_ctor_get(x_25, 4);
x_52 = lean_ctor_get(x_25, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_53 = lean_ctor_get(x_47, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_47, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_47, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_47, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_47, 5);
lean_inc(x_58);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 lean_ctor_release(x_47, 5);
 x_59 = x_47;
} else {
 lean_dec_ref(x_47);
 x_59 = lean_box(0);
}
x_60 = 0;
x_61 = lean_set_reducibility_status(x_53, x_12, x_60);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 6, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
lean_ctor_set(x_62, 2, x_55);
lean_ctor_set(x_62, 3, x_56);
lean_ctor_set(x_62, 4, x_57);
lean_ctor_set(x_62, 5, x_58);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_48);
lean_ctor_set(x_63, 2, x_49);
lean_ctor_set(x_63, 3, x_50);
lean_ctor_set(x_63, 4, x_51);
lean_ctor_set(x_63, 5, x_52);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_2, x_64);
lean_dec(x_2);
x_2 = x_65;
x_4 = x_63;
goto _start;
}
}
else
{
uint8_t x_67; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_24);
if (x_67 == 0)
{
return x_24;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_24, 0);
x_69 = lean_ctor_get(x_24, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_24);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_19);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
lean_inc(x_3);
x_74 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_72);
x_75 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_73, x_16);
lean_ctor_set(x_19, 1, x_75);
lean_ctor_set(x_19, 0, x_74);
return x_19;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_19, 0);
x_77 = lean_ctor_get(x_19, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_19);
lean_inc(x_3);
x_78 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_76);
x_79 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_77, x_16);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_81 = lean_ctor_get(x_11, 0);
x_82 = lean_ctor_get(x_11, 1);
x_83 = lean_ctor_get(x_11, 2);
x_84 = lean_ctor_get(x_11, 3);
x_85 = lean_ctor_get(x_11, 4);
x_86 = lean_ctor_get(x_11, 5);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_11);
x_87 = lean_ctor_get(x_3, 0);
lean_inc(x_87);
x_88 = l_Lean_TraceState_Inhabited___closed__1;
x_89 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_82);
lean_ctor_set(x_89, 2, x_83);
lean_ctor_set(x_89, 3, x_84);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_86);
x_90 = l_Lean_Meta_mkId(x_14, x_87, x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_3);
x_93 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_92, x_85);
x_94 = 1;
lean_inc(x_3);
lean_inc(x_12);
x_95 = l_Lean_Elab_Term_mkAuxDefinition(x_12, x_13, x_91, x_94, x_3, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 4);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 5);
lean_inc(x_102);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 lean_ctor_release(x_96, 5);
 x_103 = x_96;
} else {
 lean_dec_ref(x_96);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_97, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_97, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_97, 5);
lean_inc(x_109);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 lean_ctor_release(x_97, 4);
 lean_ctor_release(x_97, 5);
 x_110 = x_97;
} else {
 lean_dec_ref(x_97);
 x_110 = lean_box(0);
}
x_111 = 0;
x_112 = lean_set_reducibility_status(x_104, x_12, x_111);
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 6, 0);
} else {
 x_113 = x_110;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_106);
lean_ctor_set(x_113, 3, x_107);
lean_ctor_set(x_113, 4, x_108);
lean_ctor_set(x_113, 5, x_109);
if (lean_is_scalar(x_103)) {
 x_114 = lean_alloc_ctor(0, 6, 0);
} else {
 x_114 = x_103;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_98);
lean_ctor_set(x_114, 2, x_99);
lean_ctor_set(x_114, 3, x_100);
lean_ctor_set(x_114, 4, x_101);
lean_ctor_set(x_114, 5, x_102);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_add(x_2, x_115);
lean_dec(x_2);
x_2 = x_116;
x_4 = x_114;
goto _start;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_118 = lean_ctor_get(x_95, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_95, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_120 = x_95;
} else {
 lean_dec_ref(x_95);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_2);
x_122 = lean_ctor_get(x_90, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_90, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_124 = x_90;
} else {
 lean_dec_ref(x_90);
 x_124 = lean_box(0);
}
lean_inc(x_3);
x_125 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_122);
x_126 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_123, x_85);
if (lean_is_scalar(x_124)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_124;
}
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_30__addDefaults___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__1(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_30__addDefaults(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_box(0);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Term_setMCtx___boxed), 3, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_30__addDefaults___lambda__1___boxed), 4, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_monadLog___spec__2___rarg), 4, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
x_12 = lean_io_ref_get(x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l___private_Lean_Elab_Command_3__mkTermContext(x_5, x_13, x_8);
x_16 = l___private_Lean_Elab_Command_4__mkTermState(x_13);
lean_dec(x_13);
x_17 = l_Lean_Elab_Term_withLocalContext___rarg(x_2, x_3, x_11, x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_5);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_io_ref_take(x_6, x_14);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 3);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_ctor_get(x_19, 2);
lean_inc(x_26);
lean_dec(x_19);
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_22, 5);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
lean_ctor_set(x_22, 5, x_25);
lean_ctor_set(x_22, 1, x_26);
lean_ctor_set(x_22, 0, x_24);
x_31 = lean_io_ref_set(x_6, x_22, x_23);
lean_dec(x_6);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
lean_ctor_set(x_31, 0, x_18);
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_18);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_22, 2);
x_37 = lean_ctor_get(x_22, 3);
x_38 = lean_ctor_get(x_22, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_25);
x_40 = lean_io_ref_set(x_6, x_39, x_23);
lean_dec(x_6);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_18);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec(x_5);
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_io_ref_take(x_6, x_14);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 3);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_ctor_get(x_45, 2);
lean_inc(x_53);
lean_dec(x_45);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_49, 5);
lean_dec(x_55);
x_56 = lean_ctor_get(x_49, 1);
lean_dec(x_56);
x_57 = lean_ctor_get(x_49, 0);
lean_dec(x_57);
lean_ctor_set(x_49, 5, x_52);
lean_ctor_set(x_49, 1, x_53);
lean_ctor_set(x_49, 0, x_51);
x_58 = lean_io_ref_set(x_6, x_49, x_50);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_46);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_46);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_49, 2);
x_64 = lean_ctor_get(x_49, 3);
x_65 = lean_ctor_get(x_49, 4);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_49);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_51);
lean_ctor_set(x_66, 1, x_53);
lean_ctor_set(x_66, 2, x_63);
lean_ctor_set(x_66, 3, x_64);
lean_ctor_set(x_66, 4, x_65);
lean_ctor_set(x_66, 5, x_52);
x_67 = lean_io_ref_set(x_6, x_66, x_50);
lean_dec(x_6);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_69 = x_67;
} else {
 lean_dec_ref(x_67);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
 lean_ctor_set_tag(x_70, 1);
}
lean_ctor_set(x_70, 0, x_46);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_17);
x_71 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_72 = l_unreachable_x21___rarg(x_71);
x_73 = lean_apply_3(x_72, x_5, x_6, x_14);
return x_73;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Structure_30__addDefaults___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_30__addDefaults___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
lean_inc(x_2);
x_9 = l_Lean_Elab_Command_addInstance(x_7, x_2, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_1 = x_8;
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_8);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
lean_ctor_set(x_15, 3, x_4);
lean_ctor_set(x_15, 4, x_6);
lean_ctor_set(x_15, 5, x_7);
lean_ctor_set(x_15, 6, x_12);
lean_ctor_set(x_15, 7, x_8);
lean_ctor_set(x_15, 8, x_9);
lean_ctor_set(x_15, 9, x_10);
lean_ctor_set(x_15, 10, x_11);
lean_ctor_set_uint8(x_15, sizeof(void*)*11, x_5);
x_16 = l___private_Lean_Elab_Structure_26__elabStructureView(x_15, x_13, x_14);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(x_5);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__1___boxed), 14, 11);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_15);
lean_closure_set(x_16, 5, x_6);
lean_closure_set(x_16, 6, x_12);
lean_closure_set(x_16, 7, x_7);
lean_closure_set(x_16, 8, x_8);
lean_closure_set(x_16, 9, x_9);
lean_closure_set(x_16, 10, x_10);
x_17 = l_Lean_Elab_Term_elabBinders___rarg(x_11, x_16, x_13, x_14);
return x_17;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_9);
x_12 = l_Lean_Elab_Command_mkDeclName(x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_70 = l_Lean_Elab_Command_getLevelNames___rarg(x_10, x_14);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_9);
lean_inc(x_3);
x_73 = l___private_Lean_Elab_Structure_2__expandCtor(x_3, x_1, x_13, x_9, x_10, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l___private_Lean_Elab_Structure_3__expandFields(x_3, x_1, x_13, x_9, x_10, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_13);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_13);
x_80 = lean_box(x_2);
lean_inc(x_13);
lean_inc(x_1);
x_81 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__2___boxed), 14, 11);
lean_closure_set(x_81, 0, x_3);
lean_closure_set(x_81, 1, x_1);
lean_closure_set(x_81, 2, x_4);
lean_closure_set(x_81, 3, x_71);
lean_closure_set(x_81, 4, x_80);
lean_closure_set(x_81, 5, x_13);
lean_closure_set(x_81, 6, x_5);
lean_closure_set(x_81, 7, x_6);
lean_closure_set(x_81, 8, x_74);
lean_closure_set(x_81, 9, x_77);
lean_closure_set(x_81, 10, x_7);
x_82 = lean_io_ref_get(x_10, x_78);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l___private_Lean_Elab_Command_5__getVarDecls(x_83);
lean_dec(x_83);
x_86 = lean_io_ref_get(x_10, x_84);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l___private_Lean_Elab_Command_3__mkTermContext(x_9, x_87, x_79);
x_90 = l___private_Lean_Elab_Command_4__mkTermState(x_87);
lean_dec(x_87);
x_91 = l_Lean_Elab_Term_elabBinders___rarg(x_85, x_81, x_89, x_90);
lean_dec(x_85);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_io_ref_take(x_10, x_88);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_ctor_get(x_95, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_95, 3);
lean_inc(x_99);
lean_dec(x_95);
x_100 = lean_ctor_get(x_93, 2);
lean_inc(x_100);
lean_dec(x_93);
x_101 = !lean_is_exclusive(x_96);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_96, 5);
lean_dec(x_102);
x_103 = lean_ctor_get(x_96, 1);
lean_dec(x_103);
x_104 = lean_ctor_get(x_96, 0);
lean_dec(x_104);
lean_ctor_set(x_96, 5, x_99);
lean_ctor_set(x_96, 1, x_100);
lean_ctor_set(x_96, 0, x_98);
x_105 = lean_io_ref_set(x_10, x_96, x_97);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 0);
lean_dec(x_107);
lean_ctor_set(x_105, 0, x_92);
x_15 = x_105;
goto block_69;
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_92);
lean_ctor_set(x_109, 1, x_108);
x_15 = x_109;
goto block_69;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_96, 2);
x_111 = lean_ctor_get(x_96, 3);
x_112 = lean_ctor_get(x_96, 4);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_96);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_98);
lean_ctor_set(x_113, 1, x_100);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_111);
lean_ctor_set(x_113, 4, x_112);
lean_ctor_set(x_113, 5, x_99);
x_114 = lean_io_ref_set(x_10, x_113, x_97);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_92);
lean_ctor_set(x_117, 1, x_115);
x_15 = x_117;
goto block_69;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_91, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_119 = lean_ctor_get(x_91, 1);
lean_inc(x_119);
lean_dec(x_91);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_io_ref_take(x_10, x_88);
x_122 = lean_ctor_get(x_119, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 3);
lean_inc(x_126);
lean_dec(x_122);
x_127 = lean_ctor_get(x_119, 2);
lean_inc(x_127);
lean_dec(x_119);
x_128 = !lean_is_exclusive(x_123);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_123, 5);
lean_dec(x_129);
x_130 = lean_ctor_get(x_123, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_123, 0);
lean_dec(x_131);
lean_ctor_set(x_123, 5, x_126);
lean_ctor_set(x_123, 1, x_127);
lean_ctor_set(x_123, 0, x_125);
x_132 = lean_io_ref_set(x_10, x_123, x_124);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_132, 0);
lean_dec(x_134);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 0, x_120);
x_15 = x_132;
goto block_69;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_120);
lean_ctor_set(x_136, 1, x_135);
x_15 = x_136;
goto block_69;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_123, 2);
x_138 = lean_ctor_get(x_123, 3);
x_139 = lean_ctor_get(x_123, 4);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_123);
x_140 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_140, 0, x_125);
lean_ctor_set(x_140, 1, x_127);
lean_ctor_set(x_140, 2, x_137);
lean_ctor_set(x_140, 3, x_138);
lean_ctor_set(x_140, 4, x_139);
lean_ctor_set(x_140, 5, x_126);
x_141 = lean_io_ref_set(x_10, x_140, x_124);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
 lean_ctor_set_tag(x_144, 1);
}
lean_ctor_set(x_144, 0, x_120);
lean_ctor_set(x_144, 1, x_142);
x_15 = x_144;
goto block_69;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_91);
x_145 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_146 = l_unreachable_x21___rarg(x_145);
lean_inc(x_10);
lean_inc(x_9);
x_147 = lean_apply_3(x_146, x_9, x_10, x_88);
x_15 = x_147;
goto block_69;
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_76);
if (x_148 == 0)
{
return x_76;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_76, 0);
x_150 = lean_ctor_get(x_76, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_76);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_71);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_73);
if (x_152 == 0)
{
return x_73;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_73, 0);
x_154 = lean_ctor_get(x_73, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_73);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
block_69:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = l_Lean_Elab_Command_addDecl(x_18, x_9, x_10, x_17);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_9);
x_22 = l___private_Lean_Elab_Structure_28__addProjections(x_13, x_21, x_2, x_9, x_10, x_20);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l___private_Lean_Elab_Structure_29__mkAuxConstructions(x_13, x_9, x_10, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = 0;
x_28 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
x_29 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_13, x_27, x_26, x_28, x_9, x_10, x_25);
lean_dec(x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_16, 2);
lean_inc(x_31);
lean_inc(x_9);
x_32 = l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1(x_31, x_9, x_10, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_16, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_16, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_16, 5);
lean_inc(x_36);
x_37 = lean_ctor_get(x_16, 6);
lean_inc(x_37);
lean_dec(x_16);
x_38 = l___private_Lean_Elab_Structure_30__addDefaults(x_34, x_35, x_36, x_37, x_9, x_10, x_33);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_38);
if (x_45 == 0)
{
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
x_49 = !lean_is_exclusive(x_32);
if (x_49 == 0)
{
return x_32;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_32, 0);
x_51 = lean_ctor_get(x_32, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_32);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
x_53 = !lean_is_exclusive(x_29);
if (x_53 == 0)
{
return x_29;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_29, 0);
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_29);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_22);
if (x_57 == 0)
{
return x_22;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_22, 0);
x_59 = lean_ctor_get(x_22, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_22);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_19);
if (x_61 == 0)
{
return x_19;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_19, 0);
x_63 = lean_ctor_get(x_19, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_19);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_15);
if (x_65 == 0)
{
return x_15;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_15, 0);
x_67 = lean_ctor_get(x_15, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_15);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_12);
if (x_156 == 0)
{
return x_12;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_12, 0);
x_158 = lean_ctor_get(x_12, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_12);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Parser_Term_type___elambda__1___closed__5;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_elabStructure___closed__1;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Level_hole___elambda__1___closed__1;
x_2 = l___private_Lean_Elab_Quotation_5__explodeHeadPat___lambda__1___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_elabStructure___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_Elab_Command_elabStructure___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabStructure___closed__2;
x_2 = l_Lean_Elab_Command_elabStructure___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Parser_Term_type___elambda__1___closed__2;
x_2 = l_Lean_Elab_Command_elabStructure___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_registerClassAttr___closed__2;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_elabStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_3);
x_6 = l_Lean_Elab_Command_checkValidInductiveModifier(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_2, x_8);
x_10 = l_Lean_Syntax_getKind(x_9);
x_11 = l_Lean_Parser_Command_classTk___elambda__1___closed__2;
x_12 = lean_name_eq(x_10, x_11);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l_Lean_Syntax_getArg(x_2, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_2, x_15);
x_17 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = l_Lean_Syntax_getArg(x_2, x_18);
x_20 = l_Lean_Syntax_isNone(x_19);
x_21 = lean_unsigned_to_nat(4u);
x_22 = l_Lean_Syntax_getArg(x_2, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
if (x_12 == 0)
{
x_24 = x_1;
goto block_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_Elab_Command_elabStructure___closed__8;
x_51 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_50);
x_24 = x_51;
goto block_49;
}
block_49:
{
lean_object* x_25; 
if (x_20 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = l_Lean_Syntax_getArg(x_19, x_8);
lean_dec(x_19);
x_44 = l_Lean_Syntax_getArg(x_43, x_13);
lean_dec(x_43);
x_45 = l_Lean_Syntax_getArgs(x_44);
lean_dec(x_44);
x_46 = l_Array_empty___closed__1;
x_47 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_15, x_45, x_8, x_46);
lean_dec(x_45);
x_25 = x_47;
goto block_42;
}
else
{
lean_object* x_48; 
lean_dec(x_19);
x_48 = l_Array_empty___closed__1;
x_25 = x_48;
goto block_42;
}
block_42:
{
lean_object* x_26; lean_object* x_27; 
if (x_23 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lean_Syntax_getArg(x_22, x_8);
lean_dec(x_22);
x_36 = l_Lean_Syntax_getArg(x_35, x_13);
lean_dec(x_35);
x_26 = x_36;
x_27 = x_7;
goto block_34;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_22);
x_37 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_7);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Command_getMainModule___rarg(x_4, x_38);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Elab_Command_elabStructure___closed__7;
x_26 = x_41;
x_27 = x_40;
goto block_34;
}
block_34:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_Lean_Elab_Command_getLevelNames___rarg(x_4, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(x_12);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__3___boxed), 11, 7);
lean_closure_set(x_32, 0, x_24);
lean_closure_set(x_32, 1, x_31);
lean_closure_set(x_32, 2, x_2);
lean_closure_set(x_32, 3, x_29);
lean_closure_set(x_32, 4, x_25);
lean_closure_set(x_32, 5, x_26);
lean_closure_set(x_32, 6, x_17);
x_33 = l_Lean_Elab_Command_withDeclId___rarg(x_14, x_32, x_3, x_4, x_30);
lean_dec(x_14);
return x_33;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_6);
if (x_52 == 0)
{
return x_6;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_6, 0);
x_54 = lean_ctor_get(x_6, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_6);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Command_elabStructure___lambda__1(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Lean_Elab_Command_elabStructure___lambda__2(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
return x_16;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Elab_Command_elabStructure___lambda__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_DeclModifiers(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
lean_object* initialize_Lean_Elab_Inductive(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Structure(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclModifiers(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Inductive(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_StructFieldInfo_inhabited___closed__1 = _init_l_Lean_Elab_Command_StructFieldInfo_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_StructFieldInfo_inhabited___closed__1);
l_Lean_Elab_Command_StructFieldInfo_inhabited = _init_l_Lean_Elab_Command_StructFieldInfo_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_StructFieldInfo_inhabited);
l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1 = _init_l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1);
l___private_Lean_Elab_Structure_1__defaultCtorName = _init_l___private_Lean_Elab_Structure_1__defaultCtorName();
lean_mark_persistent(l___private_Lean_Elab_Structure_1__defaultCtorName);
l___private_Lean_Elab_Structure_2__expandCtor___closed__1 = _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_2__expandCtor___closed__1);
l___private_Lean_Elab_Structure_2__expandCtor___closed__2 = _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_2__expandCtor___closed__2);
l___private_Lean_Elab_Structure_2__expandCtor___closed__3 = _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_2__expandCtor___closed__3);
l___private_Lean_Elab_Structure_2__expandCtor___closed__4 = _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_2__expandCtor___closed__4);
l___private_Lean_Elab_Structure_2__expandCtor___closed__5 = _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Structure_2__expandCtor___closed__5);
l___private_Lean_Elab_Structure_2__expandCtor___closed__6 = _init_l___private_Lean_Elab_Structure_2__expandCtor___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Structure_2__expandCtor___closed__6);
l_Lean_Elab_Command_checkValidFieldModifier___closed__1 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__1);
l_Lean_Elab_Command_checkValidFieldModifier___closed__2 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__2);
l_Lean_Elab_Command_checkValidFieldModifier___closed__3 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__3);
l_Lean_Elab_Command_checkValidFieldModifier___closed__4 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__4);
l_Lean_Elab_Command_checkValidFieldModifier___closed__5 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__5);
l_Lean_Elab_Command_checkValidFieldModifier___closed__6 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__6);
l_Lean_Elab_Command_checkValidFieldModifier___closed__7 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__7);
l_Lean_Elab_Command_checkValidFieldModifier___closed__8 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__8);
l_Lean_Elab_Command_checkValidFieldModifier___closed__9 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__9);
l_Lean_Elab_Command_checkValidFieldModifier___closed__10 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__10);
l_Lean_Elab_Command_checkValidFieldModifier___closed__11 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__11);
l_Lean_Elab_Command_checkValidFieldModifier___closed__12 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__12);
l_Lean_Elab_Command_checkValidFieldModifier___closed__13 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__13();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__13);
l_Lean_Elab_Command_checkValidFieldModifier___closed__14 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__14();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__14);
l_Lean_Elab_Command_checkValidFieldModifier___closed__15 = _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__15();
lean_mark_persistent(l_Lean_Elab_Command_checkValidFieldModifier___closed__15);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9);
l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__1 = _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__1);
l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__2 = _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__2);
l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3 = _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3);
l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__4 = _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__4);
l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__5 = _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__5);
l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6 = _init_l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6);
l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__1 = _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__1);
l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__2 = _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__2);
l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3 = _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3);
l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__4 = _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__4);
l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__5 = _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__5);
l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6 = _init_l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6);
l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1 = _init_l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1);
l___private_Lean_Elab_Structure_10__elabFieldTypeValue___closed__1 = _init_l___private_Lean_Elab_Structure_10__elabFieldTypeValue___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__elabFieldTypeValue___closed__1);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__1 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__1);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__2 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__2);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__4 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__4);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__5 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__5);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__7 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__7);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__8 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__8);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__10 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__10);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__11 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__11);
l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12 = _init_l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12);
l___private_Lean_Elab_Structure_12__getResultUniverse___closed__1 = _init_l___private_Lean_Elab_Structure_12__getResultUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_12__getResultUniverse___closed__1);
l___private_Lean_Elab_Structure_12__getResultUniverse___closed__2 = _init_l___private_Lean_Elab_Structure_12__getResultUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_12__getResultUniverse___closed__2);
l___private_Lean_Elab_Structure_12__getResultUniverse___closed__3 = _init_l___private_Lean_Elab_Structure_12__getResultUniverse___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_12__getResultUniverse___closed__3);
l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__1);
l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__2);
l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__3 = _init_l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_20__updateResultingUniverse___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_26__elabStructureView___spec__6___closed__2);
l___private_Lean_Elab_Structure_26__elabStructureView___closed__1 = _init_l___private_Lean_Elab_Structure_26__elabStructureView___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_26__elabStructureView___closed__1);
l___private_Lean_Elab_Structure_26__elabStructureView___closed__2 = _init_l___private_Lean_Elab_Structure_26__elabStructureView___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_26__elabStructureView___closed__2);
l___private_Lean_Elab_Structure_26__elabStructureView___closed__3 = _init_l___private_Lean_Elab_Structure_26__elabStructureView___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_26__elabStructureView___closed__3);
l_Lean_Elab_Command_elabStructure___closed__1 = _init_l_Lean_Elab_Command_elabStructure___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__1);
l_Lean_Elab_Command_elabStructure___closed__2 = _init_l_Lean_Elab_Command_elabStructure___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__2);
l_Lean_Elab_Command_elabStructure___closed__3 = _init_l_Lean_Elab_Command_elabStructure___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__3);
l_Lean_Elab_Command_elabStructure___closed__4 = _init_l_Lean_Elab_Command_elabStructure___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__4);
l_Lean_Elab_Command_elabStructure___closed__5 = _init_l_Lean_Elab_Command_elabStructure___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__5);
l_Lean_Elab_Command_elabStructure___closed__6 = _init_l_Lean_Elab_Command_elabStructure___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__6);
l_Lean_Elab_Command_elabStructure___closed__7 = _init_l_Lean_Elab_Command_elabStructure___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__7);
l_Lean_Elab_Command_elabStructure___closed__8 = _init_l_Lean_Elab_Command_elabStructure___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__8);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
