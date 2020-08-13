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
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__1;
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__3;
lean_object* l___private_Lean_Elab_Structure_23__addCtorFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_inhabited;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_Structure_28__mkAuxConstructions___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__2(lean_object*);
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__4;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__14;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9;
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__3;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__2;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__4;
lean_object* l___private_Lean_Elab_Structure_29__addDefaults___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_withDeclId___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__1;
lean_object* l___private_Lean_Elab_Structure_12__removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Structure_14__levelMVarToParamFVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__addCtorFields___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_29__addDefaults___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Structure_3__expandFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInternalSubobjectFieldName(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__7;
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse___closed__3;
lean_object* l_Lean_Elab_Term_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structExplicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_applyVisibility(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_4__validStructType___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__8;
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__4;
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1;
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__12;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__5;
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__10;
lean_object* l___private_Lean_Elab_Structure_9__withParents(lean_object*);
uint8_t l___private_Lean_Elab_Structure_7__containsFieldName(lean_object*, lean_object*);
lean_object* l_Lean_Level_getLevelOffset___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_13__withUsed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__1;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DepElim_getUnusedLevelParam___closed__1;
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__5;
uint8_t l_Lean_Elab_Command_StructFieldInfo_isSubobject(lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_13__withUsed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
lean_object* l_Lean_Elab_Command_elabStructure___closed__8;
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse___closed__1;
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_addGlobalInstance___spec__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__15;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__4;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6;
lean_object* l_Lean_Elab_Command_elabStructure___closed__4;
lean_object* l_Lean_Elab_Term_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkId(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__2;
lean_object* l___private_Lean_Elab_Structure_1__defaultCtorName;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__1;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse___closed__2;
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__4(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
lean_object* l_Lean_Level_getOffsetAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__5;
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_29__addDefaults___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_13__withUsed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* lean_mk_no_confusion(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__9;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__5;
uint8_t l___private_Lean_Elab_Structure_4__validStructType(lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__3;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__5;
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7;
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerClassAttr___closed__2;
lean_object* l_Lean_LocalContext_updateBinderInfo(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__11;
extern lean_object* l___private_Lean_Elab_Quotation_5__explodeHeadPat___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__5;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_26__mkProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__3;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__10;
extern lean_object* l_Lean_Parser_Level_hole___elambda__1___closed__1;
lean_object* lean_mk_projections(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8;
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__addCtorFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure___closed__6;
lean_object* l___private_Lean_Elab_Structure_3__expandFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Elab_Term_setMCtx(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___closed__2;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2;
lean_object* l___private_Lean_Elab_Command_7__mkTermState(lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__7;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___closed__1;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_getMainModule(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__8;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1;
lean_object* l_Lean_Elab_Command_elabStructure___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__4;
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_addAttribute(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structInstBinder___elambda__1___closed__2;
lean_object* l___private_Lean_Elab_Structure_29__addDefaults___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__2;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__11;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__6;
lean_object* l___private_Lean_Elab_Structure_29__addDefaults(lean_object*);
lean_object* l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_8__getVarDecls(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_set_reducibility_status(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_getEnv(lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
uint8_t l_Lean_Elab_Command_StructFieldInfo_isFromParent(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_prodToExpr___rarg___lambda__1___closed__3;
lean_object* lean_mk_rec_on(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__1;
lean_object* l___private_Lean_Elab_Structure_24__mkCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
extern lean_object* l_Lean_Elab_Command_CtorView_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6;
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__13;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__addCtorFields___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_setEnv(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkProjection___main___closed__7;
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_29__addDefaults___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_Modifiers_isProtected(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__1;
uint8_t l_Lean_Elab_Command_Modifiers_isPrivate(lean_object*);
lean_object* l_Lean_Elab_Term_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_27__addProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_29__addDefaults___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendBefore(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVars(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_Structure_27__addProjections(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_inferImplicit___main(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Structure_9__withParents___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__3;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Structure_12__removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__7;
lean_object* l_Lean_Level_mkNaryMax___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_structImplicitBinder___elambda__1___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4;
lean_object* l_Lean_Meta_mkProjection___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_7__containsFieldName___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_24__mkCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateLevelMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_classTk___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__6;
lean_object* l_Lean_Elab_Term_getMCtx___rarg(lean_object*);
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_18__collectUniversesFromFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___closed__3;
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_28__mkAuxConstructions(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_18__collectUniversesFromFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* l___private_Lean_Elab_Structure_2__expandCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(6u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = l_Lean_Syntax_isNone(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Syntax_getArg(x_7, x_9);
lean_dec(x_7);
x_11 = l_Lean_Syntax_getArg(x_10, x_9);
lean_inc(x_4);
x_12 = l_Lean_Elab_Command_elabModifiers(x_11, x_4, x_5);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Command_Modifiers_isPrivate(x_13);
x_16 = l_Lean_Elab_Command_Modifiers_isProtected(x_13);
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_10, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = l_Lean_Syntax_getIdAt(x_10, x_20);
lean_inc(x_21);
x_22 = l_Lean_Name_append___main(x_3, x_21);
x_23 = lean_ctor_get_uint8(x_13, sizeof(void*)*2);
lean_inc(x_4);
x_24 = l_Lean_Elab_Command_checkValidCtorModifier(x_10, x_13, x_4, x_14);
if (x_15 == 0)
{
uint8_t x_78; 
x_78 = 0;
x_25 = x_78;
goto block_77;
}
else
{
uint8_t x_79; 
x_79 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
x_25 = x_79;
goto block_77;
}
block_77:
{
uint8_t x_26; 
if (x_25 == 0)
{
uint8_t x_75; 
x_75 = 0;
x_26 = x_75;
goto block_74;
}
else
{
uint8_t x_76; 
x_76 = 1;
x_26 = x_76;
goto block_74;
}
block_74:
{
uint8_t x_27; 
if (x_16 == 0)
{
uint8_t x_72; 
x_72 = 0;
x_27 = x_72;
goto block_71;
}
else
{
uint8_t x_73; 
x_73 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
x_27 = x_73;
goto block_71;
}
block_71:
{
uint8_t x_28; 
if (x_27 == 0)
{
uint8_t x_69; 
x_69 = 0;
x_28 = x_69;
goto block_68;
}
else
{
uint8_t x_70; 
x_70 = 1;
x_28 = x_70;
goto block_68;
}
block_68:
{
uint8_t x_29; lean_object* x_30; 
if (x_19 == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_dec(x_24);
x_57 = 1;
x_29 = x_57;
x_30 = x_56;
goto block_55;
}
else
{
uint8_t x_58; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_24);
if (x_58 == 0)
{
return x_24;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_24, 0);
x_60 = lean_ctor_get(x_24, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_24);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_24, 1);
lean_inc(x_62);
lean_dec(x_24);
x_63 = 0;
x_29 = x_63;
x_30 = x_62;
goto block_55;
}
else
{
uint8_t x_64; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_24);
if (x_64 == 0)
{
return x_24;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_24, 0);
x_66 = lean_ctor_get(x_24, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_24);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
block_55:
{
if (x_26 == 0)
{
if (x_28 == 0)
{
lean_object* x_31; 
x_31 = l_Lean_Elab_Command_applyVisibility(x_10, x_23, x_22, x_4, x_30);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_13);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*4, x_29);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
x_37 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_13);
lean_ctor_set(x_37, 2, x_21);
lean_ctor_set(x_37, 3, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4, x_29);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_10);
x_39 = !lean_is_exclusive(x_31);
if (x_39 == 0)
{
return x_31;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_31, 0);
x_41 = lean_ctor_get(x_31, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_31);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_13);
x_43 = l___private_Lean_Elab_Structure_2__expandCtor___closed__3;
x_44 = l_Lean_Elab_Command_throwError___rarg(x_10, x_43, x_4, x_30);
lean_dec(x_10);
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
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_13);
x_49 = l___private_Lean_Elab_Structure_2__expandCtor___closed__6;
x_50 = l_Lean_Elab_Command_throwError___rarg(x_10, x_49, x_4, x_30);
lean_dec(x_10);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_10);
lean_dec(x_4);
x_80 = !lean_is_exclusive(x_12);
if (x_80 == 0)
{
return x_12;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_12, 0);
x_82 = lean_ctor_get(x_12, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_12);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_7);
lean_dec(x_4);
x_84 = l___private_Lean_Elab_Structure_1__defaultCtorName;
x_85 = l_Lean_Name_append___main(x_3, x_84);
x_86 = l_Lean_Elab_Command_CtorView_inhabited___closed__1;
x_87 = 0;
x_88 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_84);
lean_ctor_set(x_88, 3, x_85);
lean_ctor_set_uint8(x_88, sizeof(void*)*4, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_5);
return x_89;
}
}
}
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_2__expandCtor(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidFieldModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("private fields are not supported yet");
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
x_1 = lean_mk_string("invalid use of attributes in field declaration");
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
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
if (x_5 == 0)
{
uint8_t x_71; 
x_71 = 0;
x_13 = x_71;
goto block_70;
}
else
{
uint8_t x_72; 
x_72 = 1;
x_13 = x_72;
goto block_70;
}
block_70:
{
uint8_t x_14; 
if (x_6 == 0)
{
uint8_t x_68; 
x_68 = 0;
x_14 = x_68;
goto block_67;
}
else
{
uint8_t x_69; 
x_69 = 1;
x_14 = x_69;
goto block_67;
}
block_67:
{
uint8_t x_15; 
if (x_7 == 0)
{
uint8_t x_65; 
x_65 = 0;
x_15 = x_65;
goto block_64;
}
else
{
uint8_t x_66; 
x_66 = 1;
x_15 = x_66;
goto block_64;
}
block_64:
{
uint8_t x_16; 
if (x_11 == 0)
{
uint8_t x_62; 
x_62 = 1;
x_16 = x_62;
goto block_61;
}
else
{
uint8_t x_63; 
x_63 = 0;
x_16 = x_63;
goto block_61;
}
block_61:
{
uint8_t x_17; 
if (x_16 == 0)
{
uint8_t x_59; 
x_59 = 0;
x_17 = x_59;
goto block_58;
}
else
{
uint8_t x_60; 
x_60 = 1;
x_17 = x_60;
goto block_58;
}
block_58:
{
uint8_t x_18; 
if (x_12 == 0)
{
uint8_t x_56; 
x_56 = 0;
x_18 = x_56;
goto block_55;
}
else
{
uint8_t x_57; 
x_57 = 1;
x_18 = x_57;
goto block_55;
}
block_55:
{
lean_object* x_19; lean_object* x_35; 
if (x_13 == 0)
{
x_35 = x_4;
goto block_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = l_Lean_Elab_Command_checkValidFieldModifier___closed__15;
x_50 = l_Lean_Elab_Command_throwError___rarg(x_1, x_49, x_3, x_4);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
block_34:
{
if (x_17 == 0)
{
if (x_18 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Elab_Command_checkValidFieldModifier___closed__3;
x_23 = l_Lean_Elab_Command_throwError___rarg(x_1, x_22, x_3, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Elab_Command_checkValidFieldModifier___closed__6;
x_29 = l_Lean_Elab_Command_throwError___rarg(x_1, x_28, x_3, x_19);
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
}
block_48:
{
if (x_14 == 0)
{
if (x_15 == 0)
{
x_19 = x_35;
goto block_34;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = l_Lean_Elab_Command_checkValidFieldModifier___closed__9;
x_37 = l_Lean_Elab_Command_throwError___rarg(x_1, x_36, x_3, x_35);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
return x_37;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = l_Lean_Elab_Command_checkValidFieldModifier___closed__12;
x_43 = l_Lean_Elab_Command_throwError___rarg(x_1, x_42, x_3, x_35);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
}
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
lean_dec(x_2);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_9);
x_15 = lean_nat_dec_lt(x_10, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_array_fget(x_9, x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_10, x_18);
lean_dec(x_10);
x_20 = l_Lean_Syntax_getId(x_17);
x_21 = l_Lean_isInternalSubobjectFieldName(x_20);
lean_inc(x_20);
x_22 = l_Lean_Name_append___main(x_1, x_20);
if (x_21 == 0)
{
uint8_t x_23; lean_object* x_24; 
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_12);
x_24 = l_Lean_Elab_Command_applyVisibility(x_17, x_23, x_22, x_12, x_13);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_27 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set(x_27, 3, x_20);
lean_ctor_set(x_27, 4, x_6);
lean_ctor_set(x_27, 5, x_7);
lean_ctor_set(x_27, 6, x_8);
lean_ctor_set_uint8(x_27, sizeof(void*)*7, x_3);
lean_ctor_set_uint8(x_27, sizeof(void*)*7 + 1, x_5);
x_28 = lean_array_push(x_11, x_27);
x_10 = x_19;
x_11 = x_28;
x_13 = x_26;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
return x_24;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_34 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_34, 0, x_20);
x_35 = l_Lean_Meta_mkProjection___main___closed__7;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Elab_Command_throwError___rarg(x_17, x_38, x_12, x_13);
lean_dec(x_17);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
lean_inc(x_12);
x_128 = l_Lean_Syntax_getKind(x_12);
x_129 = l_Lean_Parser_Command_structExplicitBinder___elambda__1___closed__2;
x_130 = lean_name_eq(x_128, x_129);
if (x_130 == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = l_Lean_Parser_Command_structImplicitBinder___elambda__1___closed__2;
x_132 = lean_name_eq(x_128, x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = l_Lean_Parser_Command_structInstBinder___elambda__1___closed__2;
x_134 = lean_name_eq(x_128, x_133);
lean_dec(x_128);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
lean_dec(x_14);
lean_dec(x_6);
x_135 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9;
x_136 = l_Lean_Elab_Command_throwError___rarg(x_12, x_135, x_7, x_8);
lean_dec(x_12);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
return x_136;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_136);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
else
{
uint8_t x_141; 
x_141 = 3;
x_15 = x_141;
x_16 = x_8;
goto block_127;
}
}
else
{
uint8_t x_142; 
lean_dec(x_128);
x_142 = 1;
x_15 = x_142;
x_16 = x_8;
goto block_127;
}
}
else
{
uint8_t x_143; 
lean_dec(x_128);
x_143 = 0;
x_15 = x_143;
x_16 = x_8;
goto block_127;
}
block_127:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Syntax_getArg(x_12, x_17);
lean_inc(x_7);
x_19 = l_Lean_Elab_Command_elabModifiers(x_18, x_7, x_16);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Command_Modifiers_isPrivate(x_20);
x_23 = l_Lean_Elab_Command_Modifiers_isProtected(x_20);
x_24 = lean_unsigned_to_nat(3u);
x_25 = l_Lean_Syntax_getArg(x_12, x_24);
x_26 = l_Lean_Syntax_isNone(x_25);
lean_dec(x_25);
x_27 = 0;
x_28 = l_Lean_BinderInfo_beq(x_15, x_27);
lean_inc(x_7);
x_29 = l_Lean_Elab_Command_checkValidFieldModifier(x_12, x_20, x_7, x_21);
if (x_22 == 0)
{
uint8_t x_121; 
x_121 = 0;
x_30 = x_121;
goto block_120;
}
else
{
uint8_t x_122; 
x_122 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
x_30 = x_122;
goto block_120;
}
block_120:
{
uint8_t x_31; 
if (x_30 == 0)
{
uint8_t x_118; 
x_118 = 0;
x_31 = x_118;
goto block_117;
}
else
{
uint8_t x_119; 
x_119 = 1;
x_31 = x_119;
goto block_117;
}
block_117:
{
uint8_t x_32; 
if (x_23 == 0)
{
uint8_t x_115; 
x_115 = 0;
x_32 = x_115;
goto block_114;
}
else
{
uint8_t x_116; 
x_116 = l_Lean_Elab_Command_Modifiers_isPrivate(x_2);
x_32 = x_116;
goto block_114;
}
block_114:
{
uint8_t x_33; 
if (x_32 == 0)
{
uint8_t x_112; 
x_112 = 0;
x_33 = x_112;
goto block_111;
}
else
{
uint8_t x_113; 
x_113 = 1;
x_33 = x_113;
goto block_111;
}
block_111:
{
uint8_t x_34; 
if (x_26 == 0)
{
uint8_t x_109; 
x_109 = 1;
x_34 = x_109;
goto block_108;
}
else
{
uint8_t x_110; 
x_110 = 0;
x_34 = x_110;
goto block_108;
}
block_108:
{
lean_object* x_35; 
if (x_28 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_unsigned_to_nat(4u);
x_96 = l_Lean_Syntax_getArg(x_12, x_95);
x_97 = l_Lean_Elab_expandDeclSig(x_96);
lean_dec(x_96);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 1);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_97, 1, x_100);
x_35 = x_97;
goto block_94;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_97);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_35 = x_104;
goto block_94;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_unsigned_to_nat(4u);
x_106 = l_Lean_Syntax_getArg(x_12, x_105);
x_107 = l_Lean_Elab_expandOptDeclSig(x_106);
lean_dec(x_106);
x_35 = x_107;
goto block_94;
}
block_94:
{
lean_object* x_36; 
if (lean_obj_tag(x_29) == 0)
{
if (x_31 == 0)
{
if (x_33 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_29, 1);
lean_inc(x_75);
lean_dec(x_29);
x_36 = x_75;
goto block_74;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_6);
x_76 = lean_ctor_get(x_29, 1);
lean_inc(x_76);
lean_dec(x_29);
x_77 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3;
x_78 = l_Lean_Elab_Command_throwError___rarg(x_12, x_77, x_7, x_76);
lean_dec(x_12);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
return x_78;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_78);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_6);
x_83 = lean_ctor_get(x_29, 1);
lean_inc(x_83);
lean_dec(x_29);
x_84 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6;
x_85 = l_Lean_Elab_Command_throwError___rarg(x_12, x_84, x_7, x_83);
lean_dec(x_12);
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
}
else
{
uint8_t x_90; 
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_90 = !lean_is_exclusive(x_29);
if (x_90 == 0)
{
return x_29;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_29, 0);
x_92 = lean_ctor_get(x_29, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_29);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
block_74:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_unsigned_to_nat(2u);
x_40 = l_Lean_Syntax_getArg(x_12, x_39);
x_41 = l_Lean_Syntax_getArgs(x_40);
lean_dec(x_40);
if (x_28 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
lean_inc(x_7);
x_43 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_12, x_15, x_20, x_34, x_37, x_38, x_42, x_41, x_17, x_6, x_7, x_36);
lean_dec(x_41);
lean_dec(x_12);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_5 = x_14;
x_6 = x_44;
x_8 = x_45;
goto _start;
}
else
{
uint8_t x_47; 
lean_dec(x_14);
lean_dec(x_7);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_unsigned_to_nat(5u);
x_52 = l_Lean_Syntax_getArg(x_12, x_51);
x_53 = l_Lean_Syntax_isNone(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = l_Lean_Syntax_getArg(x_52, x_17);
lean_dec(x_52);
x_55 = l_Lean_Syntax_getArg(x_54, x_13);
lean_dec(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_inc(x_7);
x_57 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_12, x_15, x_20, x_34, x_37, x_38, x_56, x_41, x_17, x_6, x_7, x_36);
lean_dec(x_41);
lean_dec(x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_5 = x_14;
x_6 = x_58;
x_8 = x_59;
goto _start;
}
else
{
uint8_t x_61; 
lean_dec(x_14);
lean_dec(x_7);
x_61 = !lean_is_exclusive(x_57);
if (x_61 == 0)
{
return x_57;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 0);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_52);
x_65 = lean_box(0);
lean_inc(x_7);
x_66 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_12, x_15, x_20, x_34, x_37, x_38, x_65, x_41, x_17, x_6, x_7, x_36);
lean_dec(x_41);
lean_dec(x_12);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_5 = x_14;
x_6 = x_67;
x_8 = x_68;
goto _start;
}
else
{
uint8_t x_70; 
lean_dec(x_14);
lean_dec(x_7);
x_70 = !lean_is_exclusive(x_66);
if (x_70 == 0)
{
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
}
}
}
}
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
x_123 = !lean_is_exclusive(x_19);
if (x_123 == 0)
{
return x_19;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_19, 0);
x_125 = lean_ctor_get(x_19, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_19);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_3__expandFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_unsigned_to_nat(7u);
x_7 = l_Lean_Syntax_getArg(x_1, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_7, x_8);
lean_dec(x_7);
x_10 = l_Lean_Syntax_getArgs(x_9);
lean_dec(x_9);
x_11 = l_Array_empty___closed__1;
x_12 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(x_1, x_2, x_3, x_10, x_8, x_11, x_4, x_5);
lean_dec(x_10);
return x_12;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_1, x_2, x_14, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Structure_3__expandFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_3__expandFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
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
x_15 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
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
x_31 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_array_fget(x_4, x_5);
x_14 = l_Lean_Elab_Term_getEnv___rarg(x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Elab_Structure_7__containsFieldName(x_6, x_13);
if (x_16 == 0)
{
x_17 = x_15;
goto block_74;
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
x_84 = l_Lean_Elab_Term_throwError___rarg(x_83, x_8, x_15);
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
block_74:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 4);
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_18, 4, x_22);
lean_inc(x_13);
lean_inc(x_2);
x_23 = l_Lean_Meta_mkProjection___main(x_2, x_13, x_21, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_17, x_25, x_20);
lean_inc(x_8);
lean_inc(x_24);
x_27 = l_Lean_Elab_Term_inferType(x_24, x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_13);
x_30 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed), 11, 8);
lean_closure_set(x_30, 0, x_1);
lean_closure_set(x_30, 1, x_13);
lean_closure_set(x_30, 2, x_6);
lean_closure_set(x_30, 3, x_5);
lean_closure_set(x_30, 4, x_2);
lean_closure_set(x_30, 5, x_3);
lean_closure_set(x_30, 6, x_4);
lean_closure_set(x_30, 7, x_7);
x_31 = l_Lean_Elab_Term_withLetDecl___rarg(x_13, x_28, x_24, x_30, x_8, x_29);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_8);
x_39 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_37);
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_17, x_38, x_20);
lean_ctor_set(x_23, 1, x_40);
lean_ctor_set(x_23, 0, x_39);
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
lean_inc(x_8);
x_43 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_41);
x_44 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_17, x_42, x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_18, 0);
x_47 = lean_ctor_get(x_18, 1);
x_48 = lean_ctor_get(x_18, 2);
x_49 = lean_ctor_get(x_18, 3);
x_50 = lean_ctor_get(x_18, 4);
x_51 = lean_ctor_get(x_18, 5);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_18);
x_52 = lean_ctor_get(x_8, 0);
lean_inc(x_52);
x_53 = l_Lean_TraceState_Inhabited___closed__1;
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_46);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_54, 2, x_48);
lean_ctor_set(x_54, 3, x_49);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_54, 5, x_51);
lean_inc(x_13);
lean_inc(x_2);
x_55 = l_Lean_Meta_mkProjection___main(x_2, x_13, x_52, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_8);
x_58 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_17, x_57, x_50);
lean_inc(x_8);
lean_inc(x_56);
x_59 = l_Lean_Elab_Term_inferType(x_56, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_13);
x_62 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed), 11, 8);
lean_closure_set(x_62, 0, x_1);
lean_closure_set(x_62, 1, x_13);
lean_closure_set(x_62, 2, x_6);
lean_closure_set(x_62, 3, x_5);
lean_closure_set(x_62, 4, x_2);
lean_closure_set(x_62, 5, x_3);
lean_closure_set(x_62, 6, x_4);
lean_closure_set(x_62, 7, x_7);
x_63 = l_Lean_Elab_Term_withLetDecl___rarg(x_13, x_60, x_56, x_62, x_8, x_61);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_56);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_66 = x_59;
} else {
 lean_dec_ref(x_59);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_55, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_55, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_70 = x_55;
} else {
 lean_dec_ref(x_55);
 x_70 = lean_box(0);
}
lean_inc(x_8);
x_71 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_68);
x_72 = l___private_Lean_Elab_Term_3__fromMetaState(x_8, x_17, x_69, x_50);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
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
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 10);
lean_dec(x_13);
lean_inc(x_11);
lean_ctor_set(x_5, 10, x_11);
lean_inc(x_5);
lean_inc(x_11);
x_14 = l_Lean_Elab_Term_elabType(x_11, x_5, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
x_17 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_15, x_5, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Name_eraseMacroScopes(x_18);
x_21 = l_Lean_Name_getString_x21(x_20);
lean_dec(x_20);
x_22 = l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
x_23 = lean_string_append(x_22, x_21);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_name_mk_string(x_24, x_23);
x_26 = l___private_Lean_Elab_Structure_7__containsFieldName(x_3, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
lean_dec(x_11);
x_27 = l_Lean_Elab_Term_getEnv___rarg(x_19);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_18);
lean_inc(x_28);
lean_inc(x_25);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2), 10, 7);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_25);
lean_closure_set(x_31, 2, x_3);
lean_closure_set(x_31, 3, x_28);
lean_closure_set(x_31, 4, x_18);
lean_closure_set(x_31, 5, x_2);
lean_closure_set(x_31, 6, x_4);
if (x_30 == 0)
{
uint8_t x_32; lean_object* x_33; 
lean_dec(x_28);
lean_dec(x_18);
x_32 = 0;
x_33 = l_Lean_Elab_Term_withLocalDecl___rarg(x_25, x_32, x_15, x_31, x_5, x_29);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_is_class(x_28, x_18);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; 
x_35 = 0;
x_36 = l_Lean_Elab_Term_withLocalDecl___rarg(x_25, x_35, x_15, x_31, x_5, x_29);
return x_36;
}
else
{
uint8_t x_37; lean_object* x_38; 
x_37 = 3;
x_38 = l_Lean_Elab_Term_withLocalDecl___rarg(x_25, x_37, x_15, x_31, x_5, x_29);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_39, 0, x_25);
x_40 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Elab_Term_throwErrorAt___rarg(x_11, x_43, x_5, x_19);
lean_dec(x_11);
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
}
else
{
uint8_t x_49; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
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
lean_dec(x_5);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_57 = lean_ctor_get(x_5, 0);
x_58 = lean_ctor_get(x_5, 1);
x_59 = lean_ctor_get(x_5, 2);
x_60 = lean_ctor_get(x_5, 3);
x_61 = lean_ctor_get(x_5, 4);
x_62 = lean_ctor_get(x_5, 5);
x_63 = lean_ctor_get(x_5, 6);
x_64 = lean_ctor_get(x_5, 7);
x_65 = lean_ctor_get(x_5, 8);
x_66 = lean_ctor_get(x_5, 9);
x_67 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
x_68 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 1);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 2);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_5);
lean_inc(x_11);
x_70 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_58);
lean_ctor_set(x_70, 2, x_59);
lean_ctor_set(x_70, 3, x_60);
lean_ctor_set(x_70, 4, x_61);
lean_ctor_set(x_70, 5, x_62);
lean_ctor_set(x_70, 6, x_63);
lean_ctor_set(x_70, 7, x_64);
lean_ctor_set(x_70, 8, x_65);
lean_ctor_set(x_70, 9, x_66);
lean_ctor_set(x_70, 10, x_11);
lean_ctor_set_uint8(x_70, sizeof(void*)*11, x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*11 + 1, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*11 + 2, x_69);
lean_inc(x_70);
lean_inc(x_11);
x_71 = l_Lean_Elab_Term_elabType(x_11, x_70, x_6);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_70);
x_74 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_72, x_70, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Name_eraseMacroScopes(x_75);
x_78 = l_Lean_Name_getString_x21(x_77);
lean_dec(x_77);
x_79 = l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
x_80 = lean_string_append(x_79, x_78);
lean_dec(x_78);
x_81 = lean_box(0);
x_82 = lean_name_mk_string(x_81, x_80);
x_83 = l___private_Lean_Elab_Structure_7__containsFieldName(x_3, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
lean_dec(x_11);
x_84 = l_Lean_Elab_Term_getEnv___rarg(x_76);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_75);
lean_inc(x_85);
lean_inc(x_82);
x_88 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2), 10, 7);
lean_closure_set(x_88, 0, x_1);
lean_closure_set(x_88, 1, x_82);
lean_closure_set(x_88, 2, x_3);
lean_closure_set(x_88, 3, x_85);
lean_closure_set(x_88, 4, x_75);
lean_closure_set(x_88, 5, x_2);
lean_closure_set(x_88, 6, x_4);
if (x_87 == 0)
{
uint8_t x_89; lean_object* x_90; 
lean_dec(x_85);
lean_dec(x_75);
x_89 = 0;
x_90 = l_Lean_Elab_Term_withLocalDecl___rarg(x_82, x_89, x_72, x_88, x_70, x_86);
return x_90;
}
else
{
uint8_t x_91; 
x_91 = lean_is_class(x_85, x_75);
if (x_91 == 0)
{
uint8_t x_92; lean_object* x_93; 
x_92 = 0;
x_93 = l_Lean_Elab_Term_withLocalDecl___rarg(x_82, x_92, x_72, x_88, x_70, x_86);
return x_93;
}
else
{
uint8_t x_94; lean_object* x_95; 
x_94 = 3;
x_95 = l_Lean_Elab_Term_withLocalDecl___rarg(x_82, x_94, x_72, x_88, x_70, x_86);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_96, 0, x_82);
x_97 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_98 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
x_99 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_100 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Elab_Term_throwErrorAt___rarg(x_11, x_100, x_70, x_76);
lean_dec(x_11);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
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
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_74, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_74, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_108 = x_74;
} else {
 lean_dec_ref(x_74);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_70);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = lean_ctor_get(x_71, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_71, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_112 = x_71;
} else {
 lean_dec_ref(x_71);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
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
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_109; 
x_109 = lean_ctor_get(x_1, 5);
lean_inc(x_109);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; 
x_110 = lean_box(0);
x_5 = x_110;
x_6 = x_4;
goto block_108;
}
else
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_3);
x_113 = l_Lean_Elab_Term_elabType(x_112, x_3, x_4);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
lean_inc(x_3);
lean_inc(x_2);
x_116 = l_Lean_Elab_Term_mkForall(x_2, x_114, x_3, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_ctor_set(x_109, 0, x_117);
x_5 = x_109;
x_6 = x_118;
goto block_108;
}
else
{
uint8_t x_119; 
lean_free_object(x_109);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_116);
if (x_119 == 0)
{
return x_116;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_116, 0);
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_116);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_109);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_113);
if (x_123 == 0)
{
return x_113;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_113, 0);
x_125 = lean_ctor_get(x_113, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_113);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_109, 0);
lean_inc(x_127);
lean_dec(x_109);
lean_inc(x_3);
x_128 = l_Lean_Elab_Term_elabType(x_127, x_3, x_4);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_3);
lean_inc(x_2);
x_131 = l_Lean_Elab_Term_mkForall(x_2, x_129, x_3, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_132);
x_5 = x_134;
x_6 = x_133;
goto block_108;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = lean_ctor_get(x_128, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_128, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_141 = x_128;
} else {
 lean_dec_ref(x_128);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
block_108:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 6);
lean_inc(x_7);
lean_dec(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = 1;
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_12);
x_14 = l_Lean_Elab_Term_elabTerm(x_12, x_5, x_13, x_3, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_mkLambda(x_2, x_15, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_3, 10);
lean_dec(x_21);
lean_ctor_set(x_3, 10, x_12);
lean_inc(x_5);
x_22 = l_Lean_Elab_Term_ensureHasType(x_5, x_18, x_3, x_19);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_7);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_22);
lean_ctor_set(x_7, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_5);
lean_ctor_set(x_28, 1, x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_free_object(x_7);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_22, 0);
x_32 = lean_ctor_get(x_22, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get(x_3, 1);
x_36 = lean_ctor_get(x_3, 2);
x_37 = lean_ctor_get(x_3, 3);
x_38 = lean_ctor_get(x_3, 4);
x_39 = lean_ctor_get(x_3, 5);
x_40 = lean_ctor_get(x_3, 6);
x_41 = lean_ctor_get(x_3, 7);
x_42 = lean_ctor_get(x_3, 8);
x_43 = lean_ctor_get(x_3, 9);
x_44 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
x_45 = lean_ctor_get_uint8(x_3, sizeof(void*)*11 + 1);
x_46 = lean_ctor_get_uint8(x_3, sizeof(void*)*11 + 2);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_3);
x_47 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 3, x_37);
lean_ctor_set(x_47, 4, x_38);
lean_ctor_set(x_47, 5, x_39);
lean_ctor_set(x_47, 6, x_40);
lean_ctor_set(x_47, 7, x_41);
lean_ctor_set(x_47, 8, x_42);
lean_ctor_set(x_47, 9, x_43);
lean_ctor_set(x_47, 10, x_12);
lean_ctor_set_uint8(x_47, sizeof(void*)*11, x_44);
lean_ctor_set_uint8(x_47, sizeof(void*)*11 + 1, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*11 + 2, x_46);
lean_inc(x_5);
x_48 = l_Lean_Elab_Term_ensureHasType(x_5, x_18, x_47, x_19);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
lean_ctor_set(x_7, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_7);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_7);
lean_dec(x_5);
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_56 = x_48;
} else {
 lean_dec_ref(x_48);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_17);
if (x_58 == 0)
{
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_17, 0);
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_17);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_14);
if (x_62 == 0)
{
return x_14;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_14, 0);
x_64 = lean_ctor_get(x_14, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_14);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_7, 0);
lean_inc(x_66);
lean_dec(x_7);
x_67 = 1;
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_66);
x_68 = l_Lean_Elab_Term_elabTerm(x_66, x_5, x_67, x_3, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_3);
x_71 = l_Lean_Elab_Term_mkLambda(x_2, x_69, x_3, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_3, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_3, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_3, 3);
lean_inc(x_77);
x_78 = lean_ctor_get(x_3, 4);
lean_inc(x_78);
x_79 = lean_ctor_get(x_3, 5);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 6);
lean_inc(x_80);
x_81 = lean_ctor_get(x_3, 7);
lean_inc(x_81);
x_82 = lean_ctor_get(x_3, 8);
lean_inc(x_82);
x_83 = lean_ctor_get(x_3, 9);
lean_inc(x_83);
x_84 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
x_85 = lean_ctor_get_uint8(x_3, sizeof(void*)*11 + 1);
x_86 = lean_ctor_get_uint8(x_3, sizeof(void*)*11 + 2);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 lean_ctor_release(x_3, 4);
 lean_ctor_release(x_3, 5);
 lean_ctor_release(x_3, 6);
 lean_ctor_release(x_3, 7);
 lean_ctor_release(x_3, 8);
 lean_ctor_release(x_3, 9);
 lean_ctor_release(x_3, 10);
 x_87 = x_3;
} else {
 lean_dec_ref(x_3);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 11, 3);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_74);
lean_ctor_set(x_88, 1, x_75);
lean_ctor_set(x_88, 2, x_76);
lean_ctor_set(x_88, 3, x_77);
lean_ctor_set(x_88, 4, x_78);
lean_ctor_set(x_88, 5, x_79);
lean_ctor_set(x_88, 6, x_80);
lean_ctor_set(x_88, 7, x_81);
lean_ctor_set(x_88, 8, x_82);
lean_ctor_set(x_88, 9, x_83);
lean_ctor_set(x_88, 10, x_66);
lean_ctor_set_uint8(x_88, sizeof(void*)*11, x_84);
lean_ctor_set_uint8(x_88, sizeof(void*)*11 + 1, x_85);
lean_ctor_set_uint8(x_88, sizeof(void*)*11 + 2, x_86);
lean_inc(x_5);
x_89 = l_Lean_Elab_Term_ensureHasType(x_5, x_72, x_88, x_73);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_5);
lean_ctor_set(x_94, 1, x_93);
if (lean_is_scalar(x_92)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_92;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_91);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_5);
x_96 = lean_ctor_get(x_89, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_98 = x_89;
} else {
 lean_dec_ref(x_89);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_3);
x_100 = lean_ctor_get(x_71, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_71, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_102 = x_71;
} else {
 lean_dec_ref(x_71);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_104 = lean_ctor_get(x_68, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_68, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_106 = x_68;
} else {
 lean_dec_ref(x_68);
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
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_18 = l___private_Lean_Elab_Structure_10__withFields___main___rarg(x_6, x_17, x_15, x_7, x_9, x_10);
return x_18;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid field, type expected");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' has been declared in parent structure");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("omit field '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' type to set default value");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_5, 2);
x_19 = lean_ctor_get(x_5, 3);
x_20 = lean_ctor_get(x_5, 4);
x_21 = lean_ctor_get(x_5, 5);
x_22 = lean_ctor_get(x_5, 6);
x_23 = lean_ctor_get(x_5, 7);
x_24 = lean_ctor_get(x_5, 8);
x_25 = lean_ctor_get(x_5, 9);
x_26 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 1);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 2);
x_29 = lean_ctor_get(x_5, 10);
lean_dec(x_29);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_ctor_set(x_5, 10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_30 = lean_ctor_get(x_10, 4);
lean_inc(x_30);
x_31 = l_Lean_Syntax_getArgs(x_30);
lean_dec(x_30);
lean_inc(x_10);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__1), 4, 1);
lean_closure_set(x_32, 0, x_10);
lean_inc(x_5);
x_33 = l_Lean_Elab_Term_elabBinders___rarg(x_31, x_32, x_5, x_6);
lean_dec(x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__3;
x_39 = l_Lean_Elab_Term_throwError___rarg(x_38, x_5, x_37);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_ctor_get(x_36, 0);
lean_inc(x_41);
lean_dec(x_36);
lean_inc(x_5);
x_42 = l_Lean_Elab_Term_inferType(x_41, x_5, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_inc(x_12);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed), 10, 7);
lean_closure_set(x_46, 0, x_10);
lean_closure_set(x_46, 1, x_12);
lean_closure_set(x_46, 2, x_35);
lean_closure_set(x_46, 3, x_3);
lean_closure_set(x_46, 4, x_2);
lean_closure_set(x_46, 5, x_1);
lean_closure_set(x_46, 6, x_4);
x_47 = l_Lean_Elab_Term_withLocalDecl___rarg(x_12, x_45, x_43, x_46, x_5, x_44);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_42);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_33, 1);
lean_inc(x_52);
lean_dec(x_33);
x_53 = lean_ctor_get(x_34, 1);
lean_inc(x_53);
lean_dec(x_34);
x_54 = lean_ctor_get(x_35, 0);
lean_inc(x_54);
lean_dec(x_35);
x_55 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_inc(x_12);
x_56 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed), 10, 7);
lean_closure_set(x_56, 0, x_10);
lean_closure_set(x_56, 1, x_12);
lean_closure_set(x_56, 2, x_53);
lean_closure_set(x_56, 3, x_3);
lean_closure_set(x_56, 4, x_2);
lean_closure_set(x_56, 5, x_1);
lean_closure_set(x_56, 6, x_4);
x_57 = l_Lean_Elab_Term_withLocalDecl___rarg(x_12, x_55, x_54, x_56, x_5, x_52);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_5);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_33);
if (x_58 == 0)
{
return x_33;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_33, 0);
x_60 = lean_ctor_get(x_33, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_33);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_14, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_63 = x_14;
} else {
 lean_dec_ref(x_14);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get_uint8(x_62, sizeof(void*)*4);
switch (x_64) {
case 0:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_65, 0, x_12);
x_66 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Elab_Term_throwError___rarg(x_69, x_5, x_6);
return x_70;
}
case 1:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_10, 6);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_72, 0, x_12);
x_73 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_74 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6;
x_76 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Elab_Term_throwError___rarg(x_76, x_5, x_6);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; 
x_78 = lean_ctor_get(x_62, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_62, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_62, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint8(x_62, sizeof(void*)*4 + 1);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 x_82 = x_62;
} else {
 lean_dec_ref(x_62);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_71, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 x_84 = x_71;
} else {
 lean_dec_ref(x_71);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_10, 4);
lean_inc(x_85);
x_86 = l_Lean_Syntax_getArgs(x_85);
lean_dec(x_85);
x_87 = l_Array_isEmpty___rarg(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
uint8_t x_146; 
x_146 = 1;
x_88 = x_146;
goto block_145;
}
else
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_10, 5);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
x_148 = 0;
x_88 = x_148;
goto block_145;
}
else
{
uint8_t x_149; 
lean_dec(x_147);
x_149 = 1;
x_88 = x_149;
goto block_145;
}
}
block_145:
{
uint8_t x_89; 
if (x_88 == 0)
{
uint8_t x_143; 
x_143 = 0;
x_89 = x_143;
goto block_142;
}
else
{
uint8_t x_144; 
x_144 = 1;
x_89 = x_144;
goto block_142;
}
block_142:
{
lean_object* x_90; 
if (x_89 == 0)
{
lean_dec(x_12);
lean_dec(x_10);
x_90 = x_6;
goto block_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_63);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_ctor_get(x_10, 5);
lean_inc(x_122);
lean_dec(x_10);
x_123 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_123, 0, x_12);
x_124 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9;
x_125 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12;
x_127 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = l_Lean_Syntax_inhabited;
x_129 = l_Option_get_x21___rarg___closed__3;
x_130 = lean_panic_fn(x_128, x_129);
x_131 = l_Lean_Elab_Term_throwErrorAt___rarg(x_130, x_127, x_5, x_6);
lean_dec(x_130);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
return x_131;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_131);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = lean_ctor_get(x_122, 0);
lean_inc(x_136);
lean_dec(x_122);
x_137 = l_Lean_Elab_Term_throwErrorAt___rarg(x_136, x_127, x_5, x_6);
lean_dec(x_136);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
block_121:
{
lean_object* x_91; 
lean_inc(x_5);
lean_inc(x_80);
x_91 = l_Lean_Elab_Term_inferType(x_80, x_5, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
if (lean_is_scalar(x_84)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_84;
}
lean_ctor_set(x_94, 0, x_92);
x_95 = 1;
lean_inc(x_5);
lean_inc(x_94);
lean_inc(x_83);
x_96 = l_Lean_Elab_Term_elabTerm(x_83, x_94, x_95, x_5, x_93);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_99, 0, x_16);
lean_ctor_set(x_99, 1, x_17);
lean_ctor_set(x_99, 2, x_18);
lean_ctor_set(x_99, 3, x_19);
lean_ctor_set(x_99, 4, x_20);
lean_ctor_set(x_99, 5, x_21);
lean_ctor_set(x_99, 6, x_22);
lean_ctor_set(x_99, 7, x_23);
lean_ctor_set(x_99, 8, x_24);
lean_ctor_set(x_99, 9, x_25);
lean_ctor_set(x_99, 10, x_83);
lean_ctor_set_uint8(x_99, sizeof(void*)*11, x_26);
lean_ctor_set_uint8(x_99, sizeof(void*)*11 + 1, x_27);
lean_ctor_set_uint8(x_99, sizeof(void*)*11 + 2, x_28);
x_100 = l_Lean_Elab_Term_ensureHasType(x_94, x_97, x_99, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
if (lean_is_scalar(x_63)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_63;
}
lean_ctor_set(x_103, 0, x_101);
if (lean_is_scalar(x_82)) {
 x_104 = lean_alloc_ctor(0, 4, 2);
} else {
 x_104 = x_82;
}
lean_ctor_set(x_104, 0, x_78);
lean_ctor_set(x_104, 1, x_79);
lean_ctor_set(x_104, 2, x_80);
lean_ctor_set(x_104, 3, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_64);
lean_ctor_set_uint8(x_104, sizeof(void*)*4 + 1, x_81);
x_105 = lean_array_push(x_3, x_104);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_2, x_106);
lean_dec(x_2);
x_2 = x_107;
x_3 = x_105;
x_6 = x_102;
goto _start;
}
else
{
uint8_t x_109; 
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_100);
if (x_109 == 0)
{
return x_100;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_100, 0);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_100);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_94);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_96);
if (x_113 == 0)
{
return x_96;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_96, 0);
x_115 = lean_ctor_get(x_96, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_96);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_91);
if (x_117 == 0)
{
return x_91;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_91, 0);
x_119 = lean_ctor_get(x_91, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_91);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
}
}
}
default: 
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_151 = l_unreachable_x21___rarg(x_150);
x_152 = lean_apply_2(x_151, x_5, x_6);
return x_152;
}
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; lean_object* x_166; 
x_153 = lean_ctor_get(x_5, 0);
x_154 = lean_ctor_get(x_5, 1);
x_155 = lean_ctor_get(x_5, 2);
x_156 = lean_ctor_get(x_5, 3);
x_157 = lean_ctor_get(x_5, 4);
x_158 = lean_ctor_get(x_5, 5);
x_159 = lean_ctor_get(x_5, 6);
x_160 = lean_ctor_get(x_5, 7);
x_161 = lean_ctor_get(x_5, 8);
x_162 = lean_ctor_get(x_5, 9);
x_163 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
x_164 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 1);
x_165 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 2);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_5);
lean_inc(x_162);
lean_inc(x_161);
lean_inc(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
x_166 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_166, 0, x_153);
lean_ctor_set(x_166, 1, x_154);
lean_ctor_set(x_166, 2, x_155);
lean_ctor_set(x_166, 3, x_156);
lean_ctor_set(x_166, 4, x_157);
lean_ctor_set(x_166, 5, x_158);
lean_ctor_set(x_166, 6, x_159);
lean_ctor_set(x_166, 7, x_160);
lean_ctor_set(x_166, 8, x_161);
lean_ctor_set(x_166, 9, x_162);
lean_ctor_set(x_166, 10, x_11);
lean_ctor_set_uint8(x_166, sizeof(void*)*11, x_163);
lean_ctor_set_uint8(x_166, sizeof(void*)*11 + 1, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*11 + 2, x_165);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
x_167 = lean_ctor_get(x_10, 4);
lean_inc(x_167);
x_168 = l_Lean_Syntax_getArgs(x_167);
lean_dec(x_167);
lean_inc(x_10);
x_169 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__1), 4, 1);
lean_closure_set(x_169, 0, x_10);
lean_inc(x_166);
x_170 = l_Lean_Elab_Term_elabBinders___rarg(x_168, x_169, x_166, x_6);
lean_dec(x_168);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
lean_dec(x_170);
x_175 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__3;
x_176 = l_Lean_Elab_Term_throwError___rarg(x_175, x_166, x_174);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_170, 1);
lean_inc(x_177);
lean_dec(x_170);
x_178 = lean_ctor_get(x_173, 0);
lean_inc(x_178);
lean_dec(x_173);
lean_inc(x_166);
x_179 = l_Lean_Elab_Term_inferType(x_178, x_166, x_177);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_inc(x_12);
x_183 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed), 10, 7);
lean_closure_set(x_183, 0, x_10);
lean_closure_set(x_183, 1, x_12);
lean_closure_set(x_183, 2, x_172);
lean_closure_set(x_183, 3, x_3);
lean_closure_set(x_183, 4, x_2);
lean_closure_set(x_183, 5, x_1);
lean_closure_set(x_183, 6, x_4);
x_184 = l_Lean_Elab_Term_withLocalDecl___rarg(x_12, x_182, x_180, x_183, x_166, x_181);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_166);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_ctor_get(x_179, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_179, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_187 = x_179;
} else {
 lean_dec_ref(x_179);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; 
x_189 = lean_ctor_get(x_170, 1);
lean_inc(x_189);
lean_dec(x_170);
x_190 = lean_ctor_get(x_171, 1);
lean_inc(x_190);
lean_dec(x_171);
x_191 = lean_ctor_get(x_172, 0);
lean_inc(x_191);
lean_dec(x_172);
x_192 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_inc(x_12);
x_193 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed), 10, 7);
lean_closure_set(x_193, 0, x_10);
lean_closure_set(x_193, 1, x_12);
lean_closure_set(x_193, 2, x_190);
lean_closure_set(x_193, 3, x_3);
lean_closure_set(x_193, 4, x_2);
lean_closure_set(x_193, 5, x_1);
lean_closure_set(x_193, 6, x_4);
x_194 = l_Lean_Elab_Term_withLocalDecl___rarg(x_12, x_192, x_191, x_193, x_166, x_189);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_166);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_170, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_170, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_197 = x_170;
} else {
 lean_dec_ref(x_170);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_199 = lean_ctor_get(x_14, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_200 = x_14;
} else {
 lean_dec_ref(x_14);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get_uint8(x_199, sizeof(void*)*4);
switch (x_201) {
case 0:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_202, 0, x_12);
x_203 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_204 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_206 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_Elab_Term_throwError___rarg(x_206, x_166, x_6);
return x_207;
}
case 1:
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_10, 6);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_209, 0, x_12);
x_210 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_211 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
x_212 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6;
x_213 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_Elab_Term_throwError___rarg(x_213, x_166, x_6);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; uint8_t x_225; 
x_215 = lean_ctor_get(x_199, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_199, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_199, 2);
lean_inc(x_217);
x_218 = lean_ctor_get_uint8(x_199, sizeof(void*)*4 + 1);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 x_219 = x_199;
} else {
 lean_dec_ref(x_199);
 x_219 = lean_box(0);
}
x_220 = lean_ctor_get(x_208, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 x_221 = x_208;
} else {
 lean_dec_ref(x_208);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_10, 4);
lean_inc(x_222);
x_223 = l_Lean_Syntax_getArgs(x_222);
lean_dec(x_222);
x_224 = l_Array_isEmpty___rarg(x_223);
lean_dec(x_223);
if (x_224 == 0)
{
uint8_t x_283; 
x_283 = 1;
x_225 = x_283;
goto block_282;
}
else
{
lean_object* x_284; 
x_284 = lean_ctor_get(x_10, 5);
lean_inc(x_284);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
x_285 = 0;
x_225 = x_285;
goto block_282;
}
else
{
uint8_t x_286; 
lean_dec(x_284);
x_286 = 1;
x_225 = x_286;
goto block_282;
}
}
block_282:
{
uint8_t x_226; 
if (x_225 == 0)
{
uint8_t x_280; 
x_280 = 0;
x_226 = x_280;
goto block_279;
}
else
{
uint8_t x_281; 
x_281 = 1;
x_226 = x_281;
goto block_279;
}
block_279:
{
lean_object* x_227; 
if (x_226 == 0)
{
lean_dec(x_12);
lean_dec(x_10);
x_227 = x_6;
goto block_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_200);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_259 = lean_ctor_get(x_10, 5);
lean_inc(x_259);
lean_dec(x_10);
x_260 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_260, 0, x_12);
x_261 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9;
x_262 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_260);
x_263 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12;
x_264 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_265 = l_Lean_Syntax_inhabited;
x_266 = l_Option_get_x21___rarg___closed__3;
x_267 = lean_panic_fn(x_265, x_266);
x_268 = l_Lean_Elab_Term_throwErrorAt___rarg(x_267, x_264, x_166, x_6);
lean_dec(x_267);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_271 = x_268;
} else {
 lean_dec_ref(x_268);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_259, 0);
lean_inc(x_273);
lean_dec(x_259);
x_274 = l_Lean_Elab_Term_throwErrorAt___rarg(x_273, x_264, x_166, x_6);
lean_dec(x_273);
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_277 = x_274;
} else {
 lean_dec_ref(x_274);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
block_258:
{
lean_object* x_228; 
lean_inc(x_166);
lean_inc(x_217);
x_228 = l_Lean_Elab_Term_inferType(x_217, x_166, x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
if (lean_is_scalar(x_221)) {
 x_231 = lean_alloc_ctor(1, 1, 0);
} else {
 x_231 = x_221;
}
lean_ctor_set(x_231, 0, x_229);
x_232 = 1;
lean_inc(x_166);
lean_inc(x_231);
lean_inc(x_220);
x_233 = l_Lean_Elab_Term_elabTerm(x_220, x_231, x_232, x_166, x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_236, 0, x_153);
lean_ctor_set(x_236, 1, x_154);
lean_ctor_set(x_236, 2, x_155);
lean_ctor_set(x_236, 3, x_156);
lean_ctor_set(x_236, 4, x_157);
lean_ctor_set(x_236, 5, x_158);
lean_ctor_set(x_236, 6, x_159);
lean_ctor_set(x_236, 7, x_160);
lean_ctor_set(x_236, 8, x_161);
lean_ctor_set(x_236, 9, x_162);
lean_ctor_set(x_236, 10, x_220);
lean_ctor_set_uint8(x_236, sizeof(void*)*11, x_163);
lean_ctor_set_uint8(x_236, sizeof(void*)*11 + 1, x_164);
lean_ctor_set_uint8(x_236, sizeof(void*)*11 + 2, x_165);
x_237 = l_Lean_Elab_Term_ensureHasType(x_231, x_234, x_236, x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
if (lean_is_scalar(x_200)) {
 x_240 = lean_alloc_ctor(1, 1, 0);
} else {
 x_240 = x_200;
}
lean_ctor_set(x_240, 0, x_238);
if (lean_is_scalar(x_219)) {
 x_241 = lean_alloc_ctor(0, 4, 2);
} else {
 x_241 = x_219;
}
lean_ctor_set(x_241, 0, x_215);
lean_ctor_set(x_241, 1, x_216);
lean_ctor_set(x_241, 2, x_217);
lean_ctor_set(x_241, 3, x_240);
lean_ctor_set_uint8(x_241, sizeof(void*)*4, x_201);
lean_ctor_set_uint8(x_241, sizeof(void*)*4 + 1, x_218);
x_242 = lean_array_push(x_3, x_241);
x_243 = lean_unsigned_to_nat(1u);
x_244 = lean_nat_add(x_2, x_243);
lean_dec(x_2);
x_2 = x_244;
x_3 = x_242;
x_5 = x_166;
x_6 = x_239;
goto _start;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_200);
lean_dec(x_166);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_237, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_237, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_248 = x_237;
} else {
 lean_dec_ref(x_237);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_231);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_200);
lean_dec(x_166);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_ctor_get(x_233, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_233, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_252 = x_233;
} else {
 lean_dec_ref(x_233);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_200);
lean_dec(x_166);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_254 = lean_ctor_get(x_228, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_228, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_256 = x_228;
} else {
 lean_dec_ref(x_228);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
}
}
}
}
default: 
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_287 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_288 = l_unreachable_x21___rarg(x_287);
x_289 = lean_apply_2(x_288, x_166, x_6);
return x_289;
}
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_10__withFields___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_10__withFields___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_10__withFields___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_10__withFields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___rarg), 6, 0);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__getResultUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected structure resulting type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__getResultUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__getResultUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_11__getResultUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_11__getResultUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_13 = l___private_Lean_Elab_Structure_11__getResultUniverse___closed__3;
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l___private_Lean_Elab_Structure_12__removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_inc(x_4);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1(x_2, x_2, x_6, x_7, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_4);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2(x_3, x_3, x_6, x_9, x_4, x_10);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_12__removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_12__removeUnused(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_13__withUsed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l___private_Lean_Elab_Structure_12__removeUnused(x_1, x_2, x_3, x_5, x_6);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_26 = lean_ctor_get(x_5, 1);
x_27 = lean_ctor_get(x_5, 2);
x_28 = lean_ctor_get(x_5, 3);
x_29 = lean_ctor_get(x_5, 4);
x_30 = lean_ctor_get(x_5, 5);
x_31 = lean_ctor_get(x_5, 6);
x_32 = lean_ctor_get(x_5, 7);
x_33 = lean_ctor_get(x_5, 8);
x_34 = lean_ctor_get(x_5, 9);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 1);
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 2);
x_38 = lean_ctor_get(x_5, 10);
lean_inc(x_38);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_5);
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_10, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_10, 4);
lean_inc(x_41);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 lean_ctor_release(x_10, 2);
 lean_ctor_release(x_10, 3);
 lean_ctor_release(x_10, 4);
 x_42 = x_10;
} else {
 lean_dec_ref(x_10);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_12);
lean_ctor_set(x_43, 2, x_13);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_41);
x_44 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_26);
lean_ctor_set(x_44, 2, x_27);
lean_ctor_set(x_44, 3, x_28);
lean_ctor_set(x_44, 4, x_29);
lean_ctor_set(x_44, 5, x_30);
lean_ctor_set(x_44, 6, x_31);
lean_ctor_set(x_44, 7, x_32);
lean_ctor_set(x_44, 8, x_33);
lean_ctor_set(x_44, 9, x_34);
lean_ctor_set(x_44, 10, x_38);
lean_ctor_set_uint8(x_44, sizeof(void*)*11, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*11 + 1, x_36);
lean_ctor_set_uint8(x_44, sizeof(void*)*11 + 2, x_37);
x_45 = lean_apply_3(x_4, x_14, x_44, x_11);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
return x_7;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_13__withUsed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_13__withUsed___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_13__withUsed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_13__withUsed___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_14__levelMVarToParamFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_1, x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
lean_dec(x_2);
lean_inc(x_4);
x_14 = l___private_Lean_Elab_Structure_14__levelMVarToParamFVar(x_11, x_3, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_2 = x_13;
x_3 = x_17;
x_5 = x_16;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_15__levelMVarToParamFVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_21 = l___private_Lean_Elab_Structure_14__levelMVarToParamFVar(x_17, x_3, x_4, x_5);
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
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = x_3;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamAux___spec__1), 5, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_7);
lean_inc(x_5);
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(x_1, x_8, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_5);
x_14 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(x_2, x_8, x_13, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = x_9;
x_19 = lean_apply_3(x_18, x_17, x_5, x_16);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_5);
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
lean_dec(x_9);
lean_dec(x_5);
x_24 = !lean_is_exclusive(x_10);
if (x_24 == 0)
{
return x_10;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
x_26 = lean_ctor_get(x_10, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_10);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_16__levelMVarToParamAux(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = l___private_Lean_Elab_Structure_16__levelMVarToParamAux(x_1, x_2, x_3, x_6, x_4, x_5);
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
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_17__levelMVarToParam(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l___private_Lean_Elab_Structure_18__collectUniversesFromFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_empty___closed__1;
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_3, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Structure_18__collectUniversesFromFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_18__collectUniversesFromFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compute resulting universe level of structure, provide universe explicitly");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l___private_Lean_Elab_Structure_11__getResultUniverse(x_2, x_3, x_4);
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
x_12 = l___private_Lean_Elab_Structure_18__collectUniversesFromFields(x_10, x_9, x_1, x_3, x_7);
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
x_24 = l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__3;
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
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_19__updateResultingUniverse(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar(x_4, x_10, x_5, x_6);
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
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(x_1, x_1, x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_14 = l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar(x_4, x_13, x_5, x_6);
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
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Meta_DepElim_getUnusedLevelParam___closed__1;
lean_inc(x_4);
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(x_1, x_1, x_6, x_7, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_4);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(x_2, x_2, x_6, x_9, x_4, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1(x_3, x_3, x_6, x_12, x_4, x_13);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_23__addCtorFields___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_mkOptionalNode___closed__2;
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_expr_abstract(x_3, x_17);
lean_dec(x_17);
lean_dec(x_3);
x_19 = lean_ctor_get_uint8(x_11, sizeof(void*)*4);
lean_dec(x_11);
switch (x_19) {
case 0:
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lean_LocalDecl_userName(x_14);
x_21 = l_Lean_LocalDecl_binderInfo(x_14);
x_22 = l_Lean_LocalDecl_type(x_14);
lean_dec(x_14);
x_23 = l_Lean_mkForall(x_20, x_21, x_22, x_18);
lean_dec(x_20);
x_2 = x_9;
x_3 = x_23;
x_5 = x_15;
goto _start;
}
case 1:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_LocalDecl_value(x_14);
lean_dec(x_14);
x_26 = lean_expr_instantiate1(x_18, x_25);
lean_dec(x_25);
lean_dec(x_18);
x_2 = x_9;
x_3 = x_26;
x_5 = x_15;
goto _start;
}
default: 
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_28 = l_Lean_LocalDecl_userName(x_14);
x_29 = l_Lean_mkHole___closed__3;
x_30 = l_Lean_Name_appendBefore(x_28, x_29);
x_31 = l_Lean_LocalDecl_binderInfo(x_14);
x_32 = l_Lean_LocalDecl_type(x_14);
lean_dec(x_14);
x_33 = l_Lean_mkForall(x_30, x_31, x_32, x_18);
lean_dec(x_30);
x_2 = x_9;
x_3 = x_33;
x_5 = x_15;
goto _start;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
lean_dec(x_4);
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_3);
lean_ctor_set(x_39, 1, x_5);
return x_39;
}
}
}
lean_object* l___private_Lean_Elab_Structure_23__addCtorFields___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_23__addCtorFields___main(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_23__addCtorFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_23__addCtorFields___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_23__addCtorFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_23__addCtorFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_24__mkCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_5, 10);
lean_dec(x_15);
lean_ctor_set(x_5, 10, x_7);
lean_inc(x_5);
x_16 = l___private_Lean_Elab_Structure_23__addCtorFields___main(x_4, x_13, x_12, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_5);
lean_inc(x_3);
x_19 = l_Lean_Elab_Term_mkForall(x_3, x_17, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Elab_Term_instantiateMVars(x_20, x_5, x_21);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_array_get_size(x_3);
lean_dec(x_3);
x_26 = lean_ctor_get(x_1, 9);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*4);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 3);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = l_Lean_Expr_inferImplicit___main(x_24, x_25, x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_22, 0, x_31);
return x_22;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_26, 3);
lean_inc(x_32);
lean_dec(x_26);
x_33 = 0;
x_34 = l_Lean_Expr_inferImplicit___main(x_24, x_25, x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_22, 0, x_35);
return x_22;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_array_get_size(x_3);
lean_dec(x_3);
x_39 = lean_ctor_get(x_1, 9);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*4);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_39, 3);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 1;
x_43 = l_Lean_Expr_inferImplicit___main(x_36, x_38, x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
return x_45;
}
else
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_39, 3);
lean_inc(x_46);
lean_dec(x_39);
x_47 = 0;
x_48 = l_Lean_Expr_inferImplicit___main(x_36, x_38, x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_37);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_19);
if (x_51 == 0)
{
return x_19;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_19, 0);
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_19);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_16);
if (x_55 == 0)
{
return x_16;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_16, 0);
x_57 = lean_ctor_get(x_16, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_16);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
x_59 = lean_ctor_get(x_5, 0);
x_60 = lean_ctor_get(x_5, 1);
x_61 = lean_ctor_get(x_5, 2);
x_62 = lean_ctor_get(x_5, 3);
x_63 = lean_ctor_get(x_5, 4);
x_64 = lean_ctor_get(x_5, 5);
x_65 = lean_ctor_get(x_5, 6);
x_66 = lean_ctor_get(x_5, 7);
x_67 = lean_ctor_get(x_5, 8);
x_68 = lean_ctor_get(x_5, 9);
x_69 = lean_ctor_get_uint8(x_5, sizeof(void*)*11);
x_70 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 1);
x_71 = lean_ctor_get_uint8(x_5, sizeof(void*)*11 + 2);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_5);
x_72 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_72, 0, x_59);
lean_ctor_set(x_72, 1, x_60);
lean_ctor_set(x_72, 2, x_61);
lean_ctor_set(x_72, 3, x_62);
lean_ctor_set(x_72, 4, x_63);
lean_ctor_set(x_72, 5, x_64);
lean_ctor_set(x_72, 6, x_65);
lean_ctor_set(x_72, 7, x_66);
lean_ctor_set(x_72, 8, x_67);
lean_ctor_set(x_72, 9, x_68);
lean_ctor_set(x_72, 10, x_7);
lean_ctor_set_uint8(x_72, sizeof(void*)*11, x_69);
lean_ctor_set_uint8(x_72, sizeof(void*)*11 + 1, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*11 + 2, x_71);
lean_inc(x_72);
x_73 = l___private_Lean_Elab_Structure_23__addCtorFields___main(x_4, x_13, x_12, x_72, x_6);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_72);
lean_inc(x_3);
x_76 = l_Lean_Elab_Term_mkForall(x_3, x_74, x_72, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l_Lean_Elab_Term_instantiateMVars(x_77, x_72, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_array_get_size(x_3);
lean_dec(x_3);
x_84 = lean_ctor_get(x_1, 9);
lean_inc(x_84);
lean_dec(x_1);
x_85 = lean_ctor_get_uint8(x_84, sizeof(void*)*4);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_84, 3);
lean_inc(x_86);
lean_dec(x_84);
x_87 = 1;
x_88 = l_Lean_Expr_inferImplicit___main(x_80, x_83, x_87);
lean_dec(x_83);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_81);
return x_90;
}
else
{
lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_84, 3);
lean_inc(x_91);
lean_dec(x_84);
x_92 = 0;
x_93 = l_Lean_Expr_inferImplicit___main(x_80, x_83, x_92);
lean_dec(x_83);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
if (lean_is_scalar(x_82)) {
 x_95 = lean_alloc_ctor(0, 2, 0);
} else {
 x_95 = x_82;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_81);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_72);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_ctor_get(x_76, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_76, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_98 = x_76;
} else {
 lean_dec_ref(x_76);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_72);
lean_dec(x_3);
lean_dec(x_1);
x_100 = lean_ctor_get(x_73, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_73, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_102 = x_73;
} else {
 lean_dec_ref(x_73);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_24__mkCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_24__mkCtor(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__2(lean_object* x_1) {
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
x_9 = l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__2(x_5);
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
x_15 = l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__2(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_filterMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__4(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__4(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__4(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_default");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__2;
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
x_9 = l___private_Lean_Elab_Structure_17__levelMVarToParam(x_6, x_1, x_2, x_7, x_8);
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
x_99 = l___private_Lean_Elab_Structure_19__updateResultingUniverse(x_10, x_5, x_7, x_11);
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
x_14 = l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure(x_6, x_1, x_10, x_7, x_13);
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
x_27 = l___private_Lean_Elab_Structure_24__mkCtor(x_3, x_24, x_26, x_10, x_7, x_16);
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
x_45 = l_Array_filterAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__1(x_10, x_25, x_25);
x_46 = l_Array_toList___rarg(x_45);
lean_dec(x_45);
x_47 = l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__2(x_46);
lean_inc(x_7);
lean_inc(x_10);
x_48 = l_Array_filterMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__3(x_10, x_25, x_25, x_7, x_35);
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
x_52 = l_List_map___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__4(x_51);
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
x_62 = l_Array_filterAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__5(x_10, x_25, x_25);
x_63 = x_62;
x_64 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6), 4, 2);
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
x_69 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__7(x_3, x_6, x_26, x_25, x_57);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_3);
x_70 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__8(x_10, x_10, x_25, x_69);
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
x_74 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__7(x_3, x_6, x_26, x_25, x_57);
lean_dec(x_26);
lean_dec(x_6);
lean_dec(x_3);
x_75 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__8(x_10, x_10, x_25, x_74);
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
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l___private_Lean_Elab_Structure_11__getResultUniverse(x_1, x_5, x_10);
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
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_25__elabStructureView___lambda__1___boxed), 8, 5);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_4);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_15);
lean_closure_set(x_18, 4, x_1);
x_19 = l___private_Lean_Elab_Structure_13__withUsed___rarg(x_17, x_3, x_4, x_18, x_5, x_16);
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
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 10);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_25__elabStructureView___lambda__2), 6, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Elab_Structure_10__withFields___main___rarg(x_7, x_9, x_4, x_8, x_5, x_6);
return x_10;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_25__elabStructureView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected Type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_25__elabStructureView___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_25__elabStructureView___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_25__elabStructureView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_25__elabStructureView___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Elab_Structure_4__validStructType(x_7);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_25__elabStructureView___lambda__3), 6, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_4);
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_12 = l___private_Lean_Elab_Structure_25__elabStructureView___closed__3;
x_13 = l_Lean_Elab_Term_throwErrorAt___rarg(x_5, x_12, x_2, x_8);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 10);
lean_dec(x_19);
lean_ctor_set(x_2, 10, x_10);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_empty___closed__1;
x_22 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_1, x_20, x_21, x_11, x_2, x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
x_27 = lean_ctor_get(x_2, 4);
x_28 = lean_ctor_get(x_2, 5);
x_29 = lean_ctor_get(x_2, 6);
x_30 = lean_ctor_get(x_2, 7);
x_31 = lean_ctor_get(x_2, 8);
x_32 = lean_ctor_get(x_2, 9);
x_33 = lean_ctor_get_uint8(x_2, sizeof(void*)*11);
x_34 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 1);
x_35 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 2);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 11, 3);
lean_ctor_set(x_36, 0, x_23);
lean_ctor_set(x_36, 1, x_24);
lean_ctor_set(x_36, 2, x_25);
lean_ctor_set(x_36, 3, x_26);
lean_ctor_set(x_36, 4, x_27);
lean_ctor_set(x_36, 5, x_28);
lean_ctor_set(x_36, 6, x_29);
lean_ctor_set(x_36, 7, x_30);
lean_ctor_set(x_36, 8, x_31);
lean_ctor_set(x_36, 9, x_32);
lean_ctor_set(x_36, 10, x_10);
lean_ctor_set_uint8(x_36, sizeof(void*)*11, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*11 + 1, x_34);
lean_ctor_set_uint8(x_36, sizeof(void*)*11 + 2, x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_empty___closed__1;
x_39 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_1, x_37, x_38, x_11, x_36, x_8);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_6);
if (x_40 == 0)
{
return x_6;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_6, 0);
x_42 = lean_ctor_get(x_6, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_6);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__8(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Structure_25__elabStructureView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l___private_Lean_Elab_Structure_25__elabStructureView___lambda__1(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_26__mkProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Elab_Structure_27__addProjections(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l_Lean_Elab_Command_getEnv(x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_mk_projections(x_8, x_2, x_3, x_4);
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
x_14 = l_Lean_Elab_Command_throwError___rarg(x_1, x_13, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Lean_Elab_Command_setEnv(x_15, x_5, x_9);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_27__addProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l___private_Lean_Elab_Structure_27__addProjections(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_28__mkAuxConstructions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_8 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
lean_inc(x_5);
x_9 = l_Lean_Environment_contains(x_5, x_8);
x_10 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_5);
x_11 = l_Lean_Environment_contains(x_5, x_10);
x_12 = l_Lean_Expr_heq_x3f___closed__2;
x_13 = l_Lean_Environment_contains(x_5, x_12);
lean_inc(x_2);
x_14 = l___private_Lean_Elab_Command_2__getState(x_2, x_6);
if (x_9 == 0)
{
uint8_t x_150; 
x_150 = 0;
x_15 = x_150;
goto block_149;
}
else
{
uint8_t x_151; 
x_151 = 1;
x_15 = x_151;
goto block_149;
}
block_149:
{
uint8_t x_16; 
if (x_9 == 0)
{
uint8_t x_147; 
x_147 = 0;
x_16 = x_147;
goto block_146;
}
else
{
if (x_11 == 0)
{
uint8_t x_148; 
x_148 = 0;
x_16 = x_148;
goto block_146;
}
else
{
x_16 = x_13;
goto block_146;
}
}
block_146:
{
uint8_t x_17; 
if (x_16 == 0)
{
uint8_t x_144; 
x_144 = 0;
x_17 = x_144;
goto block_143;
}
else
{
uint8_t x_145; 
x_145 = 1;
x_17 = x_145;
goto block_143;
}
block_143:
{
lean_object* x_18; 
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_14, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_14, 1);
lean_inc(x_61);
lean_dec(x_14);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_mk_rec_on(x_63, x_1);
lean_ctor_set(x_60, 0, x_64);
lean_inc(x_2);
x_65 = l___private_Lean_Elab_Command_3__setState(x_60, x_2, x_61);
if (lean_obj_tag(x_65) == 0)
{
if (x_15 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_18 = x_66;
goto block_59;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_2);
x_68 = l___private_Lean_Elab_Command_2__getState(x_2, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_mk_cases_on(x_72, x_1);
lean_ctor_set(x_69, 0, x_73);
lean_inc(x_2);
x_74 = l___private_Lean_Elab_Command_3__setState(x_69, x_2, x_70);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_18 = x_75;
goto block_59;
}
else
{
uint8_t x_76; 
lean_dec(x_7);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_74);
if (x_76 == 0)
{
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_74, 0);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_74);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
x_82 = lean_ctor_get(x_69, 2);
x_83 = lean_ctor_get(x_69, 3);
x_84 = lean_ctor_get(x_69, 4);
x_85 = lean_ctor_get(x_69, 5);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
x_86 = lean_mk_cases_on(x_80, x_1);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set(x_87, 4, x_84);
lean_ctor_set(x_87, 5, x_85);
lean_inc(x_2);
x_88 = l___private_Lean_Elab_Command_3__setState(x_87, x_2, x_70);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_18 = x_89;
goto block_59;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_7);
lean_dec(x_2);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_92 = x_88;
} else {
 lean_dec_ref(x_88);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_7);
lean_dec(x_2);
x_94 = !lean_is_exclusive(x_68);
if (x_94 == 0)
{
return x_68;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_68, 0);
x_96 = lean_ctor_get(x_68, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_68);
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
uint8_t x_98; 
lean_dec(x_7);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_65);
if (x_98 == 0)
{
return x_65;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_65, 0);
x_100 = lean_ctor_get(x_65, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_65);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_60, 0);
x_103 = lean_ctor_get(x_60, 1);
x_104 = lean_ctor_get(x_60, 2);
x_105 = lean_ctor_get(x_60, 3);
x_106 = lean_ctor_get(x_60, 4);
x_107 = lean_ctor_get(x_60, 5);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_60);
x_108 = lean_mk_rec_on(x_102, x_1);
x_109 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_109, 2, x_104);
lean_ctor_set(x_109, 3, x_105);
lean_ctor_set(x_109, 4, x_106);
lean_ctor_set(x_109, 5, x_107);
lean_inc(x_2);
x_110 = l___private_Lean_Elab_Command_3__setState(x_109, x_2, x_61);
if (lean_obj_tag(x_110) == 0)
{
if (x_15 == 0)
{
lean_object* x_111; 
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_18 = x_111;
goto block_59;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_2);
x_113 = l___private_Lean_Elab_Command_2__getState(x_2, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 4);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 5);
lean_inc(x_121);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 lean_ctor_release(x_114, 5);
 x_122 = x_114;
} else {
 lean_dec_ref(x_114);
 x_122 = lean_box(0);
}
x_123 = lean_mk_cases_on(x_116, x_1);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 6, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_117);
lean_ctor_set(x_124, 2, x_118);
lean_ctor_set(x_124, 3, x_119);
lean_ctor_set(x_124, 4, x_120);
lean_ctor_set(x_124, 5, x_121);
lean_inc(x_2);
x_125 = l___private_Lean_Elab_Command_3__setState(x_124, x_2, x_115);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_18 = x_126;
goto block_59;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_7);
lean_dec(x_2);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_129 = x_125;
} else {
 lean_dec_ref(x_125);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_7);
lean_dec(x_2);
x_131 = lean_ctor_get(x_113, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_113, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_133 = x_113;
} else {
 lean_dec_ref(x_113);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_7);
lean_dec(x_2);
x_135 = lean_ctor_get(x_110, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_110, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_137 = x_110;
} else {
 lean_dec_ref(x_110);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_7);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_14);
if (x_139 == 0)
{
return x_14;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_14, 0);
x_141 = lean_ctor_get(x_14, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_14);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
block_59:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_19 = lean_box(0);
if (lean_is_scalar(x_7)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_7;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_7);
lean_inc(x_2);
x_21 = l___private_Lean_Elab_Command_2__getState(x_2, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_mk_no_confusion(x_25, x_1);
lean_ctor_set(x_22, 0, x_26);
x_27 = l___private_Lean_Elab_Command_3__setState(x_22, x_2, x_23);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
x_40 = lean_ctor_get(x_22, 2);
x_41 = lean_ctor_get(x_22, 3);
x_42 = lean_ctor_get(x_22, 4);
x_43 = lean_ctor_get(x_22, 5);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
x_44 = lean_mk_no_confusion(x_38, x_1);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_42);
lean_ctor_set(x_45, 5, x_43);
x_46 = l___private_Lean_Elab_Command_3__setState(x_45, x_2, x_23);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_53 = x_46;
} else {
 lean_dec_ref(x_46);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_21);
if (x_55 == 0)
{
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_2);
x_152 = !lean_is_exclusive(x_4);
if (x_152 == 0)
{
return x_4;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_4, 0);
x_154 = lean_ctor_get(x_4, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_4);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_28__mkAuxConstructions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Structure_28__mkAuxConstructions(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_29__addDefaults___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 4);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
x_20 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_13, 4, x_20);
x_21 = l_Lean_Meta_mkId(x_16, x_19, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_3);
x_24 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_23, x_18);
x_25 = 1;
lean_inc(x_3);
lean_inc(x_14);
x_26 = l_Lean_Elab_Term_mkAuxDefinition(x_14, x_15, x_22, x_25, x_3, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = 0;
x_33 = lean_set_reducibility_status(x_31, x_14, x_32);
lean_ctor_set(x_29, 0, x_33);
x_2 = x_11;
x_4 = x_27;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
x_37 = lean_ctor_get(x_29, 2);
x_38 = lean_ctor_get(x_29, 3);
x_39 = lean_ctor_get(x_29, 4);
x_40 = lean_ctor_get(x_29, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_41 = 0;
x_42 = lean_set_reducibility_status(x_35, x_14, x_41);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_40);
lean_ctor_set(x_27, 0, x_43);
x_2 = x_11;
x_4 = x_27;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_45 = lean_ctor_get(x_27, 0);
x_46 = lean_ctor_get(x_27, 1);
x_47 = lean_ctor_get(x_27, 2);
x_48 = lean_ctor_get(x_27, 3);
x_49 = lean_ctor_get(x_27, 4);
x_50 = lean_ctor_get(x_27, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_27);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_45, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_45, 3);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 4);
lean_inc(x_55);
x_56 = lean_ctor_get(x_45, 5);
lean_inc(x_56);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 lean_ctor_release(x_45, 4);
 lean_ctor_release(x_45, 5);
 x_57 = x_45;
} else {
 lean_dec_ref(x_45);
 x_57 = lean_box(0);
}
x_58 = 0;
x_59 = lean_set_reducibility_status(x_51, x_14, x_58);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(0, 6, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_52);
lean_ctor_set(x_60, 2, x_53);
lean_ctor_set(x_60, 3, x_54);
lean_ctor_set(x_60, 4, x_55);
lean_ctor_set(x_60, 5, x_56);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_46);
lean_ctor_set(x_61, 2, x_47);
lean_ctor_set(x_61, 3, x_48);
lean_ctor_set(x_61, 4, x_49);
lean_ctor_set(x_61, 5, x_50);
x_2 = x_11;
x_4 = x_61;
goto _start;
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_26);
if (x_63 == 0)
{
return x_26;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_26, 0);
x_65 = lean_ctor_get(x_26, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_26);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
x_67 = !lean_is_exclusive(x_21);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_21, 0);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_3);
x_70 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_68);
x_71 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_69, x_18);
lean_ctor_set(x_21, 1, x_71);
lean_ctor_set(x_21, 0, x_70);
return x_21;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_21, 0);
x_73 = lean_ctor_get(x_21, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_21);
lean_inc(x_3);
x_74 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_72);
x_75 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_73, x_18);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_13, 0);
x_78 = lean_ctor_get(x_13, 1);
x_79 = lean_ctor_get(x_13, 2);
x_80 = lean_ctor_get(x_13, 3);
x_81 = lean_ctor_get(x_13, 4);
x_82 = lean_ctor_get(x_13, 5);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_13);
x_83 = lean_ctor_get(x_3, 0);
lean_inc(x_83);
x_84 = l_Lean_TraceState_Inhabited___closed__1;
x_85 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_78);
lean_ctor_set(x_85, 2, x_79);
lean_ctor_set(x_85, 3, x_80);
lean_ctor_set(x_85, 4, x_84);
lean_ctor_set(x_85, 5, x_82);
x_86 = l_Lean_Meta_mkId(x_16, x_83, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_3);
x_89 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_88, x_81);
x_90 = 1;
lean_inc(x_3);
lean_inc(x_14);
x_91 = l_Lean_Elab_Term_mkAuxDefinition(x_14, x_15, x_87, x_90, x_3, x_89);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_92, 2);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 3);
lean_inc(x_96);
x_97 = lean_ctor_get(x_92, 4);
lean_inc(x_97);
x_98 = lean_ctor_get(x_92, 5);
lean_inc(x_98);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 lean_ctor_release(x_92, 5);
 x_99 = x_92;
} else {
 lean_dec_ref(x_92);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_93, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_93, 2);
lean_inc(x_102);
x_103 = lean_ctor_get(x_93, 3);
lean_inc(x_103);
x_104 = lean_ctor_get(x_93, 4);
lean_inc(x_104);
x_105 = lean_ctor_get(x_93, 5);
lean_inc(x_105);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 lean_ctor_release(x_93, 2);
 lean_ctor_release(x_93, 3);
 lean_ctor_release(x_93, 4);
 lean_ctor_release(x_93, 5);
 x_106 = x_93;
} else {
 lean_dec_ref(x_93);
 x_106 = lean_box(0);
}
x_107 = 0;
x_108 = lean_set_reducibility_status(x_100, x_14, x_107);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 6, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_101);
lean_ctor_set(x_109, 2, x_102);
lean_ctor_set(x_109, 3, x_103);
lean_ctor_set(x_109, 4, x_104);
lean_ctor_set(x_109, 5, x_105);
if (lean_is_scalar(x_99)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_99;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_94);
lean_ctor_set(x_110, 2, x_95);
lean_ctor_set(x_110, 3, x_96);
lean_ctor_set(x_110, 4, x_97);
lean_ctor_set(x_110, 5, x_98);
x_2 = x_11;
x_4 = x_110;
goto _start;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
x_112 = lean_ctor_get(x_91, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_91, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_114 = x_91;
} else {
 lean_dec_ref(x_91);
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
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
x_116 = lean_ctor_get(x_86, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_86, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_118 = x_86;
} else {
 lean_dec_ref(x_86);
 x_118 = lean_box(0);
}
lean_inc(x_3);
x_119 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_116);
x_120 = l___private_Lean_Elab_Term_3__fromMetaState(x_3, x_4, x_117, x_81);
if (lean_is_scalar(x_118)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_118;
}
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_29__addDefaults___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Elab_Term_setMCtx(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_29__addDefaults___spec__1(x_2, x_7, x_3, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_29__addDefaults___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_box(0);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_29__addDefaults___rarg___lambda__1___boxed), 4, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
lean_inc(x_5);
x_9 = l___private_Lean_Elab_Command_2__getState(x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_Command_6__mkTermContext(x_5, x_10, x_7);
x_13 = l___private_Lean_Elab_Command_7__mkTermState(x_10);
lean_dec(x_10);
x_14 = l_Lean_Elab_Term_withLocalContext___rarg(x_2, x_3, x_8, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
x_17 = l___private_Lean_Elab_Command_2__getState(x_5, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 3);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_16, 2);
lean_inc(x_23);
lean_dec(x_16);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_19, 5);
lean_dec(x_25);
x_26 = lean_ctor_get(x_19, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_19, 0);
lean_dec(x_27);
lean_ctor_set(x_19, 5, x_22);
lean_ctor_set(x_19, 1, x_23);
lean_ctor_set(x_19, 0, x_21);
x_28 = l___private_Lean_Elab_Command_3__setState(x_19, x_5, x_20);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_15);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 0);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_28);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_19, 2);
x_38 = lean_ctor_get(x_19, 3);
x_39 = lean_ctor_get(x_19, 4);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_19);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_21);
lean_ctor_set(x_40, 1, x_23);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_22);
x_41 = l___private_Lean_Elab_Command_3__setState(x_40, x_5, x_20);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_43 = x_41;
} else {
 lean_dec_ref(x_41);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_15);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_15);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_47 = x_41;
} else {
 lean_dec_ref(x_41);
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
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_14, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 1);
lean_inc(x_54);
lean_dec(x_14);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_5);
x_56 = l___private_Lean_Elab_Command_2__getState(x_5, x_11);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 3);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_ctor_get(x_54, 2);
lean_inc(x_62);
lean_dec(x_54);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_58, 5);
lean_dec(x_64);
x_65 = lean_ctor_get(x_58, 1);
lean_dec(x_65);
x_66 = lean_ctor_get(x_58, 0);
lean_dec(x_66);
lean_ctor_set(x_58, 5, x_61);
lean_ctor_set(x_58, 1, x_62);
lean_ctor_set(x_58, 0, x_60);
x_67 = l___private_Lean_Elab_Command_3__setState(x_58, x_5, x_59);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 0, x_55);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_55);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_55);
x_72 = !lean_is_exclusive(x_67);
if (x_72 == 0)
{
return x_67;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_67, 0);
x_74 = lean_ctor_get(x_67, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_67);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_58, 2);
x_77 = lean_ctor_get(x_58, 3);
x_78 = lean_ctor_get(x_58, 4);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_58);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_60);
lean_ctor_set(x_79, 1, x_62);
lean_ctor_set(x_79, 2, x_76);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_79, 5, x_61);
x_80 = l___private_Lean_Elab_Command_3__setState(x_79, x_5, x_59);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
 lean_ctor_set_tag(x_83, 1);
}
lean_ctor_set(x_83, 0, x_55);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_55);
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_80, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_86 = x_80;
} else {
 lean_dec_ref(x_80);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_5);
x_88 = !lean_is_exclusive(x_56);
if (x_88 == 0)
{
return x_56;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_56, 0);
x_90 = lean_ctor_get(x_56, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_56);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_14);
x_92 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_93 = l_unreachable_x21___rarg(x_92);
x_94 = lean_apply_2(x_93, x_5, x_11);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_95 = !lean_is_exclusive(x_9);
if (x_95 == 0)
{
return x_9;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_9, 0);
x_97 = lean_ctor_get(x_9, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_9);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_29__addDefaults(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_29__addDefaults___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_29__addDefaults___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_29__addDefaults___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Structure_29__addDefaults___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_29__addDefaults___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Structure_29__addDefaults___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Structure_29__addDefaults(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
lean_inc(x_3);
x_11 = l_Lean_Elab_Command_addInstance(x_10, x_7, x_3, x_4);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
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
x_16 = l___private_Lean_Elab_Structure_25__elabStructureView(x_15, x_13, x_14);
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
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
x_12 = l_Lean_Elab_Command_mkDeclName(x_1, x_2, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_69; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
x_69 = l_Lean_Elab_Command_getLevelNames(x_10, x_14);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_10);
lean_inc(x_4);
x_72 = l___private_Lean_Elab_Structure_2__expandCtor(x_4, x_2, x_13, x_10, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_10);
x_75 = l___private_Lean_Elab_Structure_3__expandFields(x_4, x_2, x_13, x_10, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_13);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_13);
x_79 = lean_box(x_3);
lean_inc(x_13);
lean_inc(x_2);
lean_inc(x_4);
x_80 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__2___boxed), 14, 11);
lean_closure_set(x_80, 0, x_4);
lean_closure_set(x_80, 1, x_2);
lean_closure_set(x_80, 2, x_5);
lean_closure_set(x_80, 3, x_70);
lean_closure_set(x_80, 4, x_79);
lean_closure_set(x_80, 5, x_13);
lean_closure_set(x_80, 6, x_6);
lean_closure_set(x_80, 7, x_7);
lean_closure_set(x_80, 8, x_73);
lean_closure_set(x_80, 9, x_76);
lean_closure_set(x_80, 10, x_8);
lean_inc(x_10);
x_81 = l___private_Lean_Elab_Command_2__getState(x_10, x_77);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Lean_Elab_Command_8__getVarDecls(x_82);
lean_dec(x_82);
lean_inc(x_10);
x_85 = l___private_Lean_Elab_Command_2__getState(x_10, x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l___private_Lean_Elab_Command_6__mkTermContext(x_10, x_86, x_78);
x_89 = l___private_Lean_Elab_Command_7__mkTermState(x_86);
lean_dec(x_86);
x_90 = l_Lean_Elab_Term_elabBinders___rarg(x_84, x_80, x_88, x_89);
lean_dec(x_84);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_10);
x_93 = l___private_Lean_Elab_Command_2__getState(x_10, x_87);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_97 = lean_ctor_get(x_94, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_94, 3);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_ctor_get(x_92, 2);
lean_inc(x_99);
lean_dec(x_92);
x_100 = !lean_is_exclusive(x_95);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_95, 5);
lean_dec(x_101);
x_102 = lean_ctor_get(x_95, 1);
lean_dec(x_102);
x_103 = lean_ctor_get(x_95, 0);
lean_dec(x_103);
lean_ctor_set(x_95, 5, x_98);
lean_ctor_set(x_95, 1, x_99);
lean_ctor_set(x_95, 0, x_97);
lean_inc(x_10);
x_104 = l___private_Lean_Elab_Command_3__setState(x_95, x_10, x_96);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_15 = x_91;
x_16 = x_105;
goto block_68;
}
else
{
uint8_t x_106; 
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_104);
if (x_106 == 0)
{
return x_104;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_104, 0);
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_104);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_95, 2);
x_111 = lean_ctor_get(x_95, 3);
x_112 = lean_ctor_get(x_95, 4);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_95);
x_113 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_113, 0, x_97);
lean_ctor_set(x_113, 1, x_99);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_111);
lean_ctor_set(x_113, 4, x_112);
lean_ctor_set(x_113, 5, x_98);
lean_inc(x_10);
x_114 = l___private_Lean_Elab_Command_3__setState(x_113, x_10, x_96);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_15 = x_91;
x_16 = x_115;
goto block_68;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_118 = x_114;
} else {
 lean_dec_ref(x_114);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_93);
if (x_120 == 0)
{
return x_93;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_93, 0);
x_122 = lean_ctor_get(x_93, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_93);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_90, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
x_125 = lean_ctor_get(x_90, 1);
lean_inc(x_125);
lean_dec(x_90);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_10);
x_127 = l___private_Lean_Elab_Command_2__getState(x_10, x_87);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_128 = lean_ctor_get(x_125, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 3);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_ctor_get(x_125, 2);
lean_inc(x_133);
lean_dec(x_125);
x_134 = !lean_is_exclusive(x_129);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_129, 5);
lean_dec(x_135);
x_136 = lean_ctor_get(x_129, 1);
lean_dec(x_136);
x_137 = lean_ctor_get(x_129, 0);
lean_dec(x_137);
lean_ctor_set(x_129, 5, x_132);
lean_ctor_set(x_129, 1, x_133);
lean_ctor_set(x_129, 0, x_131);
x_138 = l___private_Lean_Elab_Command_3__setState(x_129, x_10, x_130);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
lean_ctor_set_tag(x_138, 1);
lean_ctor_set(x_138, 0, x_126);
return x_138;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_126);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
else
{
uint8_t x_143; 
lean_dec(x_126);
x_143 = !lean_is_exclusive(x_138);
if (x_143 == 0)
{
return x_138;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_138, 0);
x_145 = lean_ctor_get(x_138, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_138);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_147 = lean_ctor_get(x_129, 2);
x_148 = lean_ctor_get(x_129, 3);
x_149 = lean_ctor_get(x_129, 4);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_129);
x_150 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_150, 0, x_131);
lean_ctor_set(x_150, 1, x_133);
lean_ctor_set(x_150, 2, x_147);
lean_ctor_set(x_150, 3, x_148);
lean_ctor_set(x_150, 4, x_149);
lean_ctor_set(x_150, 5, x_132);
x_151 = l___private_Lean_Elab_Command_3__setState(x_150, x_10, x_130);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
 lean_ctor_set_tag(x_154, 1);
}
lean_ctor_set(x_154, 0, x_126);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_126);
x_155 = lean_ctor_get(x_151, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_151, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_157 = x_151;
} else {
 lean_dec_ref(x_151);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_10);
x_159 = !lean_is_exclusive(x_127);
if (x_159 == 0)
{
return x_127;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_127, 0);
x_161 = lean_ctor_get(x_127, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_127);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_90);
x_163 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_164 = l_unreachable_x21___rarg(x_163);
lean_inc(x_10);
x_165 = lean_apply_2(x_164, x_10, x_87);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_15 = x_166;
x_16 = x_167;
goto block_68;
}
else
{
uint8_t x_168; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_165);
if (x_168 == 0)
{
return x_165;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_165, 0);
x_170 = lean_ctor_get(x_165, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_165);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_84);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_172 = !lean_is_exclusive(x_85);
if (x_172 == 0)
{
return x_85;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_85, 0);
x_174 = lean_ctor_get(x_85, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_85);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
uint8_t x_176; 
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_81);
if (x_176 == 0)
{
return x_81;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_81, 0);
x_178 = lean_ctor_get(x_81, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_81);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
uint8_t x_180; 
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_180 = !lean_is_exclusive(x_75);
if (x_180 == 0)
{
return x_75;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_75, 0);
x_182 = lean_ctor_get(x_75, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_75);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
return x_183;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_70);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_184 = !lean_is_exclusive(x_72);
if (x_184 == 0)
{
return x_72;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_72, 0);
x_186 = lean_ctor_get(x_72, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_72);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_188 = !lean_is_exclusive(x_69);
if (x_188 == 0)
{
return x_69;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_69, 0);
x_190 = lean_ctor_get(x_69, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_69);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
block_68:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_15, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_15, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 6);
lean_inc(x_24);
lean_dec(x_15);
lean_inc(x_10);
x_25 = l_Lean_Elab_Command_addDecl(x_17, x_10, x_16);
lean_dec(x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_10);
x_27 = l___private_Lean_Elab_Structure_27__addProjections(x_1, x_13, x_18, x_3, x_10, x_26);
lean_dec(x_18);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_10);
x_29 = l___private_Lean_Elab_Structure_28__mkAuxConstructions(x_13, x_10, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = 0;
x_32 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
x_33 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_1, x_13, x_31, x_19, x_32, x_10, x_30);
lean_dec(x_19);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_10);
x_35 = l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1(x_4, x_20, x_10, x_34);
lean_dec(x_4);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l___private_Lean_Elab_Structure_29__addDefaults___rarg(x_21, x_22, x_23, x_24, x_10, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_37);
if (x_44 == 0)
{
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_37, 0);
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_37);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_10);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_33);
if (x_52 == 0)
{
return x_33;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_33, 0);
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_33);
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
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
x_56 = !lean_is_exclusive(x_29);
if (x_56 == 0)
{
return x_29;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_29, 0);
x_58 = lean_ctor_get(x_29, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_29);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_27);
if (x_60 == 0)
{
return x_27;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_27, 0);
x_62 = lean_ctor_get(x_27, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_27);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_4);
x_64 = !lean_is_exclusive(x_25);
if (x_64 == 0)
{
return x_25;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_25, 0);
x_66 = lean_ctor_get(x_25, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_25);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_192 = !lean_is_exclusive(x_12);
if (x_192 == 0)
{
return x_12;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_12, 0);
x_194 = lean_ctor_get(x_12, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_12);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
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
lean_object* l_Lean_Elab_Command_elabStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_2, x_5);
x_7 = l_Lean_Syntax_getKind(x_6);
x_8 = l_Lean_Parser_Command_classTk___elambda__1___closed__2;
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_2, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = l_Lean_Syntax_getArgs(x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Syntax_getArg(x_2, x_15);
x_17 = l_Lean_Syntax_isNone(x_16);
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Syntax_getArg(x_2, x_18);
x_20 = l_Lean_Syntax_isNone(x_19);
lean_inc(x_3);
x_21 = l_Lean_Elab_Command_checkValidInductiveModifier(x_2, x_1, x_3, x_4);
if (x_9 == 0)
{
x_22 = x_1;
goto block_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_Elab_Command_elabStructure___closed__8;
x_72 = l_Lean_Elab_Command_Modifiers_addAttribute(x_1, x_71);
x_22 = x_72;
goto block_70;
}
block_70:
{
lean_object* x_23; 
if (x_17 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = l_Lean_Syntax_getArg(x_16, x_5);
lean_dec(x_16);
x_65 = l_Lean_Syntax_getArg(x_64, x_10);
lean_dec(x_64);
x_66 = l_Lean_Syntax_getArgs(x_65);
lean_dec(x_65);
x_67 = l_Array_empty___closed__1;
x_68 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_12, x_66, x_5, x_67);
lean_dec(x_66);
x_23 = x_68;
goto block_63;
}
else
{
lean_object* x_69; 
lean_dec(x_16);
x_69 = l_Array_empty___closed__1;
x_23 = x_69;
goto block_63;
}
block_63:
{
lean_object* x_24; lean_object* x_25; uint8_t x_37; lean_object* x_38; 
if (x_20 == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_dec(x_21);
x_52 = 0;
x_37 = x_52;
x_38 = x_51;
goto block_50;
}
else
{
uint8_t x_53; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_21);
if (x_53 == 0)
{
return x_21;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_21, 0);
x_55 = lean_ctor_get(x_21, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_21);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_dec(x_21);
x_58 = 1;
x_37 = x_58;
x_38 = x_57;
goto block_50;
}
else
{
uint8_t x_59; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_21);
if (x_59 == 0)
{
return x_21;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_21, 0);
x_61 = lean_ctor_get(x_21, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_21);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
block_36:
{
lean_object* x_26; 
lean_inc(x_3);
x_26 = l_Lean_Elab_Command_getLevelNames(x_3, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(x_9);
lean_inc(x_11);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__3___boxed), 11, 8);
lean_closure_set(x_30, 0, x_11);
lean_closure_set(x_30, 1, x_22);
lean_closure_set(x_30, 2, x_29);
lean_closure_set(x_30, 3, x_2);
lean_closure_set(x_30, 4, x_27);
lean_closure_set(x_30, 5, x_23);
lean_closure_set(x_30, 6, x_24);
lean_closure_set(x_30, 7, x_14);
x_31 = l_Lean_Elab_Command_withDeclId___rarg(x_11, x_30, x_3, x_28);
lean_dec(x_11);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
block_50:
{
if (x_37 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Syntax_getArg(x_19, x_5);
lean_dec(x_19);
x_40 = l_Lean_Syntax_getArg(x_39, x_10);
lean_dec(x_39);
x_24 = x_40;
x_25 = x_38;
goto block_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_19);
x_41 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_38);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_3);
x_43 = l_Lean_Elab_Command_getMainModule(x_3, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Elab_Command_elabStructure___closed__7;
x_24 = x_45;
x_25 = x_44;
goto block_36;
}
else
{
uint8_t x_46; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
}
}
}
lean_object* l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forM___main___at_Lean_Elab_Command_elabStructure___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
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
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Elab_Command_elabStructure___lambda__3(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
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
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__1 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__1);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__2 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__2);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__3 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__3);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__4 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__4);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__5 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__5);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__7 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__7);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__8 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__8);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__10 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__10);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__11 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__11);
l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12 = _init_l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12);
l___private_Lean_Elab_Structure_11__getResultUniverse___closed__1 = _init_l___private_Lean_Elab_Structure_11__getResultUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__getResultUniverse___closed__1);
l___private_Lean_Elab_Structure_11__getResultUniverse___closed__2 = _init_l___private_Lean_Elab_Structure_11__getResultUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__getResultUniverse___closed__2);
l___private_Lean_Elab_Structure_11__getResultUniverse___closed__3 = _init_l___private_Lean_Elab_Structure_11__getResultUniverse___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_11__getResultUniverse___closed__3);
l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__1);
l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__2);
l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__3 = _init_l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__3);
l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_25__elabStructureView___spec__6___closed__2);
l___private_Lean_Elab_Structure_25__elabStructureView___closed__1 = _init_l___private_Lean_Elab_Structure_25__elabStructureView___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_25__elabStructureView___closed__1);
l___private_Lean_Elab_Structure_25__elabStructureView___closed__2 = _init_l___private_Lean_Elab_Structure_25__elabStructureView___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_25__elabStructureView___closed__2);
l___private_Lean_Elab_Structure_25__elabStructureView___closed__3 = _init_l___private_Lean_Elab_Structure_25__elabStructureView___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_25__elabStructureView___closed__3);
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
