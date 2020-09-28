// Lean compiler output
// Module: Lean.Elab.Structure
// Imports: Init Lean.Meta.Closure Lean.Elab.Command Lean.Elab.DeclModifiers Lean.Elab.DeclUtil Lean.Elab.Inductive
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
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_13__collectUsed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkHole___closed__3;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__9;
lean_object* l_Lean_Elab_Command_elabStructure___closed__11;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__11;
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Elab_Command_StructFieldInfo_inhabited;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__11;
lean_object* l_Lean_Meta_mkProjection___at___private_Lean_Elab_Structure_8__processSubfields___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_24__collectLevelParamsInStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__4;
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_18__levelMVarToParamAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_29__mkAuxConstructions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isProtected(lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__14;
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__5;
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_2__expandCtor___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__3;
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__4(lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__1;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__4;
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_21__updateResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___closed__3;
lean_object* l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__2;
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__11;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__12;
extern lean_object* l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
lean_object* l___private_Lean_Elab_Structure_15__withUsed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkId___at___private_Lean_Elab_Structure_30__addDefaults___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__collectLevelParamsInFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_3__expandFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInternalSubobjectFieldName(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_28__addProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__3;
extern lean_object* l___private_Lean_Elab_Inductive_26__removeUnused___closed__1;
lean_object* l___private_Lean_Elab_Structure_18__levelMVarToParamAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__7;
lean_object* l___private_Lean_Meta_InferType_4__getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__2;
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames___rarg(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__10;
lean_object* l___private_Lean_Elab_Structure_20__collectUniversesFromFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_4__validStructType___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_14__removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__12;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_13__collectUsed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__11;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__5;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__4;
lean_object* l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_logDbgTrace___rarg___closed__1;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__20;
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__2(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isFromParent___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__2;
lean_object* l___private_Lean_Elab_Structure_24__collectLevelParamsInStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_15__withUsed(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Structure_25__addCtorFields___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__12;
lean_object* l___private_Lean_Elab_Structure_20__collectUniversesFromFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Level_elabLevel___main___closed__6;
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__15;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__18;
lean_object* l_Lean_LocalDecl_value(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__10;
lean_object* l___private_Lean_Elab_Structure_10__elabFieldTypeValue___closed__1;
lean_object* l___private_Lean_Elab_Structure_9__withParents(lean_object*);
uint8_t l___private_Lean_Elab_Structure_7__containsFieldName(lean_object*, lean_object*);
lean_object* l_Lean_Level_getLevelOffset___main(lean_object*);
lean_object* l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_13__collectUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__1;
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__9;
uint8_t l_Lean_Elab_Command_StructFieldInfo_isSubobject(lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_expandDeclId___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__10;
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_expandDeclId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__8;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_List_map___main___at_Lean_Meta_addGlobalInstanceImp___spec__1(lean_object*);
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__10;
lean_object* l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2___closed__1;
lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_Structure_2__expandCtor___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_25__addCtorFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__7;
lean_object* l_Lean_Elab_Command_StructFieldInfo_inhabited___closed__1;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_2__expandCtor___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__15;
lean_object* l___private_Lean_Elab_Structure_18__levelMVarToParamAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Structure_16__levelMVarToParamFVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_Lean_Elab_Command_elabStructure___closed__4;
lean_object* l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_projections(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__16;
lean_object* l_Lean_Meta_addGlobalInstance___at___private_Lean_Elab_Structure_31__elabStructureView___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_1__defaultCtorName;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__2;
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
extern lean_object* l_Lean_Meta_inferTypeRef;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2___boxed(lean_object**);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__1;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_StructFieldInfo_isSubobject___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___at_Lean_Elab_Term_removeUnused___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__5;
lean_object* l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__14;
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main(lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_18__levelMVarToParamAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_21__updateResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* lean_mk_no_confusion(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__9;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__5;
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___closed__1;
uint8_t l___private_Lean_Elab_Structure_4__validStructType(lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__13;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__23;
lean_object* l_Lean_Elab_Command_elabStructure___closed__3;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__5;
extern lean_object* l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__7;
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
lean_object* l___private_Lean_Elab_Structure_15__withUsed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___closed__2;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__21;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__5;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7;
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3;
extern lean_object* l_Lean_registerClassAttr___closed__2;
lean_object* l_Lean_LocalContext_updateBinderInfo(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___closed__3;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__11;
lean_object* l_Lean_Elab_Term_elabBinders___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__5;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__22;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3;
lean_object* l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_17__elabImplicitLambdaAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection___at___private_Lean_Elab_Structure_8__processSubfields___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l___private_Lean_Elab_Structure_25__addCtorFields___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8;
lean_object* l_Lean_Syntax_isIdOrAtom_x3f(lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_resetMessageLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___closed__3;
lean_object* lean_add_instance(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
extern lean_object* l_Lean_Prod_hasQuote___rarg___closed__3;
lean_object* l_Lean_Name_getString_x21(lean_object*);
extern lean_object* l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___closed__1;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__7;
uint8_t l_Lean_isAttribute(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__6;
lean_object* l___private_Lean_Elab_Structure_3__expandFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignLevelMVar___at___private_Lean_Elab_Structure_21__updateResultingUniverse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getNumArgs(lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6;
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse___closed__1;
lean_object* l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1;
lean_object* l___private_Lean_Elab_Structure_19__levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_25__addCtorFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2;
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse___closed__2;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Structure_27__mkProjections___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__8;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_metavar_ctx_assign_level(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1;
lean_object* l_Lean_Elab_Command_elabStructure___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Elab_Term_5__isTypeApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_addGlobalInstance___at___private_Lean_Elab_Structure_31__elabStructureView___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__4;
lean_object* l_Lean_Elab_Command_getMainModule___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__13;
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__1;
lean_object* l_Lean_Elab_Command_getRef(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__14;
lean_object* l___private_Lean_Elab_Structure_11__withFields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5;
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_30__addDefaults(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__6;
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
lean_object* l___private_Lean_Elab_Command_4__getVarDecls(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_1__mkIdImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_set_reducibility_status(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__2;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__15;
lean_object* l___private_Lean_Elab_Structure_19__levelMVarToParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__elabFieldTypeValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_StructFieldInfo_isFromParent(lean_object*);
lean_object* l_Lean_Elab_Modifiers_addAttribute(lean_object*, lean_object*);
lean_object* lean_mk_rec_on(lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__19;
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_20__collectUniversesFromFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Structure_16__levelMVarToParamFVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_24__collectLevelParamsInStructure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
extern lean_object* l_Lean_Elab_Command_CtorView_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7;
lean_object* l_Lean_Meta_assignLevelMVar___at___private_Lean_Elab_Structure_21__updateResultingUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6;
lean_object* l_Lean_Meta_mkId___at___private_Lean_Elab_Structure_30__addDefaults___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__13;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__10;
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__1;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParamFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Modifiers_isPrivate(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_appendBefore(lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_Structure_2__expandCtor___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l___private_Lean_Elab_Structure_26__mkCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
lean_object* l_Lean_Expr_inferImplicit___main(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_28__addProjections(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___closed__3;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParamFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStxAux___main(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__8;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__6;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__7;
uint8_t l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__16;
lean_object* l_Lean_Level_mkNaryMax___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_13__collectUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__2;
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__8;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4;
lean_object* l___private_Lean_Elab_Structure_7__containsFieldName___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_24__collectLevelParamsInStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__17;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__1;
lean_object* l___private_Lean_Elab_Structure_26__mkCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__4;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__4;
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__6;
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_20__collectUniversesFromFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_14__removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_29__mkAuxConstructions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_2 = l_Lean_Prod_hasQuote___rarg___closed__3;
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
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_2__expandCtor___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_isIdOrAtom_x3f(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_Elab_Command_getRef(x_2, x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_replaceRef(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_2, 6);
lean_dec(x_13);
lean_ctor_set(x_2, 6, x_11);
x_14 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_15 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_14, x_2, x_3, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
x_24 = lean_ctor_get(x_2, 4);
x_25 = lean_ctor_get(x_2, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_26 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_21);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_24);
lean_ctor_set(x_26, 5, x_25);
lean_ctor_set(x_26, 6, x_11);
x_27 = l_Lean_Elab_elabAttr___rarg___closed__3;
x_28 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_27, x_26, x_3, x_10);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_6);
x_33 = lean_ctor_get(x_7, 0);
lean_inc(x_33);
lean_dec(x_7);
x_34 = lean_box(0);
x_35 = lean_name_mk_string(x_34, x_33);
x_36 = lean_st_ref_get(x_3, x_4);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_isAttribute(x_40, x_35);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_free_object(x_36);
x_42 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_42, 0, x_35);
x_43 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_46, x_2, x_3, x_39);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_2);
x_52 = lean_unsigned_to_nat(1u);
x_53 = l_Lean_Syntax_getArg(x_1, x_52);
x_54 = l_Lean_Syntax_getNumArgs(x_53);
x_55 = lean_nat_dec_eq(x_54, x_5);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_35);
lean_ctor_set(x_56, 1, x_53);
lean_ctor_set(x_36, 0, x_56);
return x_36;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_53);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_35);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_36, 0, x_58);
return x_36;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_36, 0);
x_60 = lean_ctor_get(x_36, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_36);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_isAttribute(x_61, x_35);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_63 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_63, 0, x_35);
x_64 = l_Lean_Elab_elabAttr___rarg___lambda__2___closed__3;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Lean_MessageData_arrayExpr_toMessageData___main___closed__1;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_67, x_2, x_3, x_60);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_71 = x_68;
} else {
 lean_dec_ref(x_68);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_2);
x_73 = lean_unsigned_to_nat(1u);
x_74 = l_Lean_Syntax_getArg(x_1, x_73);
x_75 = l_Lean_Syntax_getNumArgs(x_74);
x_76 = lean_nat_dec_eq(x_75, x_5);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_35);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_60);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_35);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_60);
return x_81;
}
}
}
}
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_Structure_2__expandCtor___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_2, x_3);
lean_inc(x_5);
x_12 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_2__expandCtor___spec__4(x_11, x_5, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_push(x_4, x_13);
x_16 = lean_nat_add(x_3, x_1);
lean_dec(x_3);
x_3 = x_16;
x_4 = x_15;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lean_Syntax_getArgs(x_1);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_empty___closed__1;
x_9 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_Structure_2__expandCtor___spec__5(x_6, x_5, x_7, x_8, x_2, x_3, x_4);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__3(x_6, x_2, x_3, x_4);
lean_dec(x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 1;
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 1;
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 1;
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 1;
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = 1;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = 1;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = 0;
x_4 = 1;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 1;
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__9() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__11() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 0;
x_4 = 1;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 0;
x_4 = 1;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 0;
x_4 = 1;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__15() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = 0;
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = 1;
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__17() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = 1;
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = 1;
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__19() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = 1;
x_4 = 0;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = 0;
x_4 = 1;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__21() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = 0;
x_4 = 1;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_3);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__22() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = 0;
x_4 = 1;
x_5 = l_Array_empty___closed__1;
x_6 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__23() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 2;
x_3 = 0;
x_4 = l_Array_empty___closed__1;
x_5 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(4u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(5u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = l_Lean_Syntax_getOptional_x3f(x_6);
lean_dec(x_6);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; 
lean_dec(x_2);
x_21 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_22 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_23 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_21 == 0)
{
if (x_22 == 0)
{
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_4);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__2;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_4);
return x_27;
}
}
else
{
if (x_23 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__3;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__4;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_4);
return x_31;
}
}
}
else
{
if (x_22 == 0)
{
if (x_23 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__5;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__6;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_4);
return x_35;
}
}
else
{
if (x_23 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__7;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_4);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = l_Lean_Elab_Command_CtorView_inhabited___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_4);
return x_39;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_20, 0);
lean_inc(x_40);
lean_dec(x_20);
x_41 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_40, x_2, x_3, x_4);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_45 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_46 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_44 == 0)
{
if (x_45 == 0)
{
if (x_46 == 0)
{
uint8_t x_47; uint8_t x_48; lean_object* x_49; 
x_47 = 0;
x_48 = 1;
x_49 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*2 + 1, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2 + 2, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2 + 3, x_48);
lean_ctor_set(x_41, 0, x_49);
return x_41;
}
else
{
uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_50 = 0;
x_51 = 1;
x_52 = 0;
x_53 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_53, 0, x_18);
lean_ctor_set(x_53, 1, x_43);
lean_ctor_set_uint8(x_53, sizeof(void*)*2, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 1, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 2, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*2 + 3, x_52);
lean_ctor_set(x_41, 0, x_53);
return x_41;
}
}
else
{
if (x_46 == 0)
{
uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; 
x_54 = 0;
x_55 = 1;
x_56 = 0;
x_57 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_57, 0, x_18);
lean_ctor_set(x_57, 1, x_43);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 1, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 2, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 3, x_55);
lean_ctor_set(x_41, 0, x_57);
return x_41;
}
else
{
uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_58 = 0;
x_59 = 1;
x_60 = 0;
x_61 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_61, 0, x_18);
lean_ctor_set(x_61, 1, x_43);
lean_ctor_set_uint8(x_61, sizeof(void*)*2, x_58);
lean_ctor_set_uint8(x_61, sizeof(void*)*2 + 1, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*2 + 2, x_60);
lean_ctor_set_uint8(x_61, sizeof(void*)*2 + 3, x_60);
lean_ctor_set(x_41, 0, x_61);
return x_41;
}
}
}
else
{
if (x_45 == 0)
{
if (x_46 == 0)
{
uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_62 = 0;
x_63 = 0;
x_64 = 1;
x_65 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_65, 0, x_18);
lean_ctor_set(x_65, 1, x_43);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 1, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 2, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 3, x_64);
lean_ctor_set(x_41, 0, x_65);
return x_41;
}
else
{
uint8_t x_66; uint8_t x_67; uint8_t x_68; lean_object* x_69; 
x_66 = 0;
x_67 = 0;
x_68 = 1;
x_69 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_69, 0, x_18);
lean_ctor_set(x_69, 1, x_43);
lean_ctor_set_uint8(x_69, sizeof(void*)*2, x_66);
lean_ctor_set_uint8(x_69, sizeof(void*)*2 + 1, x_67);
lean_ctor_set_uint8(x_69, sizeof(void*)*2 + 2, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*2 + 3, x_67);
lean_ctor_set(x_41, 0, x_69);
return x_41;
}
}
else
{
if (x_46 == 0)
{
uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; 
x_70 = 0;
x_71 = 0;
x_72 = 1;
x_73 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_73, 0, x_18);
lean_ctor_set(x_73, 1, x_43);
lean_ctor_set_uint8(x_73, sizeof(void*)*2, x_70);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 1, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 2, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*2 + 3, x_72);
lean_ctor_set(x_41, 0, x_73);
return x_41;
}
else
{
uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_74 = 0;
x_75 = 0;
x_76 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_76, 0, x_18);
lean_ctor_set(x_76, 1, x_43);
lean_ctor_set_uint8(x_76, sizeof(void*)*2, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 1, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 2, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*2 + 3, x_75);
lean_ctor_set(x_41, 0, x_76);
return x_41;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; 
x_77 = lean_ctor_get(x_41, 0);
x_78 = lean_ctor_get(x_41, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_41);
x_79 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_80 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_81 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_79 == 0)
{
if (x_80 == 0)
{
if (x_81 == 0)
{
uint8_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_82 = 0;
x_83 = 1;
x_84 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_84, 0, x_18);
lean_ctor_set(x_84, 1, x_77);
lean_ctor_set_uint8(x_84, sizeof(void*)*2, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*2 + 1, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*2 + 2, x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*2 + 3, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_78);
return x_85;
}
else
{
uint8_t x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_86 = 0;
x_87 = 1;
x_88 = 0;
x_89 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_89, 0, x_18);
lean_ctor_set(x_89, 1, x_77);
lean_ctor_set_uint8(x_89, sizeof(void*)*2, x_86);
lean_ctor_set_uint8(x_89, sizeof(void*)*2 + 1, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*2 + 2, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*2 + 3, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_78);
return x_90;
}
}
else
{
if (x_81 == 0)
{
uint8_t x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_91 = 0;
x_92 = 1;
x_93 = 0;
x_94 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_94, 0, x_18);
lean_ctor_set(x_94, 1, x_77);
lean_ctor_set_uint8(x_94, sizeof(void*)*2, x_91);
lean_ctor_set_uint8(x_94, sizeof(void*)*2 + 1, x_92);
lean_ctor_set_uint8(x_94, sizeof(void*)*2 + 2, x_93);
lean_ctor_set_uint8(x_94, sizeof(void*)*2 + 3, x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_78);
return x_95;
}
else
{
uint8_t x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
x_96 = 0;
x_97 = 1;
x_98 = 0;
x_99 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_99, 0, x_18);
lean_ctor_set(x_99, 1, x_77);
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_96);
lean_ctor_set_uint8(x_99, sizeof(void*)*2 + 1, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*2 + 2, x_98);
lean_ctor_set_uint8(x_99, sizeof(void*)*2 + 3, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_78);
return x_100;
}
}
}
else
{
if (x_80 == 0)
{
if (x_81 == 0)
{
uint8_t x_101; uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_101 = 0;
x_102 = 0;
x_103 = 1;
x_104 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_104, 0, x_18);
lean_ctor_set(x_104, 1, x_77);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*2 + 1, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*2 + 2, x_103);
lean_ctor_set_uint8(x_104, sizeof(void*)*2 + 3, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_78);
return x_105;
}
else
{
uint8_t x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
x_106 = 0;
x_107 = 0;
x_108 = 1;
x_109 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_109, 0, x_18);
lean_ctor_set(x_109, 1, x_77);
lean_ctor_set_uint8(x_109, sizeof(void*)*2, x_106);
lean_ctor_set_uint8(x_109, sizeof(void*)*2 + 1, x_107);
lean_ctor_set_uint8(x_109, sizeof(void*)*2 + 2, x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*2 + 3, x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_78);
return x_110;
}
}
else
{
if (x_81 == 0)
{
uint8_t x_111; uint8_t x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
x_111 = 0;
x_112 = 0;
x_113 = 1;
x_114 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_114, 0, x_18);
lean_ctor_set(x_114, 1, x_77);
lean_ctor_set_uint8(x_114, sizeof(void*)*2, x_111);
lean_ctor_set_uint8(x_114, sizeof(void*)*2 + 1, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*2 + 2, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*2 + 3, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_78);
return x_115;
}
else
{
uint8_t x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; 
x_116 = 0;
x_117 = 0;
x_118 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_118, 0, x_18);
lean_ctor_set(x_118, 1, x_77);
lean_ctor_set_uint8(x_118, sizeof(void*)*2, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*2 + 1, x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*2 + 2, x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*2 + 3, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_78);
return x_119;
}
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_120 = !lean_is_exclusive(x_41);
if (x_120 == 0)
{
return x_41;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_41, 0);
x_122 = lean_ctor_get(x_41, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_41);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_19, 0);
lean_inc(x_124);
lean_dec(x_19);
lean_inc(x_124);
x_125 = l_Lean_Syntax_getKind(x_124);
x_126 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3;
x_127 = lean_name_eq(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4;
x_129 = lean_name_eq(x_125, x_128);
lean_dec(x_125);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
x_130 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7;
x_131 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(x_124, x_130, x_2, x_3, x_4);
lean_dec(x_124);
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
lean_object* x_136; 
lean_dec(x_124);
x_136 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_136) == 0)
{
uint8_t x_137; uint8_t x_138; uint8_t x_139; 
lean_dec(x_2);
x_137 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_138 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_139 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_137 == 0)
{
if (x_138 == 0)
{
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__8;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_4);
return x_141;
}
else
{
lean_object* x_142; lean_object* x_143; 
x_142 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__9;
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_4);
return x_143;
}
}
else
{
if (x_139 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__10;
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_4);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__11;
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_4);
return x_147;
}
}
}
else
{
if (x_138 == 0)
{
if (x_139 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__12;
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_4);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__13;
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_4);
return x_151;
}
}
else
{
if (x_139 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__14;
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_4);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__15;
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_4);
return x_155;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_136, 0);
lean_inc(x_156);
lean_dec(x_136);
x_157 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_156, x_2, x_3, x_4);
lean_dec(x_156);
if (lean_obj_tag(x_157) == 0)
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_157);
if (x_158 == 0)
{
lean_object* x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_157, 0);
x_160 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_161 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_162 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_160 == 0)
{
if (x_161 == 0)
{
if (x_162 == 0)
{
uint8_t x_163; uint8_t x_164; lean_object* x_165; 
x_163 = 1;
x_164 = 1;
x_165 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_165, 0, x_18);
lean_ctor_set(x_165, 1, x_159);
lean_ctor_set_uint8(x_165, sizeof(void*)*2, x_163);
lean_ctor_set_uint8(x_165, sizeof(void*)*2 + 1, x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*2 + 2, x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*2 + 3, x_164);
lean_ctor_set(x_157, 0, x_165);
return x_157;
}
else
{
uint8_t x_166; uint8_t x_167; uint8_t x_168; lean_object* x_169; 
x_166 = 1;
x_167 = 1;
x_168 = 0;
x_169 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_169, 0, x_18);
lean_ctor_set(x_169, 1, x_159);
lean_ctor_set_uint8(x_169, sizeof(void*)*2, x_166);
lean_ctor_set_uint8(x_169, sizeof(void*)*2 + 1, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*2 + 2, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*2 + 3, x_168);
lean_ctor_set(x_157, 0, x_169);
return x_157;
}
}
else
{
if (x_162 == 0)
{
uint8_t x_170; uint8_t x_171; uint8_t x_172; lean_object* x_173; 
x_170 = 1;
x_171 = 1;
x_172 = 0;
x_173 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_173, 0, x_18);
lean_ctor_set(x_173, 1, x_159);
lean_ctor_set_uint8(x_173, sizeof(void*)*2, x_170);
lean_ctor_set_uint8(x_173, sizeof(void*)*2 + 1, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*2 + 2, x_172);
lean_ctor_set_uint8(x_173, sizeof(void*)*2 + 3, x_171);
lean_ctor_set(x_157, 0, x_173);
return x_157;
}
else
{
uint8_t x_174; uint8_t x_175; uint8_t x_176; lean_object* x_177; 
x_174 = 1;
x_175 = 1;
x_176 = 0;
x_177 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_177, 0, x_18);
lean_ctor_set(x_177, 1, x_159);
lean_ctor_set_uint8(x_177, sizeof(void*)*2, x_174);
lean_ctor_set_uint8(x_177, sizeof(void*)*2 + 1, x_175);
lean_ctor_set_uint8(x_177, sizeof(void*)*2 + 2, x_176);
lean_ctor_set_uint8(x_177, sizeof(void*)*2 + 3, x_176);
lean_ctor_set(x_157, 0, x_177);
return x_157;
}
}
}
else
{
if (x_161 == 0)
{
if (x_162 == 0)
{
uint8_t x_178; uint8_t x_179; uint8_t x_180; lean_object* x_181; 
x_178 = 1;
x_179 = 0;
x_180 = 1;
x_181 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_181, 0, x_18);
lean_ctor_set(x_181, 1, x_159);
lean_ctor_set_uint8(x_181, sizeof(void*)*2, x_178);
lean_ctor_set_uint8(x_181, sizeof(void*)*2 + 1, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*2 + 2, x_180);
lean_ctor_set_uint8(x_181, sizeof(void*)*2 + 3, x_180);
lean_ctor_set(x_157, 0, x_181);
return x_157;
}
else
{
uint8_t x_182; uint8_t x_183; uint8_t x_184; lean_object* x_185; 
x_182 = 1;
x_183 = 0;
x_184 = 1;
x_185 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_185, 0, x_18);
lean_ctor_set(x_185, 1, x_159);
lean_ctor_set_uint8(x_185, sizeof(void*)*2, x_182);
lean_ctor_set_uint8(x_185, sizeof(void*)*2 + 1, x_183);
lean_ctor_set_uint8(x_185, sizeof(void*)*2 + 2, x_184);
lean_ctor_set_uint8(x_185, sizeof(void*)*2 + 3, x_183);
lean_ctor_set(x_157, 0, x_185);
return x_157;
}
}
else
{
if (x_162 == 0)
{
uint8_t x_186; uint8_t x_187; uint8_t x_188; lean_object* x_189; 
x_186 = 1;
x_187 = 0;
x_188 = 1;
x_189 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_189, 0, x_18);
lean_ctor_set(x_189, 1, x_159);
lean_ctor_set_uint8(x_189, sizeof(void*)*2, x_186);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 1, x_187);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 2, x_187);
lean_ctor_set_uint8(x_189, sizeof(void*)*2 + 3, x_188);
lean_ctor_set(x_157, 0, x_189);
return x_157;
}
else
{
uint8_t x_190; uint8_t x_191; lean_object* x_192; 
x_190 = 1;
x_191 = 0;
x_192 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_192, 0, x_18);
lean_ctor_set(x_192, 1, x_159);
lean_ctor_set_uint8(x_192, sizeof(void*)*2, x_190);
lean_ctor_set_uint8(x_192, sizeof(void*)*2 + 1, x_191);
lean_ctor_set_uint8(x_192, sizeof(void*)*2 + 2, x_191);
lean_ctor_set_uint8(x_192, sizeof(void*)*2 + 3, x_191);
lean_ctor_set(x_157, 0, x_192);
return x_157;
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; 
x_193 = lean_ctor_get(x_157, 0);
x_194 = lean_ctor_get(x_157, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_157);
x_195 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_196 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_197 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_195 == 0)
{
if (x_196 == 0)
{
if (x_197 == 0)
{
uint8_t x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; 
x_198 = 1;
x_199 = 1;
x_200 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_200, 0, x_18);
lean_ctor_set(x_200, 1, x_193);
lean_ctor_set_uint8(x_200, sizeof(void*)*2, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*2 + 1, x_199);
lean_ctor_set_uint8(x_200, sizeof(void*)*2 + 2, x_199);
lean_ctor_set_uint8(x_200, sizeof(void*)*2 + 3, x_199);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_194);
return x_201;
}
else
{
uint8_t x_202; uint8_t x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; 
x_202 = 1;
x_203 = 1;
x_204 = 0;
x_205 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_205, 0, x_18);
lean_ctor_set(x_205, 1, x_193);
lean_ctor_set_uint8(x_205, sizeof(void*)*2, x_202);
lean_ctor_set_uint8(x_205, sizeof(void*)*2 + 1, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*2 + 2, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*2 + 3, x_204);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_194);
return x_206;
}
}
else
{
if (x_197 == 0)
{
uint8_t x_207; uint8_t x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; 
x_207 = 1;
x_208 = 1;
x_209 = 0;
x_210 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_210, 0, x_18);
lean_ctor_set(x_210, 1, x_193);
lean_ctor_set_uint8(x_210, sizeof(void*)*2, x_207);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 1, x_208);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 2, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*2 + 3, x_208);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_194);
return x_211;
}
else
{
uint8_t x_212; uint8_t x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; 
x_212 = 1;
x_213 = 1;
x_214 = 0;
x_215 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_215, 0, x_18);
lean_ctor_set(x_215, 1, x_193);
lean_ctor_set_uint8(x_215, sizeof(void*)*2, x_212);
lean_ctor_set_uint8(x_215, sizeof(void*)*2 + 1, x_213);
lean_ctor_set_uint8(x_215, sizeof(void*)*2 + 2, x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*2 + 3, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_194);
return x_216;
}
}
}
else
{
if (x_196 == 0)
{
if (x_197 == 0)
{
uint8_t x_217; uint8_t x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; 
x_217 = 1;
x_218 = 0;
x_219 = 1;
x_220 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_220, 0, x_18);
lean_ctor_set(x_220, 1, x_193);
lean_ctor_set_uint8(x_220, sizeof(void*)*2, x_217);
lean_ctor_set_uint8(x_220, sizeof(void*)*2 + 1, x_218);
lean_ctor_set_uint8(x_220, sizeof(void*)*2 + 2, x_219);
lean_ctor_set_uint8(x_220, sizeof(void*)*2 + 3, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_194);
return x_221;
}
else
{
uint8_t x_222; uint8_t x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; 
x_222 = 1;
x_223 = 0;
x_224 = 1;
x_225 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_225, 0, x_18);
lean_ctor_set(x_225, 1, x_193);
lean_ctor_set_uint8(x_225, sizeof(void*)*2, x_222);
lean_ctor_set_uint8(x_225, sizeof(void*)*2 + 1, x_223);
lean_ctor_set_uint8(x_225, sizeof(void*)*2 + 2, x_224);
lean_ctor_set_uint8(x_225, sizeof(void*)*2 + 3, x_223);
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_225);
lean_ctor_set(x_226, 1, x_194);
return x_226;
}
}
else
{
if (x_197 == 0)
{
uint8_t x_227; uint8_t x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; 
x_227 = 1;
x_228 = 0;
x_229 = 1;
x_230 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_230, 0, x_18);
lean_ctor_set(x_230, 1, x_193);
lean_ctor_set_uint8(x_230, sizeof(void*)*2, x_227);
lean_ctor_set_uint8(x_230, sizeof(void*)*2 + 1, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*2 + 2, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*2 + 3, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_194);
return x_231;
}
else
{
uint8_t x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; 
x_232 = 1;
x_233 = 0;
x_234 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_234, 0, x_18);
lean_ctor_set(x_234, 1, x_193);
lean_ctor_set_uint8(x_234, sizeof(void*)*2, x_232);
lean_ctor_set_uint8(x_234, sizeof(void*)*2 + 1, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*2 + 2, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*2 + 3, x_233);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_194);
return x_235;
}
}
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_236 = !lean_is_exclusive(x_157);
if (x_236 == 0)
{
return x_157;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_157, 0);
x_238 = lean_ctor_get(x_157, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_157);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
}
}
else
{
lean_object* x_240; 
lean_dec(x_125);
lean_dec(x_124);
x_240 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_240) == 0)
{
uint8_t x_241; uint8_t x_242; uint8_t x_243; 
lean_dec(x_2);
x_241 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_242 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_243 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_241 == 0)
{
if (x_242 == 0)
{
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__16;
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_4);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__17;
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_4);
return x_247;
}
}
else
{
if (x_243 == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__18;
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_4);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__19;
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_4);
return x_251;
}
}
}
else
{
if (x_242 == 0)
{
if (x_243 == 0)
{
lean_object* x_252; lean_object* x_253; 
x_252 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__20;
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_4);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; 
x_254 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__21;
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_4);
return x_255;
}
}
else
{
if (x_243 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__22;
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_256);
lean_ctor_set(x_257, 1, x_4);
return x_257;
}
else
{
lean_object* x_258; lean_object* x_259; 
x_258 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__23;
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_4);
return x_259;
}
}
}
}
else
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_ctor_get(x_240, 0);
lean_inc(x_260);
lean_dec(x_240);
x_261 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_260, x_2, x_3, x_4);
lean_dec(x_260);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; uint8_t x_265; uint8_t x_266; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_265 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_266 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_264 == 0)
{
if (x_265 == 0)
{
if (x_266 == 0)
{
uint8_t x_267; uint8_t x_268; lean_object* x_269; 
x_267 = 2;
x_268 = 1;
x_269 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_269, 0, x_18);
lean_ctor_set(x_269, 1, x_263);
lean_ctor_set_uint8(x_269, sizeof(void*)*2, x_267);
lean_ctor_set_uint8(x_269, sizeof(void*)*2 + 1, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*2 + 2, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*2 + 3, x_268);
lean_ctor_set(x_261, 0, x_269);
return x_261;
}
else
{
uint8_t x_270; uint8_t x_271; uint8_t x_272; lean_object* x_273; 
x_270 = 2;
x_271 = 1;
x_272 = 0;
x_273 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_273, 0, x_18);
lean_ctor_set(x_273, 1, x_263);
lean_ctor_set_uint8(x_273, sizeof(void*)*2, x_270);
lean_ctor_set_uint8(x_273, sizeof(void*)*2 + 1, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*2 + 2, x_271);
lean_ctor_set_uint8(x_273, sizeof(void*)*2 + 3, x_272);
lean_ctor_set(x_261, 0, x_273);
return x_261;
}
}
else
{
if (x_266 == 0)
{
uint8_t x_274; uint8_t x_275; uint8_t x_276; lean_object* x_277; 
x_274 = 2;
x_275 = 1;
x_276 = 0;
x_277 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_277, 0, x_18);
lean_ctor_set(x_277, 1, x_263);
lean_ctor_set_uint8(x_277, sizeof(void*)*2, x_274);
lean_ctor_set_uint8(x_277, sizeof(void*)*2 + 1, x_275);
lean_ctor_set_uint8(x_277, sizeof(void*)*2 + 2, x_276);
lean_ctor_set_uint8(x_277, sizeof(void*)*2 + 3, x_275);
lean_ctor_set(x_261, 0, x_277);
return x_261;
}
else
{
uint8_t x_278; uint8_t x_279; uint8_t x_280; lean_object* x_281; 
x_278 = 2;
x_279 = 1;
x_280 = 0;
x_281 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_281, 0, x_18);
lean_ctor_set(x_281, 1, x_263);
lean_ctor_set_uint8(x_281, sizeof(void*)*2, x_278);
lean_ctor_set_uint8(x_281, sizeof(void*)*2 + 1, x_279);
lean_ctor_set_uint8(x_281, sizeof(void*)*2 + 2, x_280);
lean_ctor_set_uint8(x_281, sizeof(void*)*2 + 3, x_280);
lean_ctor_set(x_261, 0, x_281);
return x_261;
}
}
}
else
{
if (x_265 == 0)
{
if (x_266 == 0)
{
uint8_t x_282; uint8_t x_283; uint8_t x_284; lean_object* x_285; 
x_282 = 2;
x_283 = 0;
x_284 = 1;
x_285 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_285, 0, x_18);
lean_ctor_set(x_285, 1, x_263);
lean_ctor_set_uint8(x_285, sizeof(void*)*2, x_282);
lean_ctor_set_uint8(x_285, sizeof(void*)*2 + 1, x_283);
lean_ctor_set_uint8(x_285, sizeof(void*)*2 + 2, x_284);
lean_ctor_set_uint8(x_285, sizeof(void*)*2 + 3, x_284);
lean_ctor_set(x_261, 0, x_285);
return x_261;
}
else
{
uint8_t x_286; uint8_t x_287; uint8_t x_288; lean_object* x_289; 
x_286 = 2;
x_287 = 0;
x_288 = 1;
x_289 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_289, 0, x_18);
lean_ctor_set(x_289, 1, x_263);
lean_ctor_set_uint8(x_289, sizeof(void*)*2, x_286);
lean_ctor_set_uint8(x_289, sizeof(void*)*2 + 1, x_287);
lean_ctor_set_uint8(x_289, sizeof(void*)*2 + 2, x_288);
lean_ctor_set_uint8(x_289, sizeof(void*)*2 + 3, x_287);
lean_ctor_set(x_261, 0, x_289);
return x_261;
}
}
else
{
if (x_266 == 0)
{
uint8_t x_290; uint8_t x_291; uint8_t x_292; lean_object* x_293; 
x_290 = 2;
x_291 = 0;
x_292 = 1;
x_293 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_293, 0, x_18);
lean_ctor_set(x_293, 1, x_263);
lean_ctor_set_uint8(x_293, sizeof(void*)*2, x_290);
lean_ctor_set_uint8(x_293, sizeof(void*)*2 + 1, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*2 + 2, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*2 + 3, x_292);
lean_ctor_set(x_261, 0, x_293);
return x_261;
}
else
{
uint8_t x_294; uint8_t x_295; lean_object* x_296; 
x_294 = 2;
x_295 = 0;
x_296 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_296, 0, x_18);
lean_ctor_set(x_296, 1, x_263);
lean_ctor_set_uint8(x_296, sizeof(void*)*2, x_294);
lean_ctor_set_uint8(x_296, sizeof(void*)*2 + 1, x_295);
lean_ctor_set_uint8(x_296, sizeof(void*)*2 + 2, x_295);
lean_ctor_set_uint8(x_296, sizeof(void*)*2 + 3, x_295);
lean_ctor_set(x_261, 0, x_296);
return x_261;
}
}
}
}
else
{
lean_object* x_297; lean_object* x_298; uint8_t x_299; uint8_t x_300; uint8_t x_301; 
x_297 = lean_ctor_get(x_261, 0);
x_298 = lean_ctor_get(x_261, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_261);
x_299 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_300 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_301 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_299 == 0)
{
if (x_300 == 0)
{
if (x_301 == 0)
{
uint8_t x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; 
x_302 = 2;
x_303 = 1;
x_304 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_304, 0, x_18);
lean_ctor_set(x_304, 1, x_297);
lean_ctor_set_uint8(x_304, sizeof(void*)*2, x_302);
lean_ctor_set_uint8(x_304, sizeof(void*)*2 + 1, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*2 + 2, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*2 + 3, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_298);
return x_305;
}
else
{
uint8_t x_306; uint8_t x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; 
x_306 = 2;
x_307 = 1;
x_308 = 0;
x_309 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_309, 0, x_18);
lean_ctor_set(x_309, 1, x_297);
lean_ctor_set_uint8(x_309, sizeof(void*)*2, x_306);
lean_ctor_set_uint8(x_309, sizeof(void*)*2 + 1, x_307);
lean_ctor_set_uint8(x_309, sizeof(void*)*2 + 2, x_307);
lean_ctor_set_uint8(x_309, sizeof(void*)*2 + 3, x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_298);
return x_310;
}
}
else
{
if (x_301 == 0)
{
uint8_t x_311; uint8_t x_312; uint8_t x_313; lean_object* x_314; lean_object* x_315; 
x_311 = 2;
x_312 = 1;
x_313 = 0;
x_314 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_314, 0, x_18);
lean_ctor_set(x_314, 1, x_297);
lean_ctor_set_uint8(x_314, sizeof(void*)*2, x_311);
lean_ctor_set_uint8(x_314, sizeof(void*)*2 + 1, x_312);
lean_ctor_set_uint8(x_314, sizeof(void*)*2 + 2, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*2 + 3, x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_298);
return x_315;
}
else
{
uint8_t x_316; uint8_t x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; 
x_316 = 2;
x_317 = 1;
x_318 = 0;
x_319 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_319, 0, x_18);
lean_ctor_set(x_319, 1, x_297);
lean_ctor_set_uint8(x_319, sizeof(void*)*2, x_316);
lean_ctor_set_uint8(x_319, sizeof(void*)*2 + 1, x_317);
lean_ctor_set_uint8(x_319, sizeof(void*)*2 + 2, x_318);
lean_ctor_set_uint8(x_319, sizeof(void*)*2 + 3, x_318);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_320, 1, x_298);
return x_320;
}
}
}
else
{
if (x_300 == 0)
{
if (x_301 == 0)
{
uint8_t x_321; uint8_t x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; 
x_321 = 2;
x_322 = 0;
x_323 = 1;
x_324 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_324, 0, x_18);
lean_ctor_set(x_324, 1, x_297);
lean_ctor_set_uint8(x_324, sizeof(void*)*2, x_321);
lean_ctor_set_uint8(x_324, sizeof(void*)*2 + 1, x_322);
lean_ctor_set_uint8(x_324, sizeof(void*)*2 + 2, x_323);
lean_ctor_set_uint8(x_324, sizeof(void*)*2 + 3, x_323);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_298);
return x_325;
}
else
{
uint8_t x_326; uint8_t x_327; uint8_t x_328; lean_object* x_329; lean_object* x_330; 
x_326 = 2;
x_327 = 0;
x_328 = 1;
x_329 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_329, 0, x_18);
lean_ctor_set(x_329, 1, x_297);
lean_ctor_set_uint8(x_329, sizeof(void*)*2, x_326);
lean_ctor_set_uint8(x_329, sizeof(void*)*2 + 1, x_327);
lean_ctor_set_uint8(x_329, sizeof(void*)*2 + 2, x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*2 + 3, x_327);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_298);
return x_330;
}
}
else
{
if (x_301 == 0)
{
uint8_t x_331; uint8_t x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; 
x_331 = 2;
x_332 = 0;
x_333 = 1;
x_334 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_334, 0, x_18);
lean_ctor_set(x_334, 1, x_297);
lean_ctor_set_uint8(x_334, sizeof(void*)*2, x_331);
lean_ctor_set_uint8(x_334, sizeof(void*)*2 + 1, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*2 + 2, x_332);
lean_ctor_set_uint8(x_334, sizeof(void*)*2 + 3, x_333);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_298);
return x_335;
}
else
{
uint8_t x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; 
x_336 = 2;
x_337 = 0;
x_338 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_338, 0, x_18);
lean_ctor_set(x_338, 1, x_297);
lean_ctor_set_uint8(x_338, sizeof(void*)*2, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*2 + 1, x_337);
lean_ctor_set_uint8(x_338, sizeof(void*)*2 + 2, x_337);
lean_ctor_set_uint8(x_338, sizeof(void*)*2 + 3, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_298);
return x_339;
}
}
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_340 = !lean_is_exclusive(x_261);
if (x_340 == 0)
{
return x_261;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_261, 0);
x_342 = lean_ctor_get(x_261, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_261);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
}
}
}
else
{
uint8_t x_344; 
x_344 = !lean_is_exclusive(x_17);
if (x_344 == 0)
{
lean_object* x_345; lean_object* x_346; lean_object* x_363; 
x_345 = lean_ctor_get(x_17, 0);
x_363 = l_Lean_Syntax_getArg(x_345, x_7);
if (lean_obj_tag(x_363) == 2)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_dec(x_345);
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec(x_363);
x_365 = lean_string_utf8_byte_size(x_364);
x_366 = lean_nat_sub(x_365, x_9);
lean_dec(x_365);
x_367 = lean_string_utf8_extract(x_364, x_5, x_366);
lean_dec(x_366);
lean_dec(x_364);
lean_ctor_set(x_17, 0, x_367);
x_368 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; 
x_369 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_369) == 0)
{
uint8_t x_370; uint8_t x_371; uint8_t x_372; 
lean_dec(x_2);
x_370 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_371 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_372 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_370 == 0)
{
if (x_371 == 0)
{
if (x_372 == 0)
{
uint8_t x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_373 = 0;
x_374 = 1;
x_375 = l_Array_empty___closed__1;
x_376 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_376, 0, x_17);
lean_ctor_set(x_376, 1, x_375);
lean_ctor_set_uint8(x_376, sizeof(void*)*2, x_373);
lean_ctor_set_uint8(x_376, sizeof(void*)*2 + 1, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*2 + 2, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*2 + 3, x_374);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_4);
return x_377;
}
else
{
uint8_t x_378; uint8_t x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_378 = 0;
x_379 = 1;
x_380 = 0;
x_381 = l_Array_empty___closed__1;
x_382 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_382, 0, x_17);
lean_ctor_set(x_382, 1, x_381);
lean_ctor_set_uint8(x_382, sizeof(void*)*2, x_378);
lean_ctor_set_uint8(x_382, sizeof(void*)*2 + 1, x_379);
lean_ctor_set_uint8(x_382, sizeof(void*)*2 + 2, x_379);
lean_ctor_set_uint8(x_382, sizeof(void*)*2 + 3, x_380);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_4);
return x_383;
}
}
else
{
if (x_372 == 0)
{
uint8_t x_384; uint8_t x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_384 = 0;
x_385 = 1;
x_386 = 0;
x_387 = l_Array_empty___closed__1;
x_388 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_388, 0, x_17);
lean_ctor_set(x_388, 1, x_387);
lean_ctor_set_uint8(x_388, sizeof(void*)*2, x_384);
lean_ctor_set_uint8(x_388, sizeof(void*)*2 + 1, x_385);
lean_ctor_set_uint8(x_388, sizeof(void*)*2 + 2, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*2 + 3, x_385);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_4);
return x_389;
}
else
{
uint8_t x_390; uint8_t x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_390 = 0;
x_391 = 1;
x_392 = 0;
x_393 = l_Array_empty___closed__1;
x_394 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_394, 0, x_17);
lean_ctor_set(x_394, 1, x_393);
lean_ctor_set_uint8(x_394, sizeof(void*)*2, x_390);
lean_ctor_set_uint8(x_394, sizeof(void*)*2 + 1, x_391);
lean_ctor_set_uint8(x_394, sizeof(void*)*2 + 2, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*2 + 3, x_392);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_4);
return x_395;
}
}
}
else
{
if (x_371 == 0)
{
if (x_372 == 0)
{
uint8_t x_396; uint8_t x_397; uint8_t x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_396 = 0;
x_397 = 0;
x_398 = 1;
x_399 = l_Array_empty___closed__1;
x_400 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_400, 0, x_17);
lean_ctor_set(x_400, 1, x_399);
lean_ctor_set_uint8(x_400, sizeof(void*)*2, x_396);
lean_ctor_set_uint8(x_400, sizeof(void*)*2 + 1, x_397);
lean_ctor_set_uint8(x_400, sizeof(void*)*2 + 2, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*2 + 3, x_398);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_4);
return x_401;
}
else
{
uint8_t x_402; uint8_t x_403; uint8_t x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_402 = 0;
x_403 = 0;
x_404 = 1;
x_405 = l_Array_empty___closed__1;
x_406 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_406, 0, x_17);
lean_ctor_set(x_406, 1, x_405);
lean_ctor_set_uint8(x_406, sizeof(void*)*2, x_402);
lean_ctor_set_uint8(x_406, sizeof(void*)*2 + 1, x_403);
lean_ctor_set_uint8(x_406, sizeof(void*)*2 + 2, x_404);
lean_ctor_set_uint8(x_406, sizeof(void*)*2 + 3, x_403);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_4);
return x_407;
}
}
else
{
if (x_372 == 0)
{
uint8_t x_408; uint8_t x_409; uint8_t x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_408 = 0;
x_409 = 0;
x_410 = 1;
x_411 = l_Array_empty___closed__1;
x_412 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_412, 0, x_17);
lean_ctor_set(x_412, 1, x_411);
lean_ctor_set_uint8(x_412, sizeof(void*)*2, x_408);
lean_ctor_set_uint8(x_412, sizeof(void*)*2 + 1, x_409);
lean_ctor_set_uint8(x_412, sizeof(void*)*2 + 2, x_409);
lean_ctor_set_uint8(x_412, sizeof(void*)*2 + 3, x_410);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_4);
return x_413;
}
else
{
uint8_t x_414; uint8_t x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_414 = 0;
x_415 = 0;
x_416 = l_Array_empty___closed__1;
x_417 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_417, 0, x_17);
lean_ctor_set(x_417, 1, x_416);
lean_ctor_set_uint8(x_417, sizeof(void*)*2, x_414);
lean_ctor_set_uint8(x_417, sizeof(void*)*2 + 1, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*2 + 2, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*2 + 3, x_415);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_4);
return x_418;
}
}
}
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_369, 0);
lean_inc(x_419);
lean_dec(x_369);
x_420 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_419, x_2, x_3, x_4);
lean_dec(x_419);
if (lean_obj_tag(x_420) == 0)
{
uint8_t x_421; 
x_421 = !lean_is_exclusive(x_420);
if (x_421 == 0)
{
lean_object* x_422; uint8_t x_423; uint8_t x_424; uint8_t x_425; 
x_422 = lean_ctor_get(x_420, 0);
x_423 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_424 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_425 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_423 == 0)
{
if (x_424 == 0)
{
if (x_425 == 0)
{
uint8_t x_426; uint8_t x_427; lean_object* x_428; 
x_426 = 0;
x_427 = 1;
x_428 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_428, 0, x_17);
lean_ctor_set(x_428, 1, x_422);
lean_ctor_set_uint8(x_428, sizeof(void*)*2, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*2 + 1, x_427);
lean_ctor_set_uint8(x_428, sizeof(void*)*2 + 2, x_427);
lean_ctor_set_uint8(x_428, sizeof(void*)*2 + 3, x_427);
lean_ctor_set(x_420, 0, x_428);
return x_420;
}
else
{
uint8_t x_429; uint8_t x_430; uint8_t x_431; lean_object* x_432; 
x_429 = 0;
x_430 = 1;
x_431 = 0;
x_432 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_432, 0, x_17);
lean_ctor_set(x_432, 1, x_422);
lean_ctor_set_uint8(x_432, sizeof(void*)*2, x_429);
lean_ctor_set_uint8(x_432, sizeof(void*)*2 + 1, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*2 + 2, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*2 + 3, x_431);
lean_ctor_set(x_420, 0, x_432);
return x_420;
}
}
else
{
if (x_425 == 0)
{
uint8_t x_433; uint8_t x_434; uint8_t x_435; lean_object* x_436; 
x_433 = 0;
x_434 = 1;
x_435 = 0;
x_436 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_436, 0, x_17);
lean_ctor_set(x_436, 1, x_422);
lean_ctor_set_uint8(x_436, sizeof(void*)*2, x_433);
lean_ctor_set_uint8(x_436, sizeof(void*)*2 + 1, x_434);
lean_ctor_set_uint8(x_436, sizeof(void*)*2 + 2, x_435);
lean_ctor_set_uint8(x_436, sizeof(void*)*2 + 3, x_434);
lean_ctor_set(x_420, 0, x_436);
return x_420;
}
else
{
uint8_t x_437; uint8_t x_438; uint8_t x_439; lean_object* x_440; 
x_437 = 0;
x_438 = 1;
x_439 = 0;
x_440 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_440, 0, x_17);
lean_ctor_set(x_440, 1, x_422);
lean_ctor_set_uint8(x_440, sizeof(void*)*2, x_437);
lean_ctor_set_uint8(x_440, sizeof(void*)*2 + 1, x_438);
lean_ctor_set_uint8(x_440, sizeof(void*)*2 + 2, x_439);
lean_ctor_set_uint8(x_440, sizeof(void*)*2 + 3, x_439);
lean_ctor_set(x_420, 0, x_440);
return x_420;
}
}
}
else
{
if (x_424 == 0)
{
if (x_425 == 0)
{
uint8_t x_441; uint8_t x_442; uint8_t x_443; lean_object* x_444; 
x_441 = 0;
x_442 = 0;
x_443 = 1;
x_444 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_444, 0, x_17);
lean_ctor_set(x_444, 1, x_422);
lean_ctor_set_uint8(x_444, sizeof(void*)*2, x_441);
lean_ctor_set_uint8(x_444, sizeof(void*)*2 + 1, x_442);
lean_ctor_set_uint8(x_444, sizeof(void*)*2 + 2, x_443);
lean_ctor_set_uint8(x_444, sizeof(void*)*2 + 3, x_443);
lean_ctor_set(x_420, 0, x_444);
return x_420;
}
else
{
uint8_t x_445; uint8_t x_446; uint8_t x_447; lean_object* x_448; 
x_445 = 0;
x_446 = 0;
x_447 = 1;
x_448 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_448, 0, x_17);
lean_ctor_set(x_448, 1, x_422);
lean_ctor_set_uint8(x_448, sizeof(void*)*2, x_445);
lean_ctor_set_uint8(x_448, sizeof(void*)*2 + 1, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*2 + 2, x_447);
lean_ctor_set_uint8(x_448, sizeof(void*)*2 + 3, x_446);
lean_ctor_set(x_420, 0, x_448);
return x_420;
}
}
else
{
if (x_425 == 0)
{
uint8_t x_449; uint8_t x_450; uint8_t x_451; lean_object* x_452; 
x_449 = 0;
x_450 = 0;
x_451 = 1;
x_452 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_452, 0, x_17);
lean_ctor_set(x_452, 1, x_422);
lean_ctor_set_uint8(x_452, sizeof(void*)*2, x_449);
lean_ctor_set_uint8(x_452, sizeof(void*)*2 + 1, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*2 + 2, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*2 + 3, x_451);
lean_ctor_set(x_420, 0, x_452);
return x_420;
}
else
{
uint8_t x_453; uint8_t x_454; lean_object* x_455; 
x_453 = 0;
x_454 = 0;
x_455 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_455, 0, x_17);
lean_ctor_set(x_455, 1, x_422);
lean_ctor_set_uint8(x_455, sizeof(void*)*2, x_453);
lean_ctor_set_uint8(x_455, sizeof(void*)*2 + 1, x_454);
lean_ctor_set_uint8(x_455, sizeof(void*)*2 + 2, x_454);
lean_ctor_set_uint8(x_455, sizeof(void*)*2 + 3, x_454);
lean_ctor_set(x_420, 0, x_455);
return x_420;
}
}
}
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; uint8_t x_459; uint8_t x_460; 
x_456 = lean_ctor_get(x_420, 0);
x_457 = lean_ctor_get(x_420, 1);
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_420);
x_458 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_459 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_460 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_458 == 0)
{
if (x_459 == 0)
{
if (x_460 == 0)
{
uint8_t x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; 
x_461 = 0;
x_462 = 1;
x_463 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_463, 0, x_17);
lean_ctor_set(x_463, 1, x_456);
lean_ctor_set_uint8(x_463, sizeof(void*)*2, x_461);
lean_ctor_set_uint8(x_463, sizeof(void*)*2 + 1, x_462);
lean_ctor_set_uint8(x_463, sizeof(void*)*2 + 2, x_462);
lean_ctor_set_uint8(x_463, sizeof(void*)*2 + 3, x_462);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_457);
return x_464;
}
else
{
uint8_t x_465; uint8_t x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; 
x_465 = 0;
x_466 = 1;
x_467 = 0;
x_468 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_468, 0, x_17);
lean_ctor_set(x_468, 1, x_456);
lean_ctor_set_uint8(x_468, sizeof(void*)*2, x_465);
lean_ctor_set_uint8(x_468, sizeof(void*)*2 + 1, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*2 + 2, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*2 + 3, x_467);
x_469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_469, 0, x_468);
lean_ctor_set(x_469, 1, x_457);
return x_469;
}
}
else
{
if (x_460 == 0)
{
uint8_t x_470; uint8_t x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; 
x_470 = 0;
x_471 = 1;
x_472 = 0;
x_473 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_473, 0, x_17);
lean_ctor_set(x_473, 1, x_456);
lean_ctor_set_uint8(x_473, sizeof(void*)*2, x_470);
lean_ctor_set_uint8(x_473, sizeof(void*)*2 + 1, x_471);
lean_ctor_set_uint8(x_473, sizeof(void*)*2 + 2, x_472);
lean_ctor_set_uint8(x_473, sizeof(void*)*2 + 3, x_471);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_457);
return x_474;
}
else
{
uint8_t x_475; uint8_t x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; 
x_475 = 0;
x_476 = 1;
x_477 = 0;
x_478 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_478, 0, x_17);
lean_ctor_set(x_478, 1, x_456);
lean_ctor_set_uint8(x_478, sizeof(void*)*2, x_475);
lean_ctor_set_uint8(x_478, sizeof(void*)*2 + 1, x_476);
lean_ctor_set_uint8(x_478, sizeof(void*)*2 + 2, x_477);
lean_ctor_set_uint8(x_478, sizeof(void*)*2 + 3, x_477);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_457);
return x_479;
}
}
}
else
{
if (x_459 == 0)
{
if (x_460 == 0)
{
uint8_t x_480; uint8_t x_481; uint8_t x_482; lean_object* x_483; lean_object* x_484; 
x_480 = 0;
x_481 = 0;
x_482 = 1;
x_483 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_483, 0, x_17);
lean_ctor_set(x_483, 1, x_456);
lean_ctor_set_uint8(x_483, sizeof(void*)*2, x_480);
lean_ctor_set_uint8(x_483, sizeof(void*)*2 + 1, x_481);
lean_ctor_set_uint8(x_483, sizeof(void*)*2 + 2, x_482);
lean_ctor_set_uint8(x_483, sizeof(void*)*2 + 3, x_482);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_457);
return x_484;
}
else
{
uint8_t x_485; uint8_t x_486; uint8_t x_487; lean_object* x_488; lean_object* x_489; 
x_485 = 0;
x_486 = 0;
x_487 = 1;
x_488 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_488, 0, x_17);
lean_ctor_set(x_488, 1, x_456);
lean_ctor_set_uint8(x_488, sizeof(void*)*2, x_485);
lean_ctor_set_uint8(x_488, sizeof(void*)*2 + 1, x_486);
lean_ctor_set_uint8(x_488, sizeof(void*)*2 + 2, x_487);
lean_ctor_set_uint8(x_488, sizeof(void*)*2 + 3, x_486);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_457);
return x_489;
}
}
else
{
if (x_460 == 0)
{
uint8_t x_490; uint8_t x_491; uint8_t x_492; lean_object* x_493; lean_object* x_494; 
x_490 = 0;
x_491 = 0;
x_492 = 1;
x_493 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_493, 0, x_17);
lean_ctor_set(x_493, 1, x_456);
lean_ctor_set_uint8(x_493, sizeof(void*)*2, x_490);
lean_ctor_set_uint8(x_493, sizeof(void*)*2 + 1, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*2 + 2, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*2 + 3, x_492);
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_457);
return x_494;
}
else
{
uint8_t x_495; uint8_t x_496; lean_object* x_497; lean_object* x_498; 
x_495 = 0;
x_496 = 0;
x_497 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_497, 0, x_17);
lean_ctor_set(x_497, 1, x_456);
lean_ctor_set_uint8(x_497, sizeof(void*)*2, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*2 + 1, x_496);
lean_ctor_set_uint8(x_497, sizeof(void*)*2 + 2, x_496);
lean_ctor_set_uint8(x_497, sizeof(void*)*2 + 3, x_496);
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_497);
lean_ctor_set(x_498, 1, x_457);
return x_498;
}
}
}
}
}
else
{
uint8_t x_499; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_499 = !lean_is_exclusive(x_420);
if (x_499 == 0)
{
return x_420;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_500 = lean_ctor_get(x_420, 0);
x_501 = lean_ctor_get(x_420, 1);
lean_inc(x_501);
lean_inc(x_500);
lean_dec(x_420);
x_502 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set(x_502, 1, x_501);
return x_502;
}
}
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; 
x_503 = lean_ctor_get(x_368, 0);
lean_inc(x_503);
lean_dec(x_368);
lean_inc(x_503);
x_504 = l_Lean_Syntax_getKind(x_503);
x_505 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3;
x_506 = lean_name_eq(x_504, x_505);
if (x_506 == 0)
{
lean_object* x_507; uint8_t x_508; 
x_507 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4;
x_508 = lean_name_eq(x_504, x_507);
lean_dec(x_504);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
x_509 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7;
x_510 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(x_503, x_509, x_2, x_3, x_4);
lean_dec(x_503);
x_511 = !lean_is_exclusive(x_510);
if (x_511 == 0)
{
return x_510;
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
x_512 = lean_ctor_get(x_510, 0);
x_513 = lean_ctor_get(x_510, 1);
lean_inc(x_513);
lean_inc(x_512);
lean_dec(x_510);
x_514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
return x_514;
}
}
else
{
lean_object* x_515; 
lean_dec(x_503);
x_515 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_515) == 0)
{
uint8_t x_516; uint8_t x_517; uint8_t x_518; 
lean_dec(x_2);
x_516 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_517 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_518 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_516 == 0)
{
if (x_517 == 0)
{
if (x_518 == 0)
{
uint8_t x_519; uint8_t x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_519 = 1;
x_520 = 1;
x_521 = l_Array_empty___closed__1;
x_522 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_522, 0, x_17);
lean_ctor_set(x_522, 1, x_521);
lean_ctor_set_uint8(x_522, sizeof(void*)*2, x_519);
lean_ctor_set_uint8(x_522, sizeof(void*)*2 + 1, x_520);
lean_ctor_set_uint8(x_522, sizeof(void*)*2 + 2, x_520);
lean_ctor_set_uint8(x_522, sizeof(void*)*2 + 3, x_520);
x_523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_4);
return x_523;
}
else
{
uint8_t x_524; uint8_t x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_524 = 1;
x_525 = 1;
x_526 = 0;
x_527 = l_Array_empty___closed__1;
x_528 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_528, 0, x_17);
lean_ctor_set(x_528, 1, x_527);
lean_ctor_set_uint8(x_528, sizeof(void*)*2, x_524);
lean_ctor_set_uint8(x_528, sizeof(void*)*2 + 1, x_525);
lean_ctor_set_uint8(x_528, sizeof(void*)*2 + 2, x_525);
lean_ctor_set_uint8(x_528, sizeof(void*)*2 + 3, x_526);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_4);
return x_529;
}
}
else
{
if (x_518 == 0)
{
uint8_t x_530; uint8_t x_531; uint8_t x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_530 = 1;
x_531 = 1;
x_532 = 0;
x_533 = l_Array_empty___closed__1;
x_534 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_534, 0, x_17);
lean_ctor_set(x_534, 1, x_533);
lean_ctor_set_uint8(x_534, sizeof(void*)*2, x_530);
lean_ctor_set_uint8(x_534, sizeof(void*)*2 + 1, x_531);
lean_ctor_set_uint8(x_534, sizeof(void*)*2 + 2, x_532);
lean_ctor_set_uint8(x_534, sizeof(void*)*2 + 3, x_531);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_534);
lean_ctor_set(x_535, 1, x_4);
return x_535;
}
else
{
uint8_t x_536; uint8_t x_537; uint8_t x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_536 = 1;
x_537 = 1;
x_538 = 0;
x_539 = l_Array_empty___closed__1;
x_540 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_540, 0, x_17);
lean_ctor_set(x_540, 1, x_539);
lean_ctor_set_uint8(x_540, sizeof(void*)*2, x_536);
lean_ctor_set_uint8(x_540, sizeof(void*)*2 + 1, x_537);
lean_ctor_set_uint8(x_540, sizeof(void*)*2 + 2, x_538);
lean_ctor_set_uint8(x_540, sizeof(void*)*2 + 3, x_538);
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_4);
return x_541;
}
}
}
else
{
if (x_517 == 0)
{
if (x_518 == 0)
{
uint8_t x_542; uint8_t x_543; uint8_t x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_542 = 1;
x_543 = 0;
x_544 = 1;
x_545 = l_Array_empty___closed__1;
x_546 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_546, 0, x_17);
lean_ctor_set(x_546, 1, x_545);
lean_ctor_set_uint8(x_546, sizeof(void*)*2, x_542);
lean_ctor_set_uint8(x_546, sizeof(void*)*2 + 1, x_543);
lean_ctor_set_uint8(x_546, sizeof(void*)*2 + 2, x_544);
lean_ctor_set_uint8(x_546, sizeof(void*)*2 + 3, x_544);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_4);
return x_547;
}
else
{
uint8_t x_548; uint8_t x_549; uint8_t x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_548 = 1;
x_549 = 0;
x_550 = 1;
x_551 = l_Array_empty___closed__1;
x_552 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_552, 0, x_17);
lean_ctor_set(x_552, 1, x_551);
lean_ctor_set_uint8(x_552, sizeof(void*)*2, x_548);
lean_ctor_set_uint8(x_552, sizeof(void*)*2 + 1, x_549);
lean_ctor_set_uint8(x_552, sizeof(void*)*2 + 2, x_550);
lean_ctor_set_uint8(x_552, sizeof(void*)*2 + 3, x_549);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_4);
return x_553;
}
}
else
{
if (x_518 == 0)
{
uint8_t x_554; uint8_t x_555; uint8_t x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_554 = 1;
x_555 = 0;
x_556 = 1;
x_557 = l_Array_empty___closed__1;
x_558 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_558, 0, x_17);
lean_ctor_set(x_558, 1, x_557);
lean_ctor_set_uint8(x_558, sizeof(void*)*2, x_554);
lean_ctor_set_uint8(x_558, sizeof(void*)*2 + 1, x_555);
lean_ctor_set_uint8(x_558, sizeof(void*)*2 + 2, x_555);
lean_ctor_set_uint8(x_558, sizeof(void*)*2 + 3, x_556);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_558);
lean_ctor_set(x_559, 1, x_4);
return x_559;
}
else
{
uint8_t x_560; uint8_t x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_560 = 1;
x_561 = 0;
x_562 = l_Array_empty___closed__1;
x_563 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_563, 0, x_17);
lean_ctor_set(x_563, 1, x_562);
lean_ctor_set_uint8(x_563, sizeof(void*)*2, x_560);
lean_ctor_set_uint8(x_563, sizeof(void*)*2 + 1, x_561);
lean_ctor_set_uint8(x_563, sizeof(void*)*2 + 2, x_561);
lean_ctor_set_uint8(x_563, sizeof(void*)*2 + 3, x_561);
x_564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_564, 0, x_563);
lean_ctor_set(x_564, 1, x_4);
return x_564;
}
}
}
}
else
{
lean_object* x_565; lean_object* x_566; 
x_565 = lean_ctor_get(x_515, 0);
lean_inc(x_565);
lean_dec(x_515);
x_566 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_565, x_2, x_3, x_4);
lean_dec(x_565);
if (lean_obj_tag(x_566) == 0)
{
uint8_t x_567; 
x_567 = !lean_is_exclusive(x_566);
if (x_567 == 0)
{
lean_object* x_568; uint8_t x_569; uint8_t x_570; uint8_t x_571; 
x_568 = lean_ctor_get(x_566, 0);
x_569 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_570 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_571 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_569 == 0)
{
if (x_570 == 0)
{
if (x_571 == 0)
{
uint8_t x_572; uint8_t x_573; lean_object* x_574; 
x_572 = 1;
x_573 = 1;
x_574 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_574, 0, x_17);
lean_ctor_set(x_574, 1, x_568);
lean_ctor_set_uint8(x_574, sizeof(void*)*2, x_572);
lean_ctor_set_uint8(x_574, sizeof(void*)*2 + 1, x_573);
lean_ctor_set_uint8(x_574, sizeof(void*)*2 + 2, x_573);
lean_ctor_set_uint8(x_574, sizeof(void*)*2 + 3, x_573);
lean_ctor_set(x_566, 0, x_574);
return x_566;
}
else
{
uint8_t x_575; uint8_t x_576; uint8_t x_577; lean_object* x_578; 
x_575 = 1;
x_576 = 1;
x_577 = 0;
x_578 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_578, 0, x_17);
lean_ctor_set(x_578, 1, x_568);
lean_ctor_set_uint8(x_578, sizeof(void*)*2, x_575);
lean_ctor_set_uint8(x_578, sizeof(void*)*2 + 1, x_576);
lean_ctor_set_uint8(x_578, sizeof(void*)*2 + 2, x_576);
lean_ctor_set_uint8(x_578, sizeof(void*)*2 + 3, x_577);
lean_ctor_set(x_566, 0, x_578);
return x_566;
}
}
else
{
if (x_571 == 0)
{
uint8_t x_579; uint8_t x_580; uint8_t x_581; lean_object* x_582; 
x_579 = 1;
x_580 = 1;
x_581 = 0;
x_582 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_582, 0, x_17);
lean_ctor_set(x_582, 1, x_568);
lean_ctor_set_uint8(x_582, sizeof(void*)*2, x_579);
lean_ctor_set_uint8(x_582, sizeof(void*)*2 + 1, x_580);
lean_ctor_set_uint8(x_582, sizeof(void*)*2 + 2, x_581);
lean_ctor_set_uint8(x_582, sizeof(void*)*2 + 3, x_580);
lean_ctor_set(x_566, 0, x_582);
return x_566;
}
else
{
uint8_t x_583; uint8_t x_584; uint8_t x_585; lean_object* x_586; 
x_583 = 1;
x_584 = 1;
x_585 = 0;
x_586 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_586, 0, x_17);
lean_ctor_set(x_586, 1, x_568);
lean_ctor_set_uint8(x_586, sizeof(void*)*2, x_583);
lean_ctor_set_uint8(x_586, sizeof(void*)*2 + 1, x_584);
lean_ctor_set_uint8(x_586, sizeof(void*)*2 + 2, x_585);
lean_ctor_set_uint8(x_586, sizeof(void*)*2 + 3, x_585);
lean_ctor_set(x_566, 0, x_586);
return x_566;
}
}
}
else
{
if (x_570 == 0)
{
if (x_571 == 0)
{
uint8_t x_587; uint8_t x_588; uint8_t x_589; lean_object* x_590; 
x_587 = 1;
x_588 = 0;
x_589 = 1;
x_590 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_590, 0, x_17);
lean_ctor_set(x_590, 1, x_568);
lean_ctor_set_uint8(x_590, sizeof(void*)*2, x_587);
lean_ctor_set_uint8(x_590, sizeof(void*)*2 + 1, x_588);
lean_ctor_set_uint8(x_590, sizeof(void*)*2 + 2, x_589);
lean_ctor_set_uint8(x_590, sizeof(void*)*2 + 3, x_589);
lean_ctor_set(x_566, 0, x_590);
return x_566;
}
else
{
uint8_t x_591; uint8_t x_592; uint8_t x_593; lean_object* x_594; 
x_591 = 1;
x_592 = 0;
x_593 = 1;
x_594 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_594, 0, x_17);
lean_ctor_set(x_594, 1, x_568);
lean_ctor_set_uint8(x_594, sizeof(void*)*2, x_591);
lean_ctor_set_uint8(x_594, sizeof(void*)*2 + 1, x_592);
lean_ctor_set_uint8(x_594, sizeof(void*)*2 + 2, x_593);
lean_ctor_set_uint8(x_594, sizeof(void*)*2 + 3, x_592);
lean_ctor_set(x_566, 0, x_594);
return x_566;
}
}
else
{
if (x_571 == 0)
{
uint8_t x_595; uint8_t x_596; uint8_t x_597; lean_object* x_598; 
x_595 = 1;
x_596 = 0;
x_597 = 1;
x_598 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_598, 0, x_17);
lean_ctor_set(x_598, 1, x_568);
lean_ctor_set_uint8(x_598, sizeof(void*)*2, x_595);
lean_ctor_set_uint8(x_598, sizeof(void*)*2 + 1, x_596);
lean_ctor_set_uint8(x_598, sizeof(void*)*2 + 2, x_596);
lean_ctor_set_uint8(x_598, sizeof(void*)*2 + 3, x_597);
lean_ctor_set(x_566, 0, x_598);
return x_566;
}
else
{
uint8_t x_599; uint8_t x_600; lean_object* x_601; 
x_599 = 1;
x_600 = 0;
x_601 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_601, 0, x_17);
lean_ctor_set(x_601, 1, x_568);
lean_ctor_set_uint8(x_601, sizeof(void*)*2, x_599);
lean_ctor_set_uint8(x_601, sizeof(void*)*2 + 1, x_600);
lean_ctor_set_uint8(x_601, sizeof(void*)*2 + 2, x_600);
lean_ctor_set_uint8(x_601, sizeof(void*)*2 + 3, x_600);
lean_ctor_set(x_566, 0, x_601);
return x_566;
}
}
}
}
else
{
lean_object* x_602; lean_object* x_603; uint8_t x_604; uint8_t x_605; uint8_t x_606; 
x_602 = lean_ctor_get(x_566, 0);
x_603 = lean_ctor_get(x_566, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_566);
x_604 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_605 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_606 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_604 == 0)
{
if (x_605 == 0)
{
if (x_606 == 0)
{
uint8_t x_607; uint8_t x_608; lean_object* x_609; lean_object* x_610; 
x_607 = 1;
x_608 = 1;
x_609 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_609, 0, x_17);
lean_ctor_set(x_609, 1, x_602);
lean_ctor_set_uint8(x_609, sizeof(void*)*2, x_607);
lean_ctor_set_uint8(x_609, sizeof(void*)*2 + 1, x_608);
lean_ctor_set_uint8(x_609, sizeof(void*)*2 + 2, x_608);
lean_ctor_set_uint8(x_609, sizeof(void*)*2 + 3, x_608);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_603);
return x_610;
}
else
{
uint8_t x_611; uint8_t x_612; uint8_t x_613; lean_object* x_614; lean_object* x_615; 
x_611 = 1;
x_612 = 1;
x_613 = 0;
x_614 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_614, 0, x_17);
lean_ctor_set(x_614, 1, x_602);
lean_ctor_set_uint8(x_614, sizeof(void*)*2, x_611);
lean_ctor_set_uint8(x_614, sizeof(void*)*2 + 1, x_612);
lean_ctor_set_uint8(x_614, sizeof(void*)*2 + 2, x_612);
lean_ctor_set_uint8(x_614, sizeof(void*)*2 + 3, x_613);
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_614);
lean_ctor_set(x_615, 1, x_603);
return x_615;
}
}
else
{
if (x_606 == 0)
{
uint8_t x_616; uint8_t x_617; uint8_t x_618; lean_object* x_619; lean_object* x_620; 
x_616 = 1;
x_617 = 1;
x_618 = 0;
x_619 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_619, 0, x_17);
lean_ctor_set(x_619, 1, x_602);
lean_ctor_set_uint8(x_619, sizeof(void*)*2, x_616);
lean_ctor_set_uint8(x_619, sizeof(void*)*2 + 1, x_617);
lean_ctor_set_uint8(x_619, sizeof(void*)*2 + 2, x_618);
lean_ctor_set_uint8(x_619, sizeof(void*)*2 + 3, x_617);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_603);
return x_620;
}
else
{
uint8_t x_621; uint8_t x_622; uint8_t x_623; lean_object* x_624; lean_object* x_625; 
x_621 = 1;
x_622 = 1;
x_623 = 0;
x_624 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_624, 0, x_17);
lean_ctor_set(x_624, 1, x_602);
lean_ctor_set_uint8(x_624, sizeof(void*)*2, x_621);
lean_ctor_set_uint8(x_624, sizeof(void*)*2 + 1, x_622);
lean_ctor_set_uint8(x_624, sizeof(void*)*2 + 2, x_623);
lean_ctor_set_uint8(x_624, sizeof(void*)*2 + 3, x_623);
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_624);
lean_ctor_set(x_625, 1, x_603);
return x_625;
}
}
}
else
{
if (x_605 == 0)
{
if (x_606 == 0)
{
uint8_t x_626; uint8_t x_627; uint8_t x_628; lean_object* x_629; lean_object* x_630; 
x_626 = 1;
x_627 = 0;
x_628 = 1;
x_629 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_629, 0, x_17);
lean_ctor_set(x_629, 1, x_602);
lean_ctor_set_uint8(x_629, sizeof(void*)*2, x_626);
lean_ctor_set_uint8(x_629, sizeof(void*)*2 + 1, x_627);
lean_ctor_set_uint8(x_629, sizeof(void*)*2 + 2, x_628);
lean_ctor_set_uint8(x_629, sizeof(void*)*2 + 3, x_628);
x_630 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_630, 1, x_603);
return x_630;
}
else
{
uint8_t x_631; uint8_t x_632; uint8_t x_633; lean_object* x_634; lean_object* x_635; 
x_631 = 1;
x_632 = 0;
x_633 = 1;
x_634 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_634, 0, x_17);
lean_ctor_set(x_634, 1, x_602);
lean_ctor_set_uint8(x_634, sizeof(void*)*2, x_631);
lean_ctor_set_uint8(x_634, sizeof(void*)*2 + 1, x_632);
lean_ctor_set_uint8(x_634, sizeof(void*)*2 + 2, x_633);
lean_ctor_set_uint8(x_634, sizeof(void*)*2 + 3, x_632);
x_635 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_603);
return x_635;
}
}
else
{
if (x_606 == 0)
{
uint8_t x_636; uint8_t x_637; uint8_t x_638; lean_object* x_639; lean_object* x_640; 
x_636 = 1;
x_637 = 0;
x_638 = 1;
x_639 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_639, 0, x_17);
lean_ctor_set(x_639, 1, x_602);
lean_ctor_set_uint8(x_639, sizeof(void*)*2, x_636);
lean_ctor_set_uint8(x_639, sizeof(void*)*2 + 1, x_637);
lean_ctor_set_uint8(x_639, sizeof(void*)*2 + 2, x_637);
lean_ctor_set_uint8(x_639, sizeof(void*)*2 + 3, x_638);
x_640 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_603);
return x_640;
}
else
{
uint8_t x_641; uint8_t x_642; lean_object* x_643; lean_object* x_644; 
x_641 = 1;
x_642 = 0;
x_643 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_643, 0, x_17);
lean_ctor_set(x_643, 1, x_602);
lean_ctor_set_uint8(x_643, sizeof(void*)*2, x_641);
lean_ctor_set_uint8(x_643, sizeof(void*)*2 + 1, x_642);
lean_ctor_set_uint8(x_643, sizeof(void*)*2 + 2, x_642);
lean_ctor_set_uint8(x_643, sizeof(void*)*2 + 3, x_642);
x_644 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_603);
return x_644;
}
}
}
}
}
else
{
uint8_t x_645; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_645 = !lean_is_exclusive(x_566);
if (x_645 == 0)
{
return x_566;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_646 = lean_ctor_get(x_566, 0);
x_647 = lean_ctor_get(x_566, 1);
lean_inc(x_647);
lean_inc(x_646);
lean_dec(x_566);
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
return x_648;
}
}
}
}
}
else
{
lean_object* x_649; 
lean_dec(x_504);
lean_dec(x_503);
x_649 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_649) == 0)
{
uint8_t x_650; uint8_t x_651; uint8_t x_652; 
lean_dec(x_2);
x_650 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_651 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_652 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_650 == 0)
{
if (x_651 == 0)
{
if (x_652 == 0)
{
uint8_t x_653; uint8_t x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_653 = 2;
x_654 = 1;
x_655 = l_Array_empty___closed__1;
x_656 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_656, 0, x_17);
lean_ctor_set(x_656, 1, x_655);
lean_ctor_set_uint8(x_656, sizeof(void*)*2, x_653);
lean_ctor_set_uint8(x_656, sizeof(void*)*2 + 1, x_654);
lean_ctor_set_uint8(x_656, sizeof(void*)*2 + 2, x_654);
lean_ctor_set_uint8(x_656, sizeof(void*)*2 + 3, x_654);
x_657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_4);
return x_657;
}
else
{
uint8_t x_658; uint8_t x_659; uint8_t x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_658 = 2;
x_659 = 1;
x_660 = 0;
x_661 = l_Array_empty___closed__1;
x_662 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_662, 0, x_17);
lean_ctor_set(x_662, 1, x_661);
lean_ctor_set_uint8(x_662, sizeof(void*)*2, x_658);
lean_ctor_set_uint8(x_662, sizeof(void*)*2 + 1, x_659);
lean_ctor_set_uint8(x_662, sizeof(void*)*2 + 2, x_659);
lean_ctor_set_uint8(x_662, sizeof(void*)*2 + 3, x_660);
x_663 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_663, 0, x_662);
lean_ctor_set(x_663, 1, x_4);
return x_663;
}
}
else
{
if (x_652 == 0)
{
uint8_t x_664; uint8_t x_665; uint8_t x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_664 = 2;
x_665 = 1;
x_666 = 0;
x_667 = l_Array_empty___closed__1;
x_668 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_668, 0, x_17);
lean_ctor_set(x_668, 1, x_667);
lean_ctor_set_uint8(x_668, sizeof(void*)*2, x_664);
lean_ctor_set_uint8(x_668, sizeof(void*)*2 + 1, x_665);
lean_ctor_set_uint8(x_668, sizeof(void*)*2 + 2, x_666);
lean_ctor_set_uint8(x_668, sizeof(void*)*2 + 3, x_665);
x_669 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_4);
return x_669;
}
else
{
uint8_t x_670; uint8_t x_671; uint8_t x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_670 = 2;
x_671 = 1;
x_672 = 0;
x_673 = l_Array_empty___closed__1;
x_674 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_674, 0, x_17);
lean_ctor_set(x_674, 1, x_673);
lean_ctor_set_uint8(x_674, sizeof(void*)*2, x_670);
lean_ctor_set_uint8(x_674, sizeof(void*)*2 + 1, x_671);
lean_ctor_set_uint8(x_674, sizeof(void*)*2 + 2, x_672);
lean_ctor_set_uint8(x_674, sizeof(void*)*2 + 3, x_672);
x_675 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_675, 0, x_674);
lean_ctor_set(x_675, 1, x_4);
return x_675;
}
}
}
else
{
if (x_651 == 0)
{
if (x_652 == 0)
{
uint8_t x_676; uint8_t x_677; uint8_t x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_676 = 2;
x_677 = 0;
x_678 = 1;
x_679 = l_Array_empty___closed__1;
x_680 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_680, 0, x_17);
lean_ctor_set(x_680, 1, x_679);
lean_ctor_set_uint8(x_680, sizeof(void*)*2, x_676);
lean_ctor_set_uint8(x_680, sizeof(void*)*2 + 1, x_677);
lean_ctor_set_uint8(x_680, sizeof(void*)*2 + 2, x_678);
lean_ctor_set_uint8(x_680, sizeof(void*)*2 + 3, x_678);
x_681 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_681, 0, x_680);
lean_ctor_set(x_681, 1, x_4);
return x_681;
}
else
{
uint8_t x_682; uint8_t x_683; uint8_t x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_682 = 2;
x_683 = 0;
x_684 = 1;
x_685 = l_Array_empty___closed__1;
x_686 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_686, 0, x_17);
lean_ctor_set(x_686, 1, x_685);
lean_ctor_set_uint8(x_686, sizeof(void*)*2, x_682);
lean_ctor_set_uint8(x_686, sizeof(void*)*2 + 1, x_683);
lean_ctor_set_uint8(x_686, sizeof(void*)*2 + 2, x_684);
lean_ctor_set_uint8(x_686, sizeof(void*)*2 + 3, x_683);
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_4);
return x_687;
}
}
else
{
if (x_652 == 0)
{
uint8_t x_688; uint8_t x_689; uint8_t x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_688 = 2;
x_689 = 0;
x_690 = 1;
x_691 = l_Array_empty___closed__1;
x_692 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_692, 0, x_17);
lean_ctor_set(x_692, 1, x_691);
lean_ctor_set_uint8(x_692, sizeof(void*)*2, x_688);
lean_ctor_set_uint8(x_692, sizeof(void*)*2 + 1, x_689);
lean_ctor_set_uint8(x_692, sizeof(void*)*2 + 2, x_689);
lean_ctor_set_uint8(x_692, sizeof(void*)*2 + 3, x_690);
x_693 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_693, 0, x_692);
lean_ctor_set(x_693, 1, x_4);
return x_693;
}
else
{
uint8_t x_694; uint8_t x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_694 = 2;
x_695 = 0;
x_696 = l_Array_empty___closed__1;
x_697 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_697, 0, x_17);
lean_ctor_set(x_697, 1, x_696);
lean_ctor_set_uint8(x_697, sizeof(void*)*2, x_694);
lean_ctor_set_uint8(x_697, sizeof(void*)*2 + 1, x_695);
lean_ctor_set_uint8(x_697, sizeof(void*)*2 + 2, x_695);
lean_ctor_set_uint8(x_697, sizeof(void*)*2 + 3, x_695);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_697);
lean_ctor_set(x_698, 1, x_4);
return x_698;
}
}
}
}
else
{
lean_object* x_699; lean_object* x_700; 
x_699 = lean_ctor_get(x_649, 0);
lean_inc(x_699);
lean_dec(x_649);
x_700 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_699, x_2, x_3, x_4);
lean_dec(x_699);
if (lean_obj_tag(x_700) == 0)
{
uint8_t x_701; 
x_701 = !lean_is_exclusive(x_700);
if (x_701 == 0)
{
lean_object* x_702; uint8_t x_703; uint8_t x_704; uint8_t x_705; 
x_702 = lean_ctor_get(x_700, 0);
x_703 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_704 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_705 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_703 == 0)
{
if (x_704 == 0)
{
if (x_705 == 0)
{
uint8_t x_706; uint8_t x_707; lean_object* x_708; 
x_706 = 2;
x_707 = 1;
x_708 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_708, 0, x_17);
lean_ctor_set(x_708, 1, x_702);
lean_ctor_set_uint8(x_708, sizeof(void*)*2, x_706);
lean_ctor_set_uint8(x_708, sizeof(void*)*2 + 1, x_707);
lean_ctor_set_uint8(x_708, sizeof(void*)*2 + 2, x_707);
lean_ctor_set_uint8(x_708, sizeof(void*)*2 + 3, x_707);
lean_ctor_set(x_700, 0, x_708);
return x_700;
}
else
{
uint8_t x_709; uint8_t x_710; uint8_t x_711; lean_object* x_712; 
x_709 = 2;
x_710 = 1;
x_711 = 0;
x_712 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_712, 0, x_17);
lean_ctor_set(x_712, 1, x_702);
lean_ctor_set_uint8(x_712, sizeof(void*)*2, x_709);
lean_ctor_set_uint8(x_712, sizeof(void*)*2 + 1, x_710);
lean_ctor_set_uint8(x_712, sizeof(void*)*2 + 2, x_710);
lean_ctor_set_uint8(x_712, sizeof(void*)*2 + 3, x_711);
lean_ctor_set(x_700, 0, x_712);
return x_700;
}
}
else
{
if (x_705 == 0)
{
uint8_t x_713; uint8_t x_714; uint8_t x_715; lean_object* x_716; 
x_713 = 2;
x_714 = 1;
x_715 = 0;
x_716 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_716, 0, x_17);
lean_ctor_set(x_716, 1, x_702);
lean_ctor_set_uint8(x_716, sizeof(void*)*2, x_713);
lean_ctor_set_uint8(x_716, sizeof(void*)*2 + 1, x_714);
lean_ctor_set_uint8(x_716, sizeof(void*)*2 + 2, x_715);
lean_ctor_set_uint8(x_716, sizeof(void*)*2 + 3, x_714);
lean_ctor_set(x_700, 0, x_716);
return x_700;
}
else
{
uint8_t x_717; uint8_t x_718; uint8_t x_719; lean_object* x_720; 
x_717 = 2;
x_718 = 1;
x_719 = 0;
x_720 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_720, 0, x_17);
lean_ctor_set(x_720, 1, x_702);
lean_ctor_set_uint8(x_720, sizeof(void*)*2, x_717);
lean_ctor_set_uint8(x_720, sizeof(void*)*2 + 1, x_718);
lean_ctor_set_uint8(x_720, sizeof(void*)*2 + 2, x_719);
lean_ctor_set_uint8(x_720, sizeof(void*)*2 + 3, x_719);
lean_ctor_set(x_700, 0, x_720);
return x_700;
}
}
}
else
{
if (x_704 == 0)
{
if (x_705 == 0)
{
uint8_t x_721; uint8_t x_722; uint8_t x_723; lean_object* x_724; 
x_721 = 2;
x_722 = 0;
x_723 = 1;
x_724 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_724, 0, x_17);
lean_ctor_set(x_724, 1, x_702);
lean_ctor_set_uint8(x_724, sizeof(void*)*2, x_721);
lean_ctor_set_uint8(x_724, sizeof(void*)*2 + 1, x_722);
lean_ctor_set_uint8(x_724, sizeof(void*)*2 + 2, x_723);
lean_ctor_set_uint8(x_724, sizeof(void*)*2 + 3, x_723);
lean_ctor_set(x_700, 0, x_724);
return x_700;
}
else
{
uint8_t x_725; uint8_t x_726; uint8_t x_727; lean_object* x_728; 
x_725 = 2;
x_726 = 0;
x_727 = 1;
x_728 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_728, 0, x_17);
lean_ctor_set(x_728, 1, x_702);
lean_ctor_set_uint8(x_728, sizeof(void*)*2, x_725);
lean_ctor_set_uint8(x_728, sizeof(void*)*2 + 1, x_726);
lean_ctor_set_uint8(x_728, sizeof(void*)*2 + 2, x_727);
lean_ctor_set_uint8(x_728, sizeof(void*)*2 + 3, x_726);
lean_ctor_set(x_700, 0, x_728);
return x_700;
}
}
else
{
if (x_705 == 0)
{
uint8_t x_729; uint8_t x_730; uint8_t x_731; lean_object* x_732; 
x_729 = 2;
x_730 = 0;
x_731 = 1;
x_732 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_732, 0, x_17);
lean_ctor_set(x_732, 1, x_702);
lean_ctor_set_uint8(x_732, sizeof(void*)*2, x_729);
lean_ctor_set_uint8(x_732, sizeof(void*)*2 + 1, x_730);
lean_ctor_set_uint8(x_732, sizeof(void*)*2 + 2, x_730);
lean_ctor_set_uint8(x_732, sizeof(void*)*2 + 3, x_731);
lean_ctor_set(x_700, 0, x_732);
return x_700;
}
else
{
uint8_t x_733; uint8_t x_734; lean_object* x_735; 
x_733 = 2;
x_734 = 0;
x_735 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_735, 0, x_17);
lean_ctor_set(x_735, 1, x_702);
lean_ctor_set_uint8(x_735, sizeof(void*)*2, x_733);
lean_ctor_set_uint8(x_735, sizeof(void*)*2 + 1, x_734);
lean_ctor_set_uint8(x_735, sizeof(void*)*2 + 2, x_734);
lean_ctor_set_uint8(x_735, sizeof(void*)*2 + 3, x_734);
lean_ctor_set(x_700, 0, x_735);
return x_700;
}
}
}
}
else
{
lean_object* x_736; lean_object* x_737; uint8_t x_738; uint8_t x_739; uint8_t x_740; 
x_736 = lean_ctor_get(x_700, 0);
x_737 = lean_ctor_get(x_700, 1);
lean_inc(x_737);
lean_inc(x_736);
lean_dec(x_700);
x_738 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_739 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_740 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_738 == 0)
{
if (x_739 == 0)
{
if (x_740 == 0)
{
uint8_t x_741; uint8_t x_742; lean_object* x_743; lean_object* x_744; 
x_741 = 2;
x_742 = 1;
x_743 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_743, 0, x_17);
lean_ctor_set(x_743, 1, x_736);
lean_ctor_set_uint8(x_743, sizeof(void*)*2, x_741);
lean_ctor_set_uint8(x_743, sizeof(void*)*2 + 1, x_742);
lean_ctor_set_uint8(x_743, sizeof(void*)*2 + 2, x_742);
lean_ctor_set_uint8(x_743, sizeof(void*)*2 + 3, x_742);
x_744 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_744, 0, x_743);
lean_ctor_set(x_744, 1, x_737);
return x_744;
}
else
{
uint8_t x_745; uint8_t x_746; uint8_t x_747; lean_object* x_748; lean_object* x_749; 
x_745 = 2;
x_746 = 1;
x_747 = 0;
x_748 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_748, 0, x_17);
lean_ctor_set(x_748, 1, x_736);
lean_ctor_set_uint8(x_748, sizeof(void*)*2, x_745);
lean_ctor_set_uint8(x_748, sizeof(void*)*2 + 1, x_746);
lean_ctor_set_uint8(x_748, sizeof(void*)*2 + 2, x_746);
lean_ctor_set_uint8(x_748, sizeof(void*)*2 + 3, x_747);
x_749 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set(x_749, 1, x_737);
return x_749;
}
}
else
{
if (x_740 == 0)
{
uint8_t x_750; uint8_t x_751; uint8_t x_752; lean_object* x_753; lean_object* x_754; 
x_750 = 2;
x_751 = 1;
x_752 = 0;
x_753 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_753, 0, x_17);
lean_ctor_set(x_753, 1, x_736);
lean_ctor_set_uint8(x_753, sizeof(void*)*2, x_750);
lean_ctor_set_uint8(x_753, sizeof(void*)*2 + 1, x_751);
lean_ctor_set_uint8(x_753, sizeof(void*)*2 + 2, x_752);
lean_ctor_set_uint8(x_753, sizeof(void*)*2 + 3, x_751);
x_754 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set(x_754, 1, x_737);
return x_754;
}
else
{
uint8_t x_755; uint8_t x_756; uint8_t x_757; lean_object* x_758; lean_object* x_759; 
x_755 = 2;
x_756 = 1;
x_757 = 0;
x_758 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_758, 0, x_17);
lean_ctor_set(x_758, 1, x_736);
lean_ctor_set_uint8(x_758, sizeof(void*)*2, x_755);
lean_ctor_set_uint8(x_758, sizeof(void*)*2 + 1, x_756);
lean_ctor_set_uint8(x_758, sizeof(void*)*2 + 2, x_757);
lean_ctor_set_uint8(x_758, sizeof(void*)*2 + 3, x_757);
x_759 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_737);
return x_759;
}
}
}
else
{
if (x_739 == 0)
{
if (x_740 == 0)
{
uint8_t x_760; uint8_t x_761; uint8_t x_762; lean_object* x_763; lean_object* x_764; 
x_760 = 2;
x_761 = 0;
x_762 = 1;
x_763 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_763, 0, x_17);
lean_ctor_set(x_763, 1, x_736);
lean_ctor_set_uint8(x_763, sizeof(void*)*2, x_760);
lean_ctor_set_uint8(x_763, sizeof(void*)*2 + 1, x_761);
lean_ctor_set_uint8(x_763, sizeof(void*)*2 + 2, x_762);
lean_ctor_set_uint8(x_763, sizeof(void*)*2 + 3, x_762);
x_764 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_764, 0, x_763);
lean_ctor_set(x_764, 1, x_737);
return x_764;
}
else
{
uint8_t x_765; uint8_t x_766; uint8_t x_767; lean_object* x_768; lean_object* x_769; 
x_765 = 2;
x_766 = 0;
x_767 = 1;
x_768 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_768, 0, x_17);
lean_ctor_set(x_768, 1, x_736);
lean_ctor_set_uint8(x_768, sizeof(void*)*2, x_765);
lean_ctor_set_uint8(x_768, sizeof(void*)*2 + 1, x_766);
lean_ctor_set_uint8(x_768, sizeof(void*)*2 + 2, x_767);
lean_ctor_set_uint8(x_768, sizeof(void*)*2 + 3, x_766);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_737);
return x_769;
}
}
else
{
if (x_740 == 0)
{
uint8_t x_770; uint8_t x_771; uint8_t x_772; lean_object* x_773; lean_object* x_774; 
x_770 = 2;
x_771 = 0;
x_772 = 1;
x_773 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_773, 0, x_17);
lean_ctor_set(x_773, 1, x_736);
lean_ctor_set_uint8(x_773, sizeof(void*)*2, x_770);
lean_ctor_set_uint8(x_773, sizeof(void*)*2 + 1, x_771);
lean_ctor_set_uint8(x_773, sizeof(void*)*2 + 2, x_771);
lean_ctor_set_uint8(x_773, sizeof(void*)*2 + 3, x_772);
x_774 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_737);
return x_774;
}
else
{
uint8_t x_775; uint8_t x_776; lean_object* x_777; lean_object* x_778; 
x_775 = 2;
x_776 = 0;
x_777 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_777, 0, x_17);
lean_ctor_set(x_777, 1, x_736);
lean_ctor_set_uint8(x_777, sizeof(void*)*2, x_775);
lean_ctor_set_uint8(x_777, sizeof(void*)*2 + 1, x_776);
lean_ctor_set_uint8(x_777, sizeof(void*)*2 + 2, x_776);
lean_ctor_set_uint8(x_777, sizeof(void*)*2 + 3, x_776);
x_778 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_737);
return x_778;
}
}
}
}
}
else
{
uint8_t x_779; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_779 = !lean_is_exclusive(x_700);
if (x_779 == 0)
{
return x_700;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_780 = lean_ctor_get(x_700, 0);
x_781 = lean_ctor_get(x_700, 1);
lean_inc(x_781);
lean_inc(x_780);
lean_dec(x_700);
x_782 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_782, 0, x_780);
lean_ctor_set(x_782, 1, x_781);
return x_782;
}
}
}
}
}
}
else
{
lean_object* x_783; 
lean_dec(x_363);
lean_free_object(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_783 = lean_box(0);
x_346 = x_783;
goto block_362;
}
block_362:
{
lean_object* x_347; lean_object* x_348; uint8_t x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; 
lean_dec(x_346);
x_347 = l_Lean_Syntax_getArg(x_345, x_7);
x_348 = lean_box(0);
x_349 = 0;
x_350 = l_Lean_Syntax_formatStxAux___main(x_348, x_349, x_5, x_347);
x_351 = lean_box(0);
x_352 = l_Lean_Format_pretty(x_350, x_351);
x_353 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_353, 0, x_352);
x_354 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_354, 0, x_353);
x_355 = l_Lean_Elab_elabModifiers___rarg___closed__3;
x_356 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_354);
x_357 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(x_345, x_356, x_2, x_3, x_4);
lean_dec(x_345);
x_358 = !lean_is_exclusive(x_357);
if (x_358 == 0)
{
return x_357;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_357, 0);
x_360 = lean_ctor_get(x_357, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_357);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
}
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_802; 
x_784 = lean_ctor_get(x_17, 0);
lean_inc(x_784);
lean_dec(x_17);
x_802 = l_Lean_Syntax_getArg(x_784, x_7);
if (lean_obj_tag(x_802) == 2)
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
lean_dec(x_784);
x_803 = lean_ctor_get(x_802, 1);
lean_inc(x_803);
lean_dec(x_802);
x_804 = lean_string_utf8_byte_size(x_803);
x_805 = lean_nat_sub(x_804, x_9);
lean_dec(x_804);
x_806 = lean_string_utf8_extract(x_803, x_5, x_805);
lean_dec(x_805);
lean_dec(x_803);
x_807 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_807, 0, x_806);
x_808 = l_Lean_Syntax_getOptional_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; 
x_809 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_809) == 0)
{
uint8_t x_810; uint8_t x_811; uint8_t x_812; 
lean_dec(x_2);
x_810 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_811 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_812 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_810 == 0)
{
if (x_811 == 0)
{
if (x_812 == 0)
{
uint8_t x_813; uint8_t x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_813 = 0;
x_814 = 1;
x_815 = l_Array_empty___closed__1;
x_816 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_816, 0, x_807);
lean_ctor_set(x_816, 1, x_815);
lean_ctor_set_uint8(x_816, sizeof(void*)*2, x_813);
lean_ctor_set_uint8(x_816, sizeof(void*)*2 + 1, x_814);
lean_ctor_set_uint8(x_816, sizeof(void*)*2 + 2, x_814);
lean_ctor_set_uint8(x_816, sizeof(void*)*2 + 3, x_814);
x_817 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_4);
return x_817;
}
else
{
uint8_t x_818; uint8_t x_819; uint8_t x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_818 = 0;
x_819 = 1;
x_820 = 0;
x_821 = l_Array_empty___closed__1;
x_822 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_822, 0, x_807);
lean_ctor_set(x_822, 1, x_821);
lean_ctor_set_uint8(x_822, sizeof(void*)*2, x_818);
lean_ctor_set_uint8(x_822, sizeof(void*)*2 + 1, x_819);
lean_ctor_set_uint8(x_822, sizeof(void*)*2 + 2, x_819);
lean_ctor_set_uint8(x_822, sizeof(void*)*2 + 3, x_820);
x_823 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_4);
return x_823;
}
}
else
{
if (x_812 == 0)
{
uint8_t x_824; uint8_t x_825; uint8_t x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; 
x_824 = 0;
x_825 = 1;
x_826 = 0;
x_827 = l_Array_empty___closed__1;
x_828 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_828, 0, x_807);
lean_ctor_set(x_828, 1, x_827);
lean_ctor_set_uint8(x_828, sizeof(void*)*2, x_824);
lean_ctor_set_uint8(x_828, sizeof(void*)*2 + 1, x_825);
lean_ctor_set_uint8(x_828, sizeof(void*)*2 + 2, x_826);
lean_ctor_set_uint8(x_828, sizeof(void*)*2 + 3, x_825);
x_829 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_829, 0, x_828);
lean_ctor_set(x_829, 1, x_4);
return x_829;
}
else
{
uint8_t x_830; uint8_t x_831; uint8_t x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_830 = 0;
x_831 = 1;
x_832 = 0;
x_833 = l_Array_empty___closed__1;
x_834 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_834, 0, x_807);
lean_ctor_set(x_834, 1, x_833);
lean_ctor_set_uint8(x_834, sizeof(void*)*2, x_830);
lean_ctor_set_uint8(x_834, sizeof(void*)*2 + 1, x_831);
lean_ctor_set_uint8(x_834, sizeof(void*)*2 + 2, x_832);
lean_ctor_set_uint8(x_834, sizeof(void*)*2 + 3, x_832);
x_835 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_4);
return x_835;
}
}
}
else
{
if (x_811 == 0)
{
if (x_812 == 0)
{
uint8_t x_836; uint8_t x_837; uint8_t x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_836 = 0;
x_837 = 0;
x_838 = 1;
x_839 = l_Array_empty___closed__1;
x_840 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_840, 0, x_807);
lean_ctor_set(x_840, 1, x_839);
lean_ctor_set_uint8(x_840, sizeof(void*)*2, x_836);
lean_ctor_set_uint8(x_840, sizeof(void*)*2 + 1, x_837);
lean_ctor_set_uint8(x_840, sizeof(void*)*2 + 2, x_838);
lean_ctor_set_uint8(x_840, sizeof(void*)*2 + 3, x_838);
x_841 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_841, 0, x_840);
lean_ctor_set(x_841, 1, x_4);
return x_841;
}
else
{
uint8_t x_842; uint8_t x_843; uint8_t x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_842 = 0;
x_843 = 0;
x_844 = 1;
x_845 = l_Array_empty___closed__1;
x_846 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_846, 0, x_807);
lean_ctor_set(x_846, 1, x_845);
lean_ctor_set_uint8(x_846, sizeof(void*)*2, x_842);
lean_ctor_set_uint8(x_846, sizeof(void*)*2 + 1, x_843);
lean_ctor_set_uint8(x_846, sizeof(void*)*2 + 2, x_844);
lean_ctor_set_uint8(x_846, sizeof(void*)*2 + 3, x_843);
x_847 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_847, 0, x_846);
lean_ctor_set(x_847, 1, x_4);
return x_847;
}
}
else
{
if (x_812 == 0)
{
uint8_t x_848; uint8_t x_849; uint8_t x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_848 = 0;
x_849 = 0;
x_850 = 1;
x_851 = l_Array_empty___closed__1;
x_852 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_852, 0, x_807);
lean_ctor_set(x_852, 1, x_851);
lean_ctor_set_uint8(x_852, sizeof(void*)*2, x_848);
lean_ctor_set_uint8(x_852, sizeof(void*)*2 + 1, x_849);
lean_ctor_set_uint8(x_852, sizeof(void*)*2 + 2, x_849);
lean_ctor_set_uint8(x_852, sizeof(void*)*2 + 3, x_850);
x_853 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_853, 0, x_852);
lean_ctor_set(x_853, 1, x_4);
return x_853;
}
else
{
uint8_t x_854; uint8_t x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
x_854 = 0;
x_855 = 0;
x_856 = l_Array_empty___closed__1;
x_857 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_857, 0, x_807);
lean_ctor_set(x_857, 1, x_856);
lean_ctor_set_uint8(x_857, sizeof(void*)*2, x_854);
lean_ctor_set_uint8(x_857, sizeof(void*)*2 + 1, x_855);
lean_ctor_set_uint8(x_857, sizeof(void*)*2 + 2, x_855);
lean_ctor_set_uint8(x_857, sizeof(void*)*2 + 3, x_855);
x_858 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_858, 0, x_857);
lean_ctor_set(x_858, 1, x_4);
return x_858;
}
}
}
}
else
{
lean_object* x_859; lean_object* x_860; 
x_859 = lean_ctor_get(x_809, 0);
lean_inc(x_859);
lean_dec(x_809);
x_860 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_859, x_2, x_3, x_4);
lean_dec(x_859);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; uint8_t x_864; uint8_t x_865; uint8_t x_866; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_863 = x_860;
} else {
 lean_dec_ref(x_860);
 x_863 = lean_box(0);
}
x_864 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_865 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_866 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_864 == 0)
{
if (x_865 == 0)
{
if (x_866 == 0)
{
uint8_t x_867; uint8_t x_868; lean_object* x_869; lean_object* x_870; 
x_867 = 0;
x_868 = 1;
x_869 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_869, 0, x_807);
lean_ctor_set(x_869, 1, x_861);
lean_ctor_set_uint8(x_869, sizeof(void*)*2, x_867);
lean_ctor_set_uint8(x_869, sizeof(void*)*2 + 1, x_868);
lean_ctor_set_uint8(x_869, sizeof(void*)*2 + 2, x_868);
lean_ctor_set_uint8(x_869, sizeof(void*)*2 + 3, x_868);
if (lean_is_scalar(x_863)) {
 x_870 = lean_alloc_ctor(0, 2, 0);
} else {
 x_870 = x_863;
}
lean_ctor_set(x_870, 0, x_869);
lean_ctor_set(x_870, 1, x_862);
return x_870;
}
else
{
uint8_t x_871; uint8_t x_872; uint8_t x_873; lean_object* x_874; lean_object* x_875; 
x_871 = 0;
x_872 = 1;
x_873 = 0;
x_874 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_874, 0, x_807);
lean_ctor_set(x_874, 1, x_861);
lean_ctor_set_uint8(x_874, sizeof(void*)*2, x_871);
lean_ctor_set_uint8(x_874, sizeof(void*)*2 + 1, x_872);
lean_ctor_set_uint8(x_874, sizeof(void*)*2 + 2, x_872);
lean_ctor_set_uint8(x_874, sizeof(void*)*2 + 3, x_873);
if (lean_is_scalar(x_863)) {
 x_875 = lean_alloc_ctor(0, 2, 0);
} else {
 x_875 = x_863;
}
lean_ctor_set(x_875, 0, x_874);
lean_ctor_set(x_875, 1, x_862);
return x_875;
}
}
else
{
if (x_866 == 0)
{
uint8_t x_876; uint8_t x_877; uint8_t x_878; lean_object* x_879; lean_object* x_880; 
x_876 = 0;
x_877 = 1;
x_878 = 0;
x_879 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_879, 0, x_807);
lean_ctor_set(x_879, 1, x_861);
lean_ctor_set_uint8(x_879, sizeof(void*)*2, x_876);
lean_ctor_set_uint8(x_879, sizeof(void*)*2 + 1, x_877);
lean_ctor_set_uint8(x_879, sizeof(void*)*2 + 2, x_878);
lean_ctor_set_uint8(x_879, sizeof(void*)*2 + 3, x_877);
if (lean_is_scalar(x_863)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_863;
}
lean_ctor_set(x_880, 0, x_879);
lean_ctor_set(x_880, 1, x_862);
return x_880;
}
else
{
uint8_t x_881; uint8_t x_882; uint8_t x_883; lean_object* x_884; lean_object* x_885; 
x_881 = 0;
x_882 = 1;
x_883 = 0;
x_884 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_884, 0, x_807);
lean_ctor_set(x_884, 1, x_861);
lean_ctor_set_uint8(x_884, sizeof(void*)*2, x_881);
lean_ctor_set_uint8(x_884, sizeof(void*)*2 + 1, x_882);
lean_ctor_set_uint8(x_884, sizeof(void*)*2 + 2, x_883);
lean_ctor_set_uint8(x_884, sizeof(void*)*2 + 3, x_883);
if (lean_is_scalar(x_863)) {
 x_885 = lean_alloc_ctor(0, 2, 0);
} else {
 x_885 = x_863;
}
lean_ctor_set(x_885, 0, x_884);
lean_ctor_set(x_885, 1, x_862);
return x_885;
}
}
}
else
{
if (x_865 == 0)
{
if (x_866 == 0)
{
uint8_t x_886; uint8_t x_887; uint8_t x_888; lean_object* x_889; lean_object* x_890; 
x_886 = 0;
x_887 = 0;
x_888 = 1;
x_889 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_889, 0, x_807);
lean_ctor_set(x_889, 1, x_861);
lean_ctor_set_uint8(x_889, sizeof(void*)*2, x_886);
lean_ctor_set_uint8(x_889, sizeof(void*)*2 + 1, x_887);
lean_ctor_set_uint8(x_889, sizeof(void*)*2 + 2, x_888);
lean_ctor_set_uint8(x_889, sizeof(void*)*2 + 3, x_888);
if (lean_is_scalar(x_863)) {
 x_890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_890 = x_863;
}
lean_ctor_set(x_890, 0, x_889);
lean_ctor_set(x_890, 1, x_862);
return x_890;
}
else
{
uint8_t x_891; uint8_t x_892; uint8_t x_893; lean_object* x_894; lean_object* x_895; 
x_891 = 0;
x_892 = 0;
x_893 = 1;
x_894 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_894, 0, x_807);
lean_ctor_set(x_894, 1, x_861);
lean_ctor_set_uint8(x_894, sizeof(void*)*2, x_891);
lean_ctor_set_uint8(x_894, sizeof(void*)*2 + 1, x_892);
lean_ctor_set_uint8(x_894, sizeof(void*)*2 + 2, x_893);
lean_ctor_set_uint8(x_894, sizeof(void*)*2 + 3, x_892);
if (lean_is_scalar(x_863)) {
 x_895 = lean_alloc_ctor(0, 2, 0);
} else {
 x_895 = x_863;
}
lean_ctor_set(x_895, 0, x_894);
lean_ctor_set(x_895, 1, x_862);
return x_895;
}
}
else
{
if (x_866 == 0)
{
uint8_t x_896; uint8_t x_897; uint8_t x_898; lean_object* x_899; lean_object* x_900; 
x_896 = 0;
x_897 = 0;
x_898 = 1;
x_899 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_899, 0, x_807);
lean_ctor_set(x_899, 1, x_861);
lean_ctor_set_uint8(x_899, sizeof(void*)*2, x_896);
lean_ctor_set_uint8(x_899, sizeof(void*)*2 + 1, x_897);
lean_ctor_set_uint8(x_899, sizeof(void*)*2 + 2, x_897);
lean_ctor_set_uint8(x_899, sizeof(void*)*2 + 3, x_898);
if (lean_is_scalar(x_863)) {
 x_900 = lean_alloc_ctor(0, 2, 0);
} else {
 x_900 = x_863;
}
lean_ctor_set(x_900, 0, x_899);
lean_ctor_set(x_900, 1, x_862);
return x_900;
}
else
{
uint8_t x_901; uint8_t x_902; lean_object* x_903; lean_object* x_904; 
x_901 = 0;
x_902 = 0;
x_903 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_903, 0, x_807);
lean_ctor_set(x_903, 1, x_861);
lean_ctor_set_uint8(x_903, sizeof(void*)*2, x_901);
lean_ctor_set_uint8(x_903, sizeof(void*)*2 + 1, x_902);
lean_ctor_set_uint8(x_903, sizeof(void*)*2 + 2, x_902);
lean_ctor_set_uint8(x_903, sizeof(void*)*2 + 3, x_902);
if (lean_is_scalar(x_863)) {
 x_904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_904 = x_863;
}
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_862);
return x_904;
}
}
}
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; 
lean_dec(x_807);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_905 = lean_ctor_get(x_860, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_860, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_907 = x_860;
} else {
 lean_dec_ref(x_860);
 x_907 = lean_box(0);
}
if (lean_is_scalar(x_907)) {
 x_908 = lean_alloc_ctor(1, 2, 0);
} else {
 x_908 = x_907;
}
lean_ctor_set(x_908, 0, x_905);
lean_ctor_set(x_908, 1, x_906);
return x_908;
}
}
}
else
{
lean_object* x_909; lean_object* x_910; lean_object* x_911; uint8_t x_912; 
x_909 = lean_ctor_get(x_808, 0);
lean_inc(x_909);
lean_dec(x_808);
lean_inc(x_909);
x_910 = l_Lean_Syntax_getKind(x_909);
x_911 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__3;
x_912 = lean_name_eq(x_910, x_911);
if (x_912 == 0)
{
lean_object* x_913; uint8_t x_914; 
x_913 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__4;
x_914 = lean_name_eq(x_910, x_913);
lean_dec(x_910);
if (x_914 == 0)
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; 
lean_dec(x_807);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
x_915 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__7;
x_916 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(x_909, x_915, x_2, x_3, x_4);
lean_dec(x_909);
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_916, 1);
lean_inc(x_918);
if (lean_is_exclusive(x_916)) {
 lean_ctor_release(x_916, 0);
 lean_ctor_release(x_916, 1);
 x_919 = x_916;
} else {
 lean_dec_ref(x_916);
 x_919 = lean_box(0);
}
if (lean_is_scalar(x_919)) {
 x_920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_920 = x_919;
}
lean_ctor_set(x_920, 0, x_917);
lean_ctor_set(x_920, 1, x_918);
return x_920;
}
else
{
lean_object* x_921; 
lean_dec(x_909);
x_921 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_921) == 0)
{
uint8_t x_922; uint8_t x_923; uint8_t x_924; 
lean_dec(x_2);
x_922 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_923 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_924 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_922 == 0)
{
if (x_923 == 0)
{
if (x_924 == 0)
{
uint8_t x_925; uint8_t x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_925 = 1;
x_926 = 1;
x_927 = l_Array_empty___closed__1;
x_928 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_928, 0, x_807);
lean_ctor_set(x_928, 1, x_927);
lean_ctor_set_uint8(x_928, sizeof(void*)*2, x_925);
lean_ctor_set_uint8(x_928, sizeof(void*)*2 + 1, x_926);
lean_ctor_set_uint8(x_928, sizeof(void*)*2 + 2, x_926);
lean_ctor_set_uint8(x_928, sizeof(void*)*2 + 3, x_926);
x_929 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_929, 0, x_928);
lean_ctor_set(x_929, 1, x_4);
return x_929;
}
else
{
uint8_t x_930; uint8_t x_931; uint8_t x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_930 = 1;
x_931 = 1;
x_932 = 0;
x_933 = l_Array_empty___closed__1;
x_934 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_934, 0, x_807);
lean_ctor_set(x_934, 1, x_933);
lean_ctor_set_uint8(x_934, sizeof(void*)*2, x_930);
lean_ctor_set_uint8(x_934, sizeof(void*)*2 + 1, x_931);
lean_ctor_set_uint8(x_934, sizeof(void*)*2 + 2, x_931);
lean_ctor_set_uint8(x_934, sizeof(void*)*2 + 3, x_932);
x_935 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_935, 0, x_934);
lean_ctor_set(x_935, 1, x_4);
return x_935;
}
}
else
{
if (x_924 == 0)
{
uint8_t x_936; uint8_t x_937; uint8_t x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_936 = 1;
x_937 = 1;
x_938 = 0;
x_939 = l_Array_empty___closed__1;
x_940 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_940, 0, x_807);
lean_ctor_set(x_940, 1, x_939);
lean_ctor_set_uint8(x_940, sizeof(void*)*2, x_936);
lean_ctor_set_uint8(x_940, sizeof(void*)*2 + 1, x_937);
lean_ctor_set_uint8(x_940, sizeof(void*)*2 + 2, x_938);
lean_ctor_set_uint8(x_940, sizeof(void*)*2 + 3, x_937);
x_941 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_941, 0, x_940);
lean_ctor_set(x_941, 1, x_4);
return x_941;
}
else
{
uint8_t x_942; uint8_t x_943; uint8_t x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_942 = 1;
x_943 = 1;
x_944 = 0;
x_945 = l_Array_empty___closed__1;
x_946 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_946, 0, x_807);
lean_ctor_set(x_946, 1, x_945);
lean_ctor_set_uint8(x_946, sizeof(void*)*2, x_942);
lean_ctor_set_uint8(x_946, sizeof(void*)*2 + 1, x_943);
lean_ctor_set_uint8(x_946, sizeof(void*)*2 + 2, x_944);
lean_ctor_set_uint8(x_946, sizeof(void*)*2 + 3, x_944);
x_947 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_947, 0, x_946);
lean_ctor_set(x_947, 1, x_4);
return x_947;
}
}
}
else
{
if (x_923 == 0)
{
if (x_924 == 0)
{
uint8_t x_948; uint8_t x_949; uint8_t x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_948 = 1;
x_949 = 0;
x_950 = 1;
x_951 = l_Array_empty___closed__1;
x_952 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_952, 0, x_807);
lean_ctor_set(x_952, 1, x_951);
lean_ctor_set_uint8(x_952, sizeof(void*)*2, x_948);
lean_ctor_set_uint8(x_952, sizeof(void*)*2 + 1, x_949);
lean_ctor_set_uint8(x_952, sizeof(void*)*2 + 2, x_950);
lean_ctor_set_uint8(x_952, sizeof(void*)*2 + 3, x_950);
x_953 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_953, 0, x_952);
lean_ctor_set(x_953, 1, x_4);
return x_953;
}
else
{
uint8_t x_954; uint8_t x_955; uint8_t x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; 
x_954 = 1;
x_955 = 0;
x_956 = 1;
x_957 = l_Array_empty___closed__1;
x_958 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_958, 0, x_807);
lean_ctor_set(x_958, 1, x_957);
lean_ctor_set_uint8(x_958, sizeof(void*)*2, x_954);
lean_ctor_set_uint8(x_958, sizeof(void*)*2 + 1, x_955);
lean_ctor_set_uint8(x_958, sizeof(void*)*2 + 2, x_956);
lean_ctor_set_uint8(x_958, sizeof(void*)*2 + 3, x_955);
x_959 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_959, 0, x_958);
lean_ctor_set(x_959, 1, x_4);
return x_959;
}
}
else
{
if (x_924 == 0)
{
uint8_t x_960; uint8_t x_961; uint8_t x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
x_960 = 1;
x_961 = 0;
x_962 = 1;
x_963 = l_Array_empty___closed__1;
x_964 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_964, 0, x_807);
lean_ctor_set(x_964, 1, x_963);
lean_ctor_set_uint8(x_964, sizeof(void*)*2, x_960);
lean_ctor_set_uint8(x_964, sizeof(void*)*2 + 1, x_961);
lean_ctor_set_uint8(x_964, sizeof(void*)*2 + 2, x_961);
lean_ctor_set_uint8(x_964, sizeof(void*)*2 + 3, x_962);
x_965 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_965, 0, x_964);
lean_ctor_set(x_965, 1, x_4);
return x_965;
}
else
{
uint8_t x_966; uint8_t x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
x_966 = 1;
x_967 = 0;
x_968 = l_Array_empty___closed__1;
x_969 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_969, 0, x_807);
lean_ctor_set(x_969, 1, x_968);
lean_ctor_set_uint8(x_969, sizeof(void*)*2, x_966);
lean_ctor_set_uint8(x_969, sizeof(void*)*2 + 1, x_967);
lean_ctor_set_uint8(x_969, sizeof(void*)*2 + 2, x_967);
lean_ctor_set_uint8(x_969, sizeof(void*)*2 + 3, x_967);
x_970 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_970, 0, x_969);
lean_ctor_set(x_970, 1, x_4);
return x_970;
}
}
}
}
else
{
lean_object* x_971; lean_object* x_972; 
x_971 = lean_ctor_get(x_921, 0);
lean_inc(x_971);
lean_dec(x_921);
x_972 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_971, x_2, x_3, x_4);
lean_dec(x_971);
if (lean_obj_tag(x_972) == 0)
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; uint8_t x_976; uint8_t x_977; uint8_t x_978; 
x_973 = lean_ctor_get(x_972, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_972, 1);
lean_inc(x_974);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 lean_ctor_release(x_972, 1);
 x_975 = x_972;
} else {
 lean_dec_ref(x_972);
 x_975 = lean_box(0);
}
x_976 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_977 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_978 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_976 == 0)
{
if (x_977 == 0)
{
if (x_978 == 0)
{
uint8_t x_979; uint8_t x_980; lean_object* x_981; lean_object* x_982; 
x_979 = 1;
x_980 = 1;
x_981 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_981, 0, x_807);
lean_ctor_set(x_981, 1, x_973);
lean_ctor_set_uint8(x_981, sizeof(void*)*2, x_979);
lean_ctor_set_uint8(x_981, sizeof(void*)*2 + 1, x_980);
lean_ctor_set_uint8(x_981, sizeof(void*)*2 + 2, x_980);
lean_ctor_set_uint8(x_981, sizeof(void*)*2 + 3, x_980);
if (lean_is_scalar(x_975)) {
 x_982 = lean_alloc_ctor(0, 2, 0);
} else {
 x_982 = x_975;
}
lean_ctor_set(x_982, 0, x_981);
lean_ctor_set(x_982, 1, x_974);
return x_982;
}
else
{
uint8_t x_983; uint8_t x_984; uint8_t x_985; lean_object* x_986; lean_object* x_987; 
x_983 = 1;
x_984 = 1;
x_985 = 0;
x_986 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_986, 0, x_807);
lean_ctor_set(x_986, 1, x_973);
lean_ctor_set_uint8(x_986, sizeof(void*)*2, x_983);
lean_ctor_set_uint8(x_986, sizeof(void*)*2 + 1, x_984);
lean_ctor_set_uint8(x_986, sizeof(void*)*2 + 2, x_984);
lean_ctor_set_uint8(x_986, sizeof(void*)*2 + 3, x_985);
if (lean_is_scalar(x_975)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_975;
}
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set(x_987, 1, x_974);
return x_987;
}
}
else
{
if (x_978 == 0)
{
uint8_t x_988; uint8_t x_989; uint8_t x_990; lean_object* x_991; lean_object* x_992; 
x_988 = 1;
x_989 = 1;
x_990 = 0;
x_991 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_991, 0, x_807);
lean_ctor_set(x_991, 1, x_973);
lean_ctor_set_uint8(x_991, sizeof(void*)*2, x_988);
lean_ctor_set_uint8(x_991, sizeof(void*)*2 + 1, x_989);
lean_ctor_set_uint8(x_991, sizeof(void*)*2 + 2, x_990);
lean_ctor_set_uint8(x_991, sizeof(void*)*2 + 3, x_989);
if (lean_is_scalar(x_975)) {
 x_992 = lean_alloc_ctor(0, 2, 0);
} else {
 x_992 = x_975;
}
lean_ctor_set(x_992, 0, x_991);
lean_ctor_set(x_992, 1, x_974);
return x_992;
}
else
{
uint8_t x_993; uint8_t x_994; uint8_t x_995; lean_object* x_996; lean_object* x_997; 
x_993 = 1;
x_994 = 1;
x_995 = 0;
x_996 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_996, 0, x_807);
lean_ctor_set(x_996, 1, x_973);
lean_ctor_set_uint8(x_996, sizeof(void*)*2, x_993);
lean_ctor_set_uint8(x_996, sizeof(void*)*2 + 1, x_994);
lean_ctor_set_uint8(x_996, sizeof(void*)*2 + 2, x_995);
lean_ctor_set_uint8(x_996, sizeof(void*)*2 + 3, x_995);
if (lean_is_scalar(x_975)) {
 x_997 = lean_alloc_ctor(0, 2, 0);
} else {
 x_997 = x_975;
}
lean_ctor_set(x_997, 0, x_996);
lean_ctor_set(x_997, 1, x_974);
return x_997;
}
}
}
else
{
if (x_977 == 0)
{
if (x_978 == 0)
{
uint8_t x_998; uint8_t x_999; uint8_t x_1000; lean_object* x_1001; lean_object* x_1002; 
x_998 = 1;
x_999 = 0;
x_1000 = 1;
x_1001 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1001, 0, x_807);
lean_ctor_set(x_1001, 1, x_973);
lean_ctor_set_uint8(x_1001, sizeof(void*)*2, x_998);
lean_ctor_set_uint8(x_1001, sizeof(void*)*2 + 1, x_999);
lean_ctor_set_uint8(x_1001, sizeof(void*)*2 + 2, x_1000);
lean_ctor_set_uint8(x_1001, sizeof(void*)*2 + 3, x_1000);
if (lean_is_scalar(x_975)) {
 x_1002 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1002 = x_975;
}
lean_ctor_set(x_1002, 0, x_1001);
lean_ctor_set(x_1002, 1, x_974);
return x_1002;
}
else
{
uint8_t x_1003; uint8_t x_1004; uint8_t x_1005; lean_object* x_1006; lean_object* x_1007; 
x_1003 = 1;
x_1004 = 0;
x_1005 = 1;
x_1006 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1006, 0, x_807);
lean_ctor_set(x_1006, 1, x_973);
lean_ctor_set_uint8(x_1006, sizeof(void*)*2, x_1003);
lean_ctor_set_uint8(x_1006, sizeof(void*)*2 + 1, x_1004);
lean_ctor_set_uint8(x_1006, sizeof(void*)*2 + 2, x_1005);
lean_ctor_set_uint8(x_1006, sizeof(void*)*2 + 3, x_1004);
if (lean_is_scalar(x_975)) {
 x_1007 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1007 = x_975;
}
lean_ctor_set(x_1007, 0, x_1006);
lean_ctor_set(x_1007, 1, x_974);
return x_1007;
}
}
else
{
if (x_978 == 0)
{
uint8_t x_1008; uint8_t x_1009; uint8_t x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1008 = 1;
x_1009 = 0;
x_1010 = 1;
x_1011 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1011, 0, x_807);
lean_ctor_set(x_1011, 1, x_973);
lean_ctor_set_uint8(x_1011, sizeof(void*)*2, x_1008);
lean_ctor_set_uint8(x_1011, sizeof(void*)*2 + 1, x_1009);
lean_ctor_set_uint8(x_1011, sizeof(void*)*2 + 2, x_1009);
lean_ctor_set_uint8(x_1011, sizeof(void*)*2 + 3, x_1010);
if (lean_is_scalar(x_975)) {
 x_1012 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1012 = x_975;
}
lean_ctor_set(x_1012, 0, x_1011);
lean_ctor_set(x_1012, 1, x_974);
return x_1012;
}
else
{
uint8_t x_1013; uint8_t x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1013 = 1;
x_1014 = 0;
x_1015 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1015, 0, x_807);
lean_ctor_set(x_1015, 1, x_973);
lean_ctor_set_uint8(x_1015, sizeof(void*)*2, x_1013);
lean_ctor_set_uint8(x_1015, sizeof(void*)*2 + 1, x_1014);
lean_ctor_set_uint8(x_1015, sizeof(void*)*2 + 2, x_1014);
lean_ctor_set_uint8(x_1015, sizeof(void*)*2 + 3, x_1014);
if (lean_is_scalar(x_975)) {
 x_1016 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1016 = x_975;
}
lean_ctor_set(x_1016, 0, x_1015);
lean_ctor_set(x_1016, 1, x_974);
return x_1016;
}
}
}
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
lean_dec(x_807);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_1017 = lean_ctor_get(x_972, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_972, 1);
lean_inc(x_1018);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 lean_ctor_release(x_972, 1);
 x_1019 = x_972;
} else {
 lean_dec_ref(x_972);
 x_1019 = lean_box(0);
}
if (lean_is_scalar(x_1019)) {
 x_1020 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1020 = x_1019;
}
lean_ctor_set(x_1020, 0, x_1017);
lean_ctor_set(x_1020, 1, x_1018);
return x_1020;
}
}
}
}
else
{
lean_object* x_1021; 
lean_dec(x_910);
lean_dec(x_909);
x_1021 = l_Lean_Syntax_getOptional_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_1021) == 0)
{
uint8_t x_1022; uint8_t x_1023; uint8_t x_1024; 
lean_dec(x_2);
x_1022 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_1023 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_1024 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_1022 == 0)
{
if (x_1023 == 0)
{
if (x_1024 == 0)
{
uint8_t x_1025; uint8_t x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1025 = 2;
x_1026 = 1;
x_1027 = l_Array_empty___closed__1;
x_1028 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1028, 0, x_807);
lean_ctor_set(x_1028, 1, x_1027);
lean_ctor_set_uint8(x_1028, sizeof(void*)*2, x_1025);
lean_ctor_set_uint8(x_1028, sizeof(void*)*2 + 1, x_1026);
lean_ctor_set_uint8(x_1028, sizeof(void*)*2 + 2, x_1026);
lean_ctor_set_uint8(x_1028, sizeof(void*)*2 + 3, x_1026);
x_1029 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1029, 0, x_1028);
lean_ctor_set(x_1029, 1, x_4);
return x_1029;
}
else
{
uint8_t x_1030; uint8_t x_1031; uint8_t x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; 
x_1030 = 2;
x_1031 = 1;
x_1032 = 0;
x_1033 = l_Array_empty___closed__1;
x_1034 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1034, 0, x_807);
lean_ctor_set(x_1034, 1, x_1033);
lean_ctor_set_uint8(x_1034, sizeof(void*)*2, x_1030);
lean_ctor_set_uint8(x_1034, sizeof(void*)*2 + 1, x_1031);
lean_ctor_set_uint8(x_1034, sizeof(void*)*2 + 2, x_1031);
lean_ctor_set_uint8(x_1034, sizeof(void*)*2 + 3, x_1032);
x_1035 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1035, 0, x_1034);
lean_ctor_set(x_1035, 1, x_4);
return x_1035;
}
}
else
{
if (x_1024 == 0)
{
uint8_t x_1036; uint8_t x_1037; uint8_t x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1036 = 2;
x_1037 = 1;
x_1038 = 0;
x_1039 = l_Array_empty___closed__1;
x_1040 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1040, 0, x_807);
lean_ctor_set(x_1040, 1, x_1039);
lean_ctor_set_uint8(x_1040, sizeof(void*)*2, x_1036);
lean_ctor_set_uint8(x_1040, sizeof(void*)*2 + 1, x_1037);
lean_ctor_set_uint8(x_1040, sizeof(void*)*2 + 2, x_1038);
lean_ctor_set_uint8(x_1040, sizeof(void*)*2 + 3, x_1037);
x_1041 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1041, 0, x_1040);
lean_ctor_set(x_1041, 1, x_4);
return x_1041;
}
else
{
uint8_t x_1042; uint8_t x_1043; uint8_t x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1042 = 2;
x_1043 = 1;
x_1044 = 0;
x_1045 = l_Array_empty___closed__1;
x_1046 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1046, 0, x_807);
lean_ctor_set(x_1046, 1, x_1045);
lean_ctor_set_uint8(x_1046, sizeof(void*)*2, x_1042);
lean_ctor_set_uint8(x_1046, sizeof(void*)*2 + 1, x_1043);
lean_ctor_set_uint8(x_1046, sizeof(void*)*2 + 2, x_1044);
lean_ctor_set_uint8(x_1046, sizeof(void*)*2 + 3, x_1044);
x_1047 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_4);
return x_1047;
}
}
}
else
{
if (x_1023 == 0)
{
if (x_1024 == 0)
{
uint8_t x_1048; uint8_t x_1049; uint8_t x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; 
x_1048 = 2;
x_1049 = 0;
x_1050 = 1;
x_1051 = l_Array_empty___closed__1;
x_1052 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1052, 0, x_807);
lean_ctor_set(x_1052, 1, x_1051);
lean_ctor_set_uint8(x_1052, sizeof(void*)*2, x_1048);
lean_ctor_set_uint8(x_1052, sizeof(void*)*2 + 1, x_1049);
lean_ctor_set_uint8(x_1052, sizeof(void*)*2 + 2, x_1050);
lean_ctor_set_uint8(x_1052, sizeof(void*)*2 + 3, x_1050);
x_1053 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_4);
return x_1053;
}
else
{
uint8_t x_1054; uint8_t x_1055; uint8_t x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1054 = 2;
x_1055 = 0;
x_1056 = 1;
x_1057 = l_Array_empty___closed__1;
x_1058 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1058, 0, x_807);
lean_ctor_set(x_1058, 1, x_1057);
lean_ctor_set_uint8(x_1058, sizeof(void*)*2, x_1054);
lean_ctor_set_uint8(x_1058, sizeof(void*)*2 + 1, x_1055);
lean_ctor_set_uint8(x_1058, sizeof(void*)*2 + 2, x_1056);
lean_ctor_set_uint8(x_1058, sizeof(void*)*2 + 3, x_1055);
x_1059 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1059, 0, x_1058);
lean_ctor_set(x_1059, 1, x_4);
return x_1059;
}
}
else
{
if (x_1024 == 0)
{
uint8_t x_1060; uint8_t x_1061; uint8_t x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1060 = 2;
x_1061 = 0;
x_1062 = 1;
x_1063 = l_Array_empty___closed__1;
x_1064 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1064, 0, x_807);
lean_ctor_set(x_1064, 1, x_1063);
lean_ctor_set_uint8(x_1064, sizeof(void*)*2, x_1060);
lean_ctor_set_uint8(x_1064, sizeof(void*)*2 + 1, x_1061);
lean_ctor_set_uint8(x_1064, sizeof(void*)*2 + 2, x_1061);
lean_ctor_set_uint8(x_1064, sizeof(void*)*2 + 3, x_1062);
x_1065 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1065, 0, x_1064);
lean_ctor_set(x_1065, 1, x_4);
return x_1065;
}
else
{
uint8_t x_1066; uint8_t x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
x_1066 = 2;
x_1067 = 0;
x_1068 = l_Array_empty___closed__1;
x_1069 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1069, 0, x_807);
lean_ctor_set(x_1069, 1, x_1068);
lean_ctor_set_uint8(x_1069, sizeof(void*)*2, x_1066);
lean_ctor_set_uint8(x_1069, sizeof(void*)*2 + 1, x_1067);
lean_ctor_set_uint8(x_1069, sizeof(void*)*2 + 2, x_1067);
lean_ctor_set_uint8(x_1069, sizeof(void*)*2 + 3, x_1067);
x_1070 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1070, 0, x_1069);
lean_ctor_set(x_1070, 1, x_4);
return x_1070;
}
}
}
}
else
{
lean_object* x_1071; lean_object* x_1072; 
x_1071 = lean_ctor_get(x_1021, 0);
lean_inc(x_1071);
lean_dec(x_1021);
x_1072 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_1071, x_2, x_3, x_4);
lean_dec(x_1071);
if (lean_obj_tag(x_1072) == 0)
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; uint8_t x_1076; uint8_t x_1077; uint8_t x_1078; 
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1072, 1);
lean_inc(x_1074);
if (lean_is_exclusive(x_1072)) {
 lean_ctor_release(x_1072, 0);
 lean_ctor_release(x_1072, 1);
 x_1075 = x_1072;
} else {
 lean_dec_ref(x_1072);
 x_1075 = lean_box(0);
}
x_1076 = l_Lean_Syntax_isNone(x_12);
lean_dec(x_12);
x_1077 = l_Lean_Syntax_isNone(x_16);
lean_dec(x_16);
x_1078 = l_Lean_Syntax_isNone(x_14);
lean_dec(x_14);
if (x_1076 == 0)
{
if (x_1077 == 0)
{
if (x_1078 == 0)
{
uint8_t x_1079; uint8_t x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1079 = 2;
x_1080 = 1;
x_1081 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1081, 0, x_807);
lean_ctor_set(x_1081, 1, x_1073);
lean_ctor_set_uint8(x_1081, sizeof(void*)*2, x_1079);
lean_ctor_set_uint8(x_1081, sizeof(void*)*2 + 1, x_1080);
lean_ctor_set_uint8(x_1081, sizeof(void*)*2 + 2, x_1080);
lean_ctor_set_uint8(x_1081, sizeof(void*)*2 + 3, x_1080);
if (lean_is_scalar(x_1075)) {
 x_1082 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1082 = x_1075;
}
lean_ctor_set(x_1082, 0, x_1081);
lean_ctor_set(x_1082, 1, x_1074);
return x_1082;
}
else
{
uint8_t x_1083; uint8_t x_1084; uint8_t x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1083 = 2;
x_1084 = 1;
x_1085 = 0;
x_1086 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1086, 0, x_807);
lean_ctor_set(x_1086, 1, x_1073);
lean_ctor_set_uint8(x_1086, sizeof(void*)*2, x_1083);
lean_ctor_set_uint8(x_1086, sizeof(void*)*2 + 1, x_1084);
lean_ctor_set_uint8(x_1086, sizeof(void*)*2 + 2, x_1084);
lean_ctor_set_uint8(x_1086, sizeof(void*)*2 + 3, x_1085);
if (lean_is_scalar(x_1075)) {
 x_1087 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1087 = x_1075;
}
lean_ctor_set(x_1087, 0, x_1086);
lean_ctor_set(x_1087, 1, x_1074);
return x_1087;
}
}
else
{
if (x_1078 == 0)
{
uint8_t x_1088; uint8_t x_1089; uint8_t x_1090; lean_object* x_1091; lean_object* x_1092; 
x_1088 = 2;
x_1089 = 1;
x_1090 = 0;
x_1091 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1091, 0, x_807);
lean_ctor_set(x_1091, 1, x_1073);
lean_ctor_set_uint8(x_1091, sizeof(void*)*2, x_1088);
lean_ctor_set_uint8(x_1091, sizeof(void*)*2 + 1, x_1089);
lean_ctor_set_uint8(x_1091, sizeof(void*)*2 + 2, x_1090);
lean_ctor_set_uint8(x_1091, sizeof(void*)*2 + 3, x_1089);
if (lean_is_scalar(x_1075)) {
 x_1092 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1092 = x_1075;
}
lean_ctor_set(x_1092, 0, x_1091);
lean_ctor_set(x_1092, 1, x_1074);
return x_1092;
}
else
{
uint8_t x_1093; uint8_t x_1094; uint8_t x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1093 = 2;
x_1094 = 1;
x_1095 = 0;
x_1096 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1096, 0, x_807);
lean_ctor_set(x_1096, 1, x_1073);
lean_ctor_set_uint8(x_1096, sizeof(void*)*2, x_1093);
lean_ctor_set_uint8(x_1096, sizeof(void*)*2 + 1, x_1094);
lean_ctor_set_uint8(x_1096, sizeof(void*)*2 + 2, x_1095);
lean_ctor_set_uint8(x_1096, sizeof(void*)*2 + 3, x_1095);
if (lean_is_scalar(x_1075)) {
 x_1097 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1097 = x_1075;
}
lean_ctor_set(x_1097, 0, x_1096);
lean_ctor_set(x_1097, 1, x_1074);
return x_1097;
}
}
}
else
{
if (x_1077 == 0)
{
if (x_1078 == 0)
{
uint8_t x_1098; uint8_t x_1099; uint8_t x_1100; lean_object* x_1101; lean_object* x_1102; 
x_1098 = 2;
x_1099 = 0;
x_1100 = 1;
x_1101 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1101, 0, x_807);
lean_ctor_set(x_1101, 1, x_1073);
lean_ctor_set_uint8(x_1101, sizeof(void*)*2, x_1098);
lean_ctor_set_uint8(x_1101, sizeof(void*)*2 + 1, x_1099);
lean_ctor_set_uint8(x_1101, sizeof(void*)*2 + 2, x_1100);
lean_ctor_set_uint8(x_1101, sizeof(void*)*2 + 3, x_1100);
if (lean_is_scalar(x_1075)) {
 x_1102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1102 = x_1075;
}
lean_ctor_set(x_1102, 0, x_1101);
lean_ctor_set(x_1102, 1, x_1074);
return x_1102;
}
else
{
uint8_t x_1103; uint8_t x_1104; uint8_t x_1105; lean_object* x_1106; lean_object* x_1107; 
x_1103 = 2;
x_1104 = 0;
x_1105 = 1;
x_1106 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1106, 0, x_807);
lean_ctor_set(x_1106, 1, x_1073);
lean_ctor_set_uint8(x_1106, sizeof(void*)*2, x_1103);
lean_ctor_set_uint8(x_1106, sizeof(void*)*2 + 1, x_1104);
lean_ctor_set_uint8(x_1106, sizeof(void*)*2 + 2, x_1105);
lean_ctor_set_uint8(x_1106, sizeof(void*)*2 + 3, x_1104);
if (lean_is_scalar(x_1075)) {
 x_1107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1107 = x_1075;
}
lean_ctor_set(x_1107, 0, x_1106);
lean_ctor_set(x_1107, 1, x_1074);
return x_1107;
}
}
else
{
if (x_1078 == 0)
{
uint8_t x_1108; uint8_t x_1109; uint8_t x_1110; lean_object* x_1111; lean_object* x_1112; 
x_1108 = 2;
x_1109 = 0;
x_1110 = 1;
x_1111 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1111, 0, x_807);
lean_ctor_set(x_1111, 1, x_1073);
lean_ctor_set_uint8(x_1111, sizeof(void*)*2, x_1108);
lean_ctor_set_uint8(x_1111, sizeof(void*)*2 + 1, x_1109);
lean_ctor_set_uint8(x_1111, sizeof(void*)*2 + 2, x_1109);
lean_ctor_set_uint8(x_1111, sizeof(void*)*2 + 3, x_1110);
if (lean_is_scalar(x_1075)) {
 x_1112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1112 = x_1075;
}
lean_ctor_set(x_1112, 0, x_1111);
lean_ctor_set(x_1112, 1, x_1074);
return x_1112;
}
else
{
uint8_t x_1113; uint8_t x_1114; lean_object* x_1115; lean_object* x_1116; 
x_1113 = 2;
x_1114 = 0;
x_1115 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_1115, 0, x_807);
lean_ctor_set(x_1115, 1, x_1073);
lean_ctor_set_uint8(x_1115, sizeof(void*)*2, x_1113);
lean_ctor_set_uint8(x_1115, sizeof(void*)*2 + 1, x_1114);
lean_ctor_set_uint8(x_1115, sizeof(void*)*2 + 2, x_1114);
lean_ctor_set_uint8(x_1115, sizeof(void*)*2 + 3, x_1114);
if (lean_is_scalar(x_1075)) {
 x_1116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1116 = x_1075;
}
lean_ctor_set(x_1116, 0, x_1115);
lean_ctor_set(x_1116, 1, x_1074);
return x_1116;
}
}
}
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
lean_dec(x_807);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
x_1117 = lean_ctor_get(x_1072, 0);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_1072, 1);
lean_inc(x_1118);
if (lean_is_exclusive(x_1072)) {
 lean_ctor_release(x_1072, 0);
 lean_ctor_release(x_1072, 1);
 x_1119 = x_1072;
} else {
 lean_dec_ref(x_1072);
 x_1119 = lean_box(0);
}
if (lean_is_scalar(x_1119)) {
 x_1120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1120 = x_1119;
}
lean_ctor_set(x_1120, 0, x_1117);
lean_ctor_set(x_1120, 1, x_1118);
return x_1120;
}
}
}
}
}
else
{
lean_object* x_1121; 
lean_dec(x_802);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
x_1121 = lean_box(0);
x_785 = x_1121;
goto block_801;
}
block_801:
{
lean_object* x_786; lean_object* x_787; uint8_t x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; 
lean_dec(x_785);
x_786 = l_Lean_Syntax_getArg(x_784, x_7);
x_787 = lean_box(0);
x_788 = 0;
x_789 = l_Lean_Syntax_formatStxAux___main(x_787, x_788, x_5, x_786);
x_790 = lean_box(0);
x_791 = l_Lean_Format_pretty(x_789, x_790);
x_792 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_792, 0, x_791);
x_793 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_793, 0, x_792);
x_794 = l_Lean_Elab_elabModifiers___rarg___closed__3;
x_795 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_793);
x_796 = l_Lean_throwErrorAt___at_Lean_Elab_Command_elabCommand___main___spec__7___rarg(x_784, x_795, x_2, x_3, x_4);
lean_dec(x_784);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
x_798 = lean_ctor_get(x_796, 1);
lean_inc(x_798);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 x_799 = x_796;
} else {
 lean_dec_ref(x_796);
 x_799 = lean_box(0);
}
if (lean_is_scalar(x_799)) {
 x_800 = lean_alloc_ctor(1, 2, 0);
} else {
 x_800 = x_799;
}
lean_ctor_set(x_800, 0, x_797);
lean_ctor_set(x_800, 1, x_798);
return x_800;
}
}
}
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_8, x_10);
lean_dec(x_8);
x_12 = l_Lean_Syntax_getArg(x_11, x_10);
x_13 = l_Lean_Elab_Command_getRef(x_4, x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_replaceRef(x_11, x_14);
lean_dec(x_14);
x_17 = !lean_is_exclusive(x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_4, 6);
lean_dec(x_18);
lean_ctor_set(x_4, 6, x_16);
lean_inc(x_4);
x_19 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1(x_12, x_4, x_5, x_15);
lean_dec(x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_100; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_4);
x_100 = l_Lean_Elab_Command_checkValidCtorModifier(x_20, x_4, x_5, x_21);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_Lean_Elab_Modifiers_isPrivate(x_20);
if (x_102 == 0)
{
x_22 = x_101;
goto block_99;
}
else
{
uint8_t x_103; 
x_103 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_103 == 0)
{
x_22 = x_101;
goto block_99;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
lean_dec(x_20);
lean_dec(x_11);
x_104 = l___private_Lean_Elab_Structure_2__expandCtor___closed__6;
x_105 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_104, x_4, x_5, x_101);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
return x_105;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_105, 0);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_105);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_11);
x_110 = !lean_is_exclusive(x_100);
if (x_110 == 0)
{
return x_100;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_100, 0);
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_100);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
block_99:
{
uint8_t x_23; 
x_23 = l_Lean_Elab_Modifiers_isProtected(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_24 = lean_unsigned_to_nat(2u);
x_25 = l_Lean_Syntax_getArg(x_11, x_24);
x_26 = l_Lean_Syntax_isNone(x_25);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = l_Lean_Syntax_getIdAt(x_11, x_27);
lean_inc(x_28);
x_29 = l_Lean_Name_append___main(x_3, x_28);
x_30 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_31 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__5(x_30, x_29, x_4, x_5, x_22);
if (x_26 == 0)
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = 1;
x_35 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_35, 0, x_11);
lean_ctor_set(x_35, 1, x_20);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*4, x_34);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = 1;
x_39 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_39, 0, x_11);
lean_ctor_set(x_39, 1, x_20);
lean_ctor_set(x_39, 2, x_28);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_11);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_31, 0);
x_47 = 0;
x_48 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_20);
lean_ctor_set(x_48, 2, x_28);
lean_ctor_set(x_48, 3, x_46);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_47);
lean_ctor_set(x_31, 0, x_48);
return x_31;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_31, 0);
x_50 = lean_ctor_get(x_31, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_31);
x_51 = 0;
x_52 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_52, 0, x_11);
lean_ctor_set(x_52, 1, x_20);
lean_ctor_set(x_52, 2, x_28);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set_uint8(x_52, sizeof(void*)*4, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_11);
x_54 = !lean_is_exclusive(x_31);
if (x_54 == 0)
{
return x_31;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_31);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
x_58 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_59 = lean_unsigned_to_nat(2u);
x_60 = l_Lean_Syntax_getArg(x_11, x_59);
x_61 = l_Lean_Syntax_isNone(x_60);
lean_dec(x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = l_Lean_Syntax_getIdAt(x_11, x_62);
lean_inc(x_63);
x_64 = l_Lean_Name_append___main(x_3, x_63);
x_65 = lean_ctor_get_uint8(x_20, sizeof(void*)*2);
x_66 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__5(x_65, x_64, x_4, x_5, x_22);
if (x_61 == 0)
{
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = 1;
x_70 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_70, 0, x_11);
lean_ctor_set(x_70, 1, x_20);
lean_ctor_set(x_70, 2, x_63);
lean_ctor_set(x_70, 3, x_68);
lean_ctor_set_uint8(x_70, sizeof(void*)*4, x_69);
lean_ctor_set(x_66, 0, x_70);
return x_66;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_66, 0);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_66);
x_73 = 1;
x_74 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_74, 0, x_11);
lean_ctor_set(x_74, 1, x_20);
lean_ctor_set(x_74, 2, x_63);
lean_ctor_set(x_74, 3, x_71);
lean_ctor_set_uint8(x_74, sizeof(void*)*4, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_63);
lean_dec(x_20);
lean_dec(x_11);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
return x_66;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_66, 0);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_66);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_66);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_66, 0);
x_82 = 0;
x_83 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_83, 0, x_11);
lean_ctor_set(x_83, 1, x_20);
lean_ctor_set(x_83, 2, x_63);
lean_ctor_set(x_83, 3, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_82);
lean_ctor_set(x_66, 0, x_83);
return x_66;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_66, 0);
x_85 = lean_ctor_get(x_66, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_66);
x_86 = 0;
x_87 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_87, 0, x_11);
lean_ctor_set(x_87, 1, x_20);
lean_ctor_set(x_87, 2, x_63);
lean_ctor_set(x_87, 3, x_84);
lean_ctor_set_uint8(x_87, sizeof(void*)*4, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_63);
lean_dec(x_20);
lean_dec(x_11);
x_89 = !lean_is_exclusive(x_66);
if (x_89 == 0)
{
return x_66;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_66, 0);
x_91 = lean_ctor_get(x_66, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_66);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_20);
lean_dec(x_11);
x_93 = l___private_Lean_Elab_Structure_2__expandCtor___closed__3;
x_94 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_93, x_4, x_5, x_22);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
return x_94;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_4);
lean_dec(x_11);
x_114 = !lean_is_exclusive(x_19);
if (x_114 == 0)
{
return x_19;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_19, 0);
x_116 = lean_ctor_get(x_19, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_19);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_4, 0);
x_119 = lean_ctor_get(x_4, 1);
x_120 = lean_ctor_get(x_4, 2);
x_121 = lean_ctor_get(x_4, 3);
x_122 = lean_ctor_get(x_4, 4);
x_123 = lean_ctor_get(x_4, 5);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_4);
x_124 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_124, 0, x_118);
lean_ctor_set(x_124, 1, x_119);
lean_ctor_set(x_124, 2, x_120);
lean_ctor_set(x_124, 3, x_121);
lean_ctor_set(x_124, 4, x_122);
lean_ctor_set(x_124, 5, x_123);
lean_ctor_set(x_124, 6, x_16);
lean_inc(x_124);
x_125 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1(x_12, x_124, x_5, x_15);
lean_dec(x_12);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_194; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_124);
x_194 = l_Lean_Elab_Command_checkValidCtorModifier(x_126, x_124, x_5, x_127);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
x_196 = l_Lean_Elab_Modifiers_isPrivate(x_126);
if (x_196 == 0)
{
x_128 = x_195;
goto block_193;
}
else
{
uint8_t x_197; 
x_197 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_197 == 0)
{
x_128 = x_195;
goto block_193;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_126);
lean_dec(x_11);
x_198 = l___private_Lean_Elab_Structure_2__expandCtor___closed__6;
x_199 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_198, x_124, x_5, x_195);
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
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec(x_11);
x_204 = lean_ctor_get(x_194, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_194, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_206 = x_194;
} else {
 lean_dec_ref(x_194);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
block_193:
{
uint8_t x_129; 
x_129 = l_Lean_Elab_Modifiers_isProtected(x_126);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_130 = lean_unsigned_to_nat(2u);
x_131 = l_Lean_Syntax_getArg(x_11, x_130);
x_132 = l_Lean_Syntax_isNone(x_131);
lean_dec(x_131);
x_133 = lean_unsigned_to_nat(1u);
x_134 = l_Lean_Syntax_getIdAt(x_11, x_133);
lean_inc(x_134);
x_135 = l_Lean_Name_append___main(x_3, x_134);
x_136 = lean_ctor_get_uint8(x_126, sizeof(void*)*2);
x_137 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__5(x_136, x_135, x_124, x_5, x_128);
if (x_132 == 0)
{
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = 1;
x_142 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_142, 0, x_11);
lean_ctor_set(x_142, 1, x_126);
lean_ctor_set(x_142, 2, x_134);
lean_ctor_set(x_142, 3, x_138);
lean_ctor_set_uint8(x_142, sizeof(void*)*4, x_141);
if (lean_is_scalar(x_140)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_140;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_139);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_134);
lean_dec(x_126);
lean_dec(x_11);
x_144 = lean_ctor_get(x_137, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_137, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_146 = x_137;
} else {
 lean_dec_ref(x_137);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_137, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_137, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_150 = x_137;
} else {
 lean_dec_ref(x_137);
 x_150 = lean_box(0);
}
x_151 = 0;
x_152 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_152, 0, x_11);
lean_ctor_set(x_152, 1, x_126);
lean_ctor_set(x_152, 2, x_134);
lean_ctor_set(x_152, 3, x_148);
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_151);
if (lean_is_scalar(x_150)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_150;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_149);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_134);
lean_dec(x_126);
lean_dec(x_11);
x_154 = lean_ctor_get(x_137, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_137, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_156 = x_137;
} else {
 lean_dec_ref(x_137);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
else
{
uint8_t x_158; 
x_158 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_159 = lean_unsigned_to_nat(2u);
x_160 = l_Lean_Syntax_getArg(x_11, x_159);
x_161 = l_Lean_Syntax_isNone(x_160);
lean_dec(x_160);
x_162 = lean_unsigned_to_nat(1u);
x_163 = l_Lean_Syntax_getIdAt(x_11, x_162);
lean_inc(x_163);
x_164 = l_Lean_Name_append___main(x_3, x_163);
x_165 = lean_ctor_get_uint8(x_126, sizeof(void*)*2);
x_166 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__5(x_165, x_164, x_124, x_5, x_128);
if (x_161 == 0)
{
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = 1;
x_171 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_171, 0, x_11);
lean_ctor_set(x_171, 1, x_126);
lean_ctor_set(x_171, 2, x_163);
lean_ctor_set(x_171, 3, x_167);
lean_ctor_set_uint8(x_171, sizeof(void*)*4, x_170);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_168);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_163);
lean_dec(x_126);
lean_dec(x_11);
x_173 = lean_ctor_get(x_166, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_166, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_175 = x_166;
} else {
 lean_dec_ref(x_166);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_166, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_166, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_179 = x_166;
} else {
 lean_dec_ref(x_166);
 x_179 = lean_box(0);
}
x_180 = 0;
x_181 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_181, 0, x_11);
lean_ctor_set(x_181, 1, x_126);
lean_ctor_set(x_181, 2, x_163);
lean_ctor_set(x_181, 3, x_177);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_180);
if (lean_is_scalar(x_179)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_179;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_178);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_163);
lean_dec(x_126);
lean_dec(x_11);
x_183 = lean_ctor_get(x_166, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_166, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_185 = x_166;
} else {
 lean_dec_ref(x_166);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_126);
lean_dec(x_11);
x_187 = l___private_Lean_Elab_Structure_2__expandCtor___closed__3;
x_188 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_187, x_124, x_5, x_128);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
if (lean_is_scalar(x_191)) {
 x_192 = lean_alloc_ctor(1, 2, 0);
} else {
 x_192 = x_191;
}
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_190);
return x_192;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_124);
lean_dec(x_11);
x_208 = lean_ctor_get(x_125, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_125, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_210 = x_125;
} else {
 lean_dec_ref(x_125);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_8);
lean_dec(x_4);
x_212 = l___private_Lean_Elab_Structure_1__defaultCtorName;
x_213 = l_Lean_Name_append___main(x_3, x_212);
x_214 = l_Lean_Elab_Command_CtorView_inhabited___closed__1;
x_215 = 0;
x_216 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_216, 0, x_1);
lean_ctor_set(x_216, 1, x_214);
lean_ctor_set(x_216, 2, x_212);
lean_ctor_set(x_216, 3, x_213);
lean_ctor_set_uint8(x_216, sizeof(void*)*4, x_215);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_6);
return x_217;
}
}
}
lean_object* l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_2__expandCtor___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabAttr___at___private_Lean_Elab_Structure_2__expandCtor___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_foldlStepMAux___main___at___private_Lean_Elab_Structure_2__expandCtor___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_foldlStepMAux___main___at___private_Lean_Elab_Structure_2__expandCtor___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabDeclAttrs___at___private_Lean_Elab_Structure_2__expandCtor___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
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
x_44 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_43, x_2, x_3, x_4);
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
x_11 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_10, x_2, x_3, x_5);
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
x_16 = l_Lean_Elab_Modifiers_isPrivate(x_1);
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
x_20 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_19, x_2, x_3, x_5);
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
x_30 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_29, x_2, x_3, x_26);
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
x_36 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_35, x_2, x_3, x_26);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_57; 
x_18 = lean_array_fget(x_9, x_10);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_10, x_19);
lean_dec(x_10);
x_21 = l_Lean_Syntax_getId(x_18);
x_22 = l_Lean_isInternalSubobjectFieldName(x_21);
x_57 = l_Lean_Elab_Command_getRef(x_12, x_13, x_14);
if (x_22 == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = 0;
x_23 = x_60;
x_24 = x_58;
x_25 = x_59;
goto block_56;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = 1;
x_23 = x_63;
x_24 = x_61;
x_25 = x_62;
goto block_56;
}
block_56:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = l_Lean_replaceRef(x_18, x_24);
lean_dec(x_24);
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
x_29 = lean_ctor_get(x_12, 2);
x_30 = lean_ctor_get(x_12, 3);
x_31 = lean_ctor_get(x_12, 4);
x_32 = lean_ctor_get(x_12, 5);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_33 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_30);
lean_ctor_set(x_33, 4, x_31);
lean_ctor_set(x_33, 5, x_32);
lean_ctor_set(x_33, 6, x_26);
if (x_23 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
lean_inc(x_21);
x_34 = l_Lean_Name_append___main(x_1, x_21);
x_35 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_36 = l_Lean_Elab_applyVisibility___at_Lean_Elab_Command_expandDeclId___spec__5(x_35, x_34, x_33, x_13, x_25);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_39 = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(x_39, 0, x_18);
lean_ctor_set(x_39, 1, x_4);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_21);
lean_ctor_set(x_39, 4, x_6);
lean_ctor_set(x_39, 5, x_7);
lean_ctor_set(x_39, 6, x_8);
lean_ctor_set_uint8(x_39, sizeof(void*)*7, x_3);
lean_ctor_set_uint8(x_39, sizeof(void*)*7 + 1, x_5);
x_40 = lean_array_push(x_11, x_39);
x_10 = x_20;
x_11 = x_40;
x_14 = x_38;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_36, 0);
x_44 = lean_ctor_get(x_36, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_36);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_21);
x_47 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main___closed__7;
x_48 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3;
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_50, x_33, x_13, x_25);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
return x_51;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_51);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structExplicitBinder");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'protected' field in a 'private' structure");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid 'private' field in a 'private' structure");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structImplicitBinder");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("structInstBinder");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__11;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected kind of structure field");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
uint8_t _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__16() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_Lean_BinderInfo_beq(x_1, x_1);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_219; 
x_13 = lean_array_fget(x_4, x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
lean_inc(x_13);
x_25 = l_Lean_Syntax_getKind(x_13);
x_26 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2;
x_27 = lean_name_eq(x_25, x_26);
x_219 = l_Lean_Elab_Command_getRef(x_7, x_8, x_9);
if (x_27 == 0)
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
x_222 = 0;
x_28 = x_222;
x_29 = x_220;
x_30 = x_221;
goto block_218;
}
else
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_ctor_get(x_219, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_219, 1);
lean_inc(x_224);
lean_dec(x_219);
x_225 = 1;
x_28 = x_225;
x_29 = x_223;
x_30 = x_224;
goto block_218;
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
block_218:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_31 = l_Lean_replaceRef(x_13, x_29);
lean_dec(x_29);
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
x_34 = lean_ctor_get(x_7, 2);
x_35 = lean_ctor_get(x_7, 3);
x_36 = lean_ctor_get(x_7, 4);
x_37 = lean_ctor_get(x_7, 5);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_38 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
lean_ctor_set(x_38, 5, x_37);
lean_ctor_set(x_38, 6, x_31);
if (x_28 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__10;
x_113 = lean_name_eq(x_25, x_112);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__12;
x_115 = lean_name_eq(x_25, x_114);
lean_dec(x_25);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec(x_13);
lean_dec(x_6);
x_116 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__15;
x_117 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_116, x_38, x_8, x_30);
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
x_16 = x_117;
goto block_24;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_117);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_16 = x_121;
goto block_24;
}
}
else
{
uint8_t x_122; 
x_122 = 3;
x_39 = x_122;
x_40 = x_30;
goto block_111;
}
}
else
{
uint8_t x_123; 
lean_dec(x_25);
x_123 = 1;
x_39 = x_123;
x_40 = x_30;
goto block_111;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_25);
x_124 = lean_unsigned_to_nat(0u);
x_125 = l_Lean_Syntax_getArg(x_13, x_124);
lean_inc(x_38);
x_126 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1(x_125, x_38, x_8, x_30);
lean_dec(x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_192; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_38);
x_192 = l_Lean_Elab_Command_checkValidFieldModifier(x_127, x_38, x_8, x_128);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = l_Lean_Elab_Modifiers_isPrivate(x_127);
if (x_194 == 0)
{
uint8_t x_195; 
x_195 = l_Lean_Elab_Modifiers_isProtected(x_127);
if (x_195 == 0)
{
x_129 = x_193;
goto block_191;
}
else
{
uint8_t x_196; 
x_196 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_196 == 0)
{
x_129 = x_193;
goto block_191;
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_127);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_6);
x_197 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5;
x_198 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_197, x_38, x_8, x_193);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
return x_198;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_198);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
else
{
uint8_t x_203; 
x_203 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_203 == 0)
{
x_129 = x_193;
goto block_191;
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; 
lean_dec(x_127);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_6);
x_204 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8;
x_205 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_204, x_38, x_8, x_193);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
return x_205;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_205);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_127);
lean_dec(x_38);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_6);
x_210 = !lean_is_exclusive(x_192);
if (x_210 == 0)
{
return x_192;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_192, 0);
x_212 = lean_ctor_get(x_192, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_192);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
block_191:
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_130 = lean_unsigned_to_nat(3u);
x_131 = l_Lean_Syntax_getArg(x_13, x_130);
x_132 = l_Lean_Syntax_isNone(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
uint8_t x_189; 
x_189 = 1;
x_133 = x_189;
goto block_188;
}
else
{
uint8_t x_190; 
x_190 = 0;
x_133 = x_190;
goto block_188;
}
block_188:
{
lean_object* x_134; lean_object* x_135; uint8_t x_176; 
x_176 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__16;
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_unsigned_to_nat(4u);
x_178 = l_Lean_Syntax_getArg(x_13, x_177);
x_179 = l_Lean_Elab_expandDeclSig(x_178);
lean_dec(x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_134 = x_180;
x_135 = x_182;
goto block_175;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_183 = lean_unsigned_to_nat(4u);
x_184 = l_Lean_Syntax_getArg(x_13, x_183);
x_185 = l_Lean_Elab_expandOptDeclSig(x_184);
lean_dec(x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_134 = x_186;
x_135 = x_187;
goto block_175;
}
block_175:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_unsigned_to_nat(2u);
x_137 = l_Lean_Syntax_getArg(x_13, x_136);
x_138 = l_Lean_Syntax_getArgs(x_137);
lean_dec(x_137);
x_139 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__16;
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_140 = lean_box(0);
x_141 = 0;
x_142 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_13, x_141, x_127, x_133, x_134, x_135, x_140, x_138, x_124, x_6, x_38, x_8, x_129);
lean_dec(x_38);
lean_dec(x_138);
lean_dec(x_13);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_5 = x_15;
x_6 = x_143;
x_9 = x_144;
goto _start;
}
else
{
uint8_t x_146; 
lean_dec(x_15);
x_146 = !lean_is_exclusive(x_142);
if (x_146 == 0)
{
return x_142;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_142, 0);
x_148 = lean_ctor_get(x_142, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_142);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_unsigned_to_nat(5u);
x_151 = l_Lean_Syntax_getArg(x_13, x_150);
x_152 = l_Lean_Syntax_isNone(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; 
x_153 = l_Lean_Syntax_getArg(x_151, x_124);
lean_dec(x_151);
x_154 = l_Lean_Syntax_getArg(x_153, x_14);
lean_dec(x_153);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = 0;
x_157 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_13, x_156, x_127, x_133, x_134, x_135, x_155, x_138, x_124, x_6, x_38, x_8, x_129);
lean_dec(x_38);
lean_dec(x_138);
lean_dec(x_13);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_5 = x_15;
x_6 = x_158;
x_9 = x_159;
goto _start;
}
else
{
uint8_t x_161; 
lean_dec(x_15);
x_161 = !lean_is_exclusive(x_157);
if (x_161 == 0)
{
return x_157;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_157, 0);
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_157);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
lean_object* x_165; uint8_t x_166; lean_object* x_167; 
lean_dec(x_151);
x_165 = lean_box(0);
x_166 = 0;
x_167 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_13, x_166, x_127, x_133, x_134, x_135, x_165, x_138, x_124, x_6, x_38, x_8, x_129);
lean_dec(x_38);
lean_dec(x_138);
lean_dec(x_13);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_5 = x_15;
x_6 = x_168;
x_9 = x_169;
goto _start;
}
else
{
uint8_t x_171; 
lean_dec(x_15);
x_171 = !lean_is_exclusive(x_167);
if (x_171 == 0)
{
return x_167;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_167, 0);
x_173 = lean_ctor_get(x_167, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_167);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
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
uint8_t x_214; 
lean_dec(x_38);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_6);
x_214 = !lean_is_exclusive(x_126);
if (x_214 == 0)
{
return x_126;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_126, 0);
x_216 = lean_ctor_get(x_126, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_126);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
block_111:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Syntax_getArg(x_13, x_41);
lean_inc(x_38);
x_43 = l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1(x_42, x_38, x_8, x_40);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_85; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_38);
x_85 = l_Lean_Elab_Command_checkValidFieldModifier(x_44, x_38, x_8, x_45);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Lean_Elab_Modifiers_isPrivate(x_44);
if (x_87 == 0)
{
uint8_t x_88; 
x_88 = l_Lean_Elab_Modifiers_isProtected(x_44);
if (x_88 == 0)
{
x_46 = x_86;
goto block_84;
}
else
{
uint8_t x_89; 
x_89 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_89 == 0)
{
x_46 = x_86;
goto block_84;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_44);
lean_dec(x_13);
lean_dec(x_6);
x_90 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__5;
x_91 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_90, x_38, x_8, x_86);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
x_16 = x_91;
goto block_24;
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
x_16 = x_95;
goto block_24;
}
}
}
}
else
{
uint8_t x_96; 
x_96 = l_Lean_Elab_Modifiers_isPrivate(x_2);
if (x_96 == 0)
{
x_46 = x_86;
goto block_84;
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_44);
lean_dec(x_13);
lean_dec(x_6);
x_97 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__8;
x_98 = l_Lean_throwError___at___private_Lean_Elab_Command_3__elabCommandUsing___main___spec__1___rarg(x_97, x_38, x_8, x_86);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
x_16 = x_98;
goto block_24;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_98);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_16 = x_102;
goto block_24;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_44);
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_6);
x_103 = !lean_is_exclusive(x_85);
if (x_103 == 0)
{
x_16 = x_85;
goto block_24;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_85, 0);
x_105 = lean_ctor_get(x_85, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_85);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_16 = x_106;
goto block_24;
}
}
block_84:
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; 
x_47 = lean_unsigned_to_nat(3u);
x_48 = l_Lean_Syntax_getArg(x_13, x_47);
x_49 = l_Lean_Syntax_isNone(x_48);
lean_dec(x_48);
x_50 = 0;
x_51 = l_Lean_BinderInfo_beq(x_39, x_50);
if (x_49 == 0)
{
uint8_t x_82; 
x_82 = 1;
x_52 = x_82;
goto block_81;
}
else
{
uint8_t x_83; 
x_83 = 0;
x_52 = x_83;
goto block_81;
}
block_81:
{
lean_object* x_53; lean_object* x_54; 
if (x_51 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_unsigned_to_nat(4u);
x_71 = l_Lean_Syntax_getArg(x_13, x_70);
x_72 = l_Lean_Elab_expandDeclSig(x_71);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_53 = x_73;
x_54 = x_75;
goto block_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_unsigned_to_nat(4u);
x_77 = l_Lean_Syntax_getArg(x_13, x_76);
x_78 = l_Lean_Elab_expandOptDeclSig(x_77);
lean_dec(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_53 = x_79;
x_54 = x_80;
goto block_69;
}
block_69:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_unsigned_to_nat(2u);
x_56 = l_Lean_Syntax_getArg(x_13, x_55);
x_57 = l_Lean_Syntax_getArgs(x_56);
lean_dec(x_56);
if (x_51 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_box(0);
x_59 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_13, x_39, x_44, x_52, x_53, x_54, x_58, x_57, x_41, x_6, x_38, x_8, x_46);
lean_dec(x_38);
lean_dec(x_57);
lean_dec(x_13);
x_16 = x_59;
goto block_24;
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_unsigned_to_nat(5u);
x_61 = l_Lean_Syntax_getArg(x_13, x_60);
x_62 = l_Lean_Syntax_isNone(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = l_Lean_Syntax_getArg(x_61, x_41);
lean_dec(x_61);
x_64 = l_Lean_Syntax_getArg(x_63, x_14);
lean_dec(x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_13, x_39, x_44, x_52, x_53, x_54, x_65, x_57, x_41, x_6, x_38, x_8, x_46);
lean_dec(x_38);
lean_dec(x_57);
lean_dec(x_13);
x_16 = x_66;
goto block_24;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_61);
x_67 = lean_box(0);
x_68 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_3, x_13, x_39, x_44, x_52, x_53, x_54, x_67, x_57, x_41, x_6, x_38, x_8, x_46);
lean_dec(x_38);
lean_dec(x_57);
lean_dec(x_13);
x_16 = x_68;
goto block_24;
}
}
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_38);
lean_dec(x_13);
lean_dec(x_6);
x_107 = !lean_is_exclusive(x_43);
if (x_107 == 0)
{
x_16 = x_43;
goto block_24;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_43, 0);
x_109 = lean_ctor_get(x_43, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_43);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_16 = x_110;
goto block_24;
}
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
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn___main(x_1);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_get(x_7, x_8);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_10);
x_16 = l_Lean_isStructure(x_15, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_free_object(x_11);
x_17 = l_System_FilePath_dirName___closed__1;
x_18 = l_Lean_Name_toStringWithSep___main(x_17, x_10);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
return x_25;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_dec(x_2);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_10);
x_33 = l_Lean_isStructure(x_32, x_10);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = l_System_FilePath_dirName___closed__1;
x_35 = l_Lean_Name_toStringWithSep___main(x_34, x_10);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_10);
lean_ctor_set(x_47, 1, x_31);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_9);
x_48 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3;
x_49 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_48, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_49;
}
}
}
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
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
lean_object* l_Lean_Meta_mkProjection___at___private_Lean_Elab_Structure_8__processSubfields___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_2);
x_17 = l_Lean_Name_append___main(x_1, x_2);
x_18 = lean_box(0);
x_19 = 1;
x_20 = 0;
x_21 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_9);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*4 + 1, x_20);
x_22 = lean_array_push(x_3, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
x_25 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(x_1, x_5, x_6, x_7, x_24, x_22, x_8, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_25;
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
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_5, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_apply_8(x_7, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_array_fget(x_4, x_5);
x_19 = lean_st_ref_get(x_13, x_14);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l___private_Lean_Elab_Structure_7__containsFieldName(x_6, x_18);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_18);
lean_inc(x_2);
x_22 = l___private_Lean_Meta_AppBuilder_25__mkProjectionImp___main(x_2, x_18, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_23);
x_25 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_18);
x_28 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed), 16, 8);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_18);
lean_closure_set(x_28, 2, x_6);
lean_closure_set(x_28, 3, x_5);
lean_closure_set(x_28, 4, x_2);
lean_closure_set(x_28, 5, x_3);
lean_closure_set(x_28, 6, x_4);
lean_closure_set(x_28, 7, x_7);
x_29 = l_Lean_Meta_withLetDecl___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_18, x_26, x_23, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_27);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_22);
if (x_34 == 0)
{
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_22);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_38, 0, x_18);
x_39 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_40 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
x_41 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_43, 0, x_3);
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_46 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_46, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg), 14, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkProjection___at___private_Lean_Elab_Structure_8__processSubfields___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_mkProjection___at___private_Lean_Elab_Structure_8__processSubfields___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Structure_8__processSubfields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___rarg), 14, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_2, x_13, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
lean_inc(x_2);
x_17 = l_Lean_Name_append___main(x_16, x_2);
x_18 = lean_box(0);
x_19 = 2;
x_20 = 0;
lean_inc(x_8);
x_21 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_8);
lean_ctor_set(x_21, 3, x_18);
lean_ctor_set_uint8(x_21, sizeof(void*)*4, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*4 + 1, x_20);
x_22 = lean_array_push(x_3, x_21);
lean_inc(x_5);
x_23 = l_Lean_getStructureFieldsFlattened(x_4, x_5);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1___boxed), 11, 3);
lean_closure_set(x_24, 0, x_6);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_7);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(x_16, x_8, x_5, x_23, x_25, x_22, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_26;
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
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_1, 7);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_2, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_apply_8(x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget(x_12, x_2);
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_9, 3);
x_19 = l_Lean_replaceRef(x_16, x_18);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
lean_ctor_set(x_9, 3, x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_22 = l_Lean_Elab_Term_elabType(x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_5);
x_25 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_46; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Name_eraseMacroScopes(x_26);
x_29 = l_Lean_Name_getString_x21(x_28);
lean_dec(x_28);
x_30 = l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
x_31 = lean_string_append(x_30, x_29);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = lean_name_mk_string(x_32, x_31);
x_46 = l___private_Lean_Elab_Structure_7__containsFieldName(x_3, x_33);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_16);
x_47 = lean_st_ref_get(x_10, x_27);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_34 = x_50;
x_35 = x_49;
goto block_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_51, 0, x_33);
x_52 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_16, x_55, x_5, x_6, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_16);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
return x_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
block_45:
{
uint8_t x_36; lean_object* x_37; 
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_26);
lean_inc(x_34);
lean_inc(x_33);
x_37 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2), 15, 7);
lean_closure_set(x_37, 0, x_1);
lean_closure_set(x_37, 1, x_33);
lean_closure_set(x_37, 2, x_3);
lean_closure_set(x_37, 3, x_34);
lean_closure_set(x_37, 4, x_26);
lean_closure_set(x_37, 5, x_2);
lean_closure_set(x_37, 6, x_4);
if (x_36 == 0)
{
uint8_t x_38; lean_object* x_39; 
lean_dec(x_34);
lean_dec(x_26);
x_38 = 0;
x_39 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_33, x_38, x_23, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_is_class(x_34, x_26);
if (x_40 == 0)
{
uint8_t x_41; lean_object* x_42; 
x_41 = 0;
x_42 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_33, x_41, x_23, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
return x_42;
}
else
{
uint8_t x_43; lean_object* x_44; 
x_43 = 3;
x_44 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_33, x_43, x_23, x_37, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
return x_44;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_25);
if (x_61 == 0)
{
return x_25;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_25, 0);
x_63 = lean_ctor_get(x_25, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_25);
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
lean_dec(x_9);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_22);
if (x_65 == 0)
{
return x_22;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_22, 0);
x_67 = lean_ctor_get(x_22, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_22);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
x_71 = lean_ctor_get(x_9, 2);
x_72 = lean_ctor_get(x_9, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_73 = l_Lean_replaceRef(x_16, x_72);
x_74 = l_Lean_replaceRef(x_73, x_72);
lean_dec(x_73);
x_75 = l_Lean_replaceRef(x_74, x_72);
lean_dec(x_72);
lean_dec(x_74);
x_76 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_75);
lean_inc(x_10);
lean_inc(x_76);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_77 = l_Lean_Elab_Term_elabType(x_16, x_5, x_6, x_7, x_8, x_76, x_10, x_11);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_5);
x_80 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_78, x_5, x_6, x_7, x_8, x_76, x_10, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_101; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Lean_Name_eraseMacroScopes(x_81);
x_84 = l_Lean_Name_getString_x21(x_83);
lean_dec(x_83);
x_85 = l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
x_86 = lean_string_append(x_85, x_84);
lean_dec(x_84);
x_87 = lean_box(0);
x_88 = lean_name_mk_string(x_87, x_86);
x_101 = l___private_Lean_Elab_Structure_7__containsFieldName(x_3, x_88);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_16);
x_102 = lean_st_ref_get(x_10, x_82);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_89 = x_105;
x_90 = x_104;
goto block_100;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_106, 0, x_88);
x_107 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
x_109 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_16, x_110, x_5, x_6, x_7, x_8, x_76, x_10, x_82);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_16);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
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
block_100:
{
uint8_t x_91; lean_object* x_92; 
x_91 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_81);
lean_inc(x_89);
lean_inc(x_88);
x_92 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2), 15, 7);
lean_closure_set(x_92, 0, x_1);
lean_closure_set(x_92, 1, x_88);
lean_closure_set(x_92, 2, x_3);
lean_closure_set(x_92, 3, x_89);
lean_closure_set(x_92, 4, x_81);
lean_closure_set(x_92, 5, x_2);
lean_closure_set(x_92, 6, x_4);
if (x_91 == 0)
{
uint8_t x_93; lean_object* x_94; 
lean_dec(x_89);
lean_dec(x_81);
x_93 = 0;
x_94 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_88, x_93, x_78, x_92, x_5, x_6, x_7, x_8, x_76, x_10, x_90);
return x_94;
}
else
{
uint8_t x_95; 
x_95 = lean_is_class(x_89, x_81);
if (x_95 == 0)
{
uint8_t x_96; lean_object* x_97; 
x_96 = 0;
x_97 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_88, x_96, x_78, x_92, x_5, x_6, x_7, x_8, x_76, x_10, x_90);
return x_97;
}
else
{
uint8_t x_98; lean_object* x_99; 
x_98 = 3;
x_99 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_88, x_98, x_78, x_92, x_5, x_6, x_7, x_8, x_76, x_10, x_90);
return x_99;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_80, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_80, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_118 = x_80;
} else {
 lean_dec_ref(x_80);
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
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_76);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_77, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_77, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_122 = x_77;
} else {
 lean_dec_ref(x_77);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_9__withParents(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___rarg), 11, 0);
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
lean_object* l___private_Lean_Elab_Structure_10__elabFieldTypeValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 6);
lean_inc(x_11);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = l___private_Lean_Elab_Structure_10__elabFieldTypeValue___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_box(0);
x_17 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_elabTerm(x_15, x_16, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_17__elabImplicitLambdaAux___spec__1(x_2, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_11, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
lean_ctor_set(x_11, 0, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_11);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_free_object(x_11);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
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
lean_free_object(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_11, 0);
lean_inc(x_37);
lean_dec(x_11);
x_38 = lean_box(0);
x_39 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_40 = l_Lean_Elab_Term_elabTerm(x_37, x_38, x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_17__elabImplicitLambdaAux___spec__1(x_2, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_47);
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_ctor_get(x_40, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_56 = x_40;
} else {
 lean_dec_ref(x_40);
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
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_10);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_10, 0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_60 = l_Lean_Elab_Term_elabType(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_1, 6);
lean_inc(x_61);
lean_dec(x_1);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
lean_ctor_set(x_10, 0, x_66);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_10);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
lean_ctor_set(x_10, 0, x_69);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_10);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_free_object(x_10);
x_74 = !lean_is_exclusive(x_64);
if (x_74 == 0)
{
return x_64;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_64, 0);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_64);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_ctor_get(x_60, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
lean_dec(x_60);
x_80 = !lean_is_exclusive(x_61);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_61, 0);
lean_inc(x_78);
lean_ctor_set(x_61, 0, x_78);
x_82 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_83 = l_Lean_Elab_Term_elabTermEnsuringType(x_81, x_61, x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_5);
lean_inc(x_2);
x_86 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_17__elabImplicitLambdaAux___spec__1(x_2, x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_89) == 0)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_89, 0);
lean_ctor_set(x_10, 0, x_87);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_10);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_89, 0, x_93);
return x_89;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_89, 0);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_89);
lean_ctor_set(x_10, 0, x_87);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_94);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_10);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_87);
lean_free_object(x_10);
x_99 = !lean_is_exclusive(x_89);
if (x_99 == 0)
{
return x_89;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_89, 0);
x_101 = lean_ctor_get(x_89, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_89);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_84);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_86);
if (x_103 == 0)
{
return x_86;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_86, 0);
x_105 = lean_ctor_get(x_86, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_86);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_78);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_83);
if (x_107 == 0)
{
return x_83;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_83, 0);
x_109 = lean_ctor_get(x_83, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_83);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_61, 0);
lean_inc(x_111);
lean_dec(x_61);
lean_inc(x_78);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_78);
x_113 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_114 = l_Lean_Elab_Term_elabTermEnsuringType(x_111, x_112, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_5);
lean_inc(x_2);
x_117 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_17__elabImplicitLambdaAux___spec__1(x_2, x_115, x_3, x_4, x_5, x_6, x_7, x_8, x_119);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
lean_ctor_set(x_10, 0, x_118);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_121);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_10);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_123)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_123;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_122);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_118);
lean_free_object(x_10);
x_127 = lean_ctor_get(x_120, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_129 = x_120;
} else {
 lean_dec_ref(x_120);
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
lean_dec(x_115);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_131 = lean_ctor_get(x_117, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_117, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_133 = x_117;
} else {
 lean_dec_ref(x_117);
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
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_78);
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_ctor_get(x_114, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_114, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_137 = x_114;
} else {
 lean_dec_ref(x_114);
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
}
else
{
uint8_t x_139; 
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_60);
if (x_139 == 0)
{
return x_60;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_60, 0);
x_141 = lean_ctor_get(x_60, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_60);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_10, 0);
lean_inc(x_143);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_144 = l_Lean_Elab_Term_elabType(x_143, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_1, 6);
lean_inc(x_145);
lean_dec(x_1);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_146, x_3, x_4, x_5, x_6, x_7, x_8, x_147);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_149);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
if (lean_is_scalar(x_151)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_151;
}
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_150);
return x_155;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_148, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_148, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_158 = x_148;
} else {
 lean_dec_ref(x_148);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_144, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_144, 1);
lean_inc(x_161);
lean_dec(x_144);
x_162 = lean_ctor_get(x_145, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_163 = x_145;
} else {
 lean_dec_ref(x_145);
 x_163 = lean_box(0);
}
lean_inc(x_160);
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_160);
x_165 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_166 = l_Lean_Elab_Term_elabTermEnsuringType(x_162, x_164, x_165, x_3, x_4, x_5, x_6, x_7, x_8, x_161);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
lean_inc(x_5);
lean_inc(x_2);
x_169 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_160, x_3, x_4, x_5, x_6, x_7, x_8, x_168);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_172 = l_Lean_Meta_mkLambdaFVars___at___private_Lean_Elab_Term_17__elabImplicitLambdaAux___spec__1(x_2, x_167, x_3, x_4, x_5, x_6, x_7, x_8, x_171);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_170);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_173);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
if (lean_is_scalar(x_175)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_175;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_174);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_170);
x_180 = lean_ctor_get(x_172, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_172, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_182 = x_172;
} else {
 lean_dec_ref(x_172);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_167);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_184 = lean_ctor_get(x_169, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_169, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_186 = x_169;
} else {
 lean_dec_ref(x_169);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_160);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_188 = lean_ctor_get(x_166, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_166, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_190 = x_166;
} else {
 lean_dec_ref(x_166);
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
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_ctor_get(x_144, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_144, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_194 = x_144;
} else {
 lean_dec_ref(x_144);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_1, 2);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*7 + 1);
x_18 = 0;
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_8);
lean_ctor_set(x_19, 3, x_3);
lean_ctor_set_uint8(x_19, sizeof(void*)*4, x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*4 + 1, x_17);
x_20 = lean_array_push(x_4, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
x_23 = l___private_Lean_Elab_Structure_11__withFields___main___rarg(x_6, x_22, x_20, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_23;
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
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_apply_8(x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_array_fget(x_1, x_2);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 3);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(x_17, x_3, x_18);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_9, 3);
x_22 = l_Lean_replaceRef(x_16, x_21);
lean_dec(x_16);
x_23 = l_Lean_replaceRef(x_22, x_21);
lean_dec(x_22);
x_24 = l_Lean_replaceRef(x_23, x_21);
lean_dec(x_21);
lean_dec(x_23);
lean_ctor_set(x_9, 3, x_24);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_15, 4);
lean_inc(x_25);
x_26 = l_Lean_Syntax_getArgs(x_25);
lean_dec(x_25);
lean_inc(x_15);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__elabFieldTypeValue), 9, 1);
lean_closure_set(x_27, 0, x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_28 = l_Lean_Elab_Term_elabBinders___rarg(x_26, x_27, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3;
x_34 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_33, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_37 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_inc(x_17);
x_41 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed), 15, 7);
lean_closure_set(x_41, 0, x_15);
lean_closure_set(x_41, 1, x_17);
lean_closure_set(x_41, 2, x_30);
lean_closure_set(x_41, 3, x_3);
lean_closure_set(x_41, 4, x_2);
lean_closure_set(x_41, 5, x_1);
lean_closure_set(x_41, 6, x_4);
x_42 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_17, x_40, x_38, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_39);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_47 = lean_ctor_get(x_28, 1);
lean_inc(x_47);
lean_dec(x_28);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = lean_ctor_get(x_30, 0);
lean_inc(x_49);
lean_dec(x_30);
x_50 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_inc(x_17);
x_51 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed), 15, 7);
lean_closure_set(x_51, 0, x_15);
lean_closure_set(x_51, 1, x_17);
lean_closure_set(x_51, 2, x_48);
lean_closure_set(x_51, 3, x_3);
lean_closure_set(x_51, 4, x_2);
lean_closure_set(x_51, 5, x_1);
lean_closure_set(x_51, 6, x_4);
x_52 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_17, x_50, x_49, x_51, x_5, x_6, x_7, x_8, x_9, x_10, x_47);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_9);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_28);
if (x_53 == 0)
{
return x_28;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_28, 0);
x_55 = lean_ctor_get(x_28, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_28);
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
x_57 = !lean_is_exclusive(x_19);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_19, 0);
x_59 = lean_ctor_get_uint8(x_58, sizeof(void*)*4);
switch (x_59) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_free_object(x_19);
lean_dec(x_58);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_60, 0, x_17);
x_61 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_62 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
x_63 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_64 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_64, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_65;
}
case 1:
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_15, 6);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_19);
lean_dec(x_58);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_67, 0, x_17);
x_68 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6;
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_71, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_58);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_58, 0);
x_75 = lean_ctor_get(x_58, 1);
x_76 = lean_ctor_get(x_58, 2);
x_77 = lean_ctor_get(x_58, 3);
lean_dec(x_77);
x_78 = !lean_is_exclusive(x_66);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_79 = lean_ctor_get(x_66, 0);
x_102 = lean_ctor_get(x_15, 4);
lean_inc(x_102);
x_103 = l_Lean_Syntax_getArgs(x_102);
lean_dec(x_102);
x_104 = l_Array_isEmpty___rarg(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; 
lean_free_object(x_66);
lean_dec(x_79);
lean_free_object(x_58);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_box(0);
x_80 = x_105;
goto block_101;
}
else
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_15, 5);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
lean_dec(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_76);
x_107 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_76, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_ctor_set(x_66, 0, x_108);
x_110 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_111 = l_Lean_Elab_Term_elabTermEnsuringType(x_79, x_66, x_110, x_5, x_6, x_7, x_8, x_9, x_10, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_ctor_set(x_19, 0, x_112);
lean_ctor_set(x_58, 3, x_19);
x_114 = lean_array_push(x_3, x_58);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_add(x_2, x_115);
lean_dec(x_2);
x_2 = x_116;
x_3 = x_114;
x_11 = x_113;
goto _start;
}
else
{
uint8_t x_118; 
lean_free_object(x_58);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_19);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_111);
if (x_118 == 0)
{
return x_111;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_111, 0);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_111);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
uint8_t x_122; 
lean_free_object(x_66);
lean_dec(x_79);
lean_free_object(x_58);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_19);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_107);
if (x_122 == 0)
{
return x_107;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_107, 0);
x_124 = lean_ctor_get(x_107, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_107);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; 
lean_dec(x_106);
lean_free_object(x_66);
lean_dec(x_79);
lean_free_object(x_58);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_box(0);
x_80 = x_126;
goto block_101;
}
}
block_101:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_80);
x_81 = lean_ctor_get(x_15, 5);
lean_inc(x_81);
lean_dec(x_15);
x_82 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_82, 0, x_17);
x_83 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = l_Lean_Syntax_inhabited;
x_88 = l_Option_get_x21___rarg___closed__3;
x_89 = lean_panic_fn(x_87, x_88);
x_90 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_89, x_86, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_89);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
return x_90;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_90);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_81, 0);
lean_inc(x_95);
lean_dec(x_81);
x_96 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_95, x_86, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_95);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
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
return x_100;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_127 = lean_ctor_get(x_66, 0);
lean_inc(x_127);
lean_dec(x_66);
x_150 = lean_ctor_get(x_15, 4);
lean_inc(x_150);
x_151 = l_Lean_Syntax_getArgs(x_150);
lean_dec(x_150);
x_152 = l_Array_isEmpty___rarg(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; 
lean_dec(x_127);
lean_free_object(x_58);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = lean_box(0);
x_128 = x_153;
goto block_149;
}
else
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_15, 5);
lean_inc(x_154);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; 
lean_dec(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_76);
x_155 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_76, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_156);
x_159 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_160 = l_Lean_Elab_Term_elabTermEnsuringType(x_127, x_158, x_159, x_5, x_6, x_7, x_8, x_9, x_10, x_157);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
lean_ctor_set(x_19, 0, x_161);
lean_ctor_set(x_58, 3, x_19);
x_163 = lean_array_push(x_3, x_58);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_nat_add(x_2, x_164);
lean_dec(x_2);
x_2 = x_165;
x_3 = x_163;
x_11 = x_162;
goto _start;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_free_object(x_58);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_19);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = lean_ctor_get(x_160, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_169 = x_160;
} else {
 lean_dec_ref(x_160);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_127);
lean_free_object(x_58);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_19);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_155, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_155, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_173 = x_155;
} else {
 lean_dec_ref(x_155);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
lean_object* x_175; 
lean_dec(x_154);
lean_dec(x_127);
lean_free_object(x_58);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_free_object(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_box(0);
x_128 = x_175;
goto block_149;
}
}
block_149:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_128);
x_129 = lean_ctor_get(x_15, 5);
lean_inc(x_129);
lean_dec(x_15);
x_130 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_130, 0, x_17);
x_131 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_132 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_130);
x_133 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_134 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_135 = l_Lean_Syntax_inhabited;
x_136 = l_Option_get_x21___rarg___closed__3;
x_137 = lean_panic_fn(x_135, x_136);
x_138 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_137, x_134, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_137);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
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
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_129, 0);
lean_inc(x_143);
lean_dec(x_129);
x_144 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_143, x_134, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_147 = x_144;
} else {
 lean_dec_ref(x_144);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_176 = lean_ctor_get(x_58, 0);
x_177 = lean_ctor_get(x_58, 1);
x_178 = lean_ctor_get(x_58, 2);
x_179 = lean_ctor_get_uint8(x_58, sizeof(void*)*4 + 1);
lean_inc(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_58);
x_180 = lean_ctor_get(x_66, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_181 = x_66;
} else {
 lean_dec_ref(x_66);
 x_181 = lean_box(0);
}
x_204 = lean_ctor_get(x_15, 4);
lean_inc(x_204);
x_205 = l_Lean_Syntax_getArgs(x_204);
lean_dec(x_204);
x_206 = l_Array_isEmpty___rarg(x_205);
lean_dec(x_205);
if (x_206 == 0)
{
lean_object* x_207; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_free_object(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_box(0);
x_182 = x_207;
goto block_203;
}
else
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_15, 5);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; 
lean_dec(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_178);
x_209 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_178, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
if (lean_is_scalar(x_181)) {
 x_212 = lean_alloc_ctor(1, 1, 0);
} else {
 x_212 = x_181;
}
lean_ctor_set(x_212, 0, x_210);
x_213 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_214 = l_Lean_Elab_Term_elabTermEnsuringType(x_180, x_212, x_213, x_5, x_6, x_7, x_8, x_9, x_10, x_211);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
lean_ctor_set(x_19, 0, x_215);
x_217 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_217, 0, x_176);
lean_ctor_set(x_217, 1, x_177);
lean_ctor_set(x_217, 2, x_178);
lean_ctor_set(x_217, 3, x_19);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_59);
lean_ctor_set_uint8(x_217, sizeof(void*)*4 + 1, x_179);
x_218 = lean_array_push(x_3, x_217);
x_219 = lean_unsigned_to_nat(1u);
x_220 = lean_nat_add(x_2, x_219);
lean_dec(x_2);
x_2 = x_220;
x_3 = x_218;
x_11 = x_216;
goto _start;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_free_object(x_19);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_222 = lean_ctor_get(x_214, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_214, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_224 = x_214;
} else {
 lean_dec_ref(x_214);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_free_object(x_19);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_226 = lean_ctor_get(x_209, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_209, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_228 = x_209;
} else {
 lean_dec_ref(x_209);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; 
lean_dec(x_208);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_free_object(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = lean_box(0);
x_182 = x_230;
goto block_203;
}
}
block_203:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_182);
x_183 = lean_ctor_get(x_15, 5);
lean_inc(x_183);
lean_dec(x_15);
x_184 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_184, 0, x_17);
x_185 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_186 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_184);
x_187 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_188 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_189 = l_Lean_Syntax_inhabited;
x_190 = l_Option_get_x21___rarg___closed__3;
x_191 = lean_panic_fn(x_189, x_190);
x_192 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_191, x_188, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_195 = x_192;
} else {
 lean_dec_ref(x_192);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_193);
lean_ctor_set(x_196, 1, x_194);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_197 = lean_ctor_get(x_183, 0);
lean_inc(x_197);
lean_dec(x_183);
x_198 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_197, x_188, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_197);
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
}
}
default: 
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_free_object(x_19);
lean_dec(x_58);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_231 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_232 = l_unreachable_x21___rarg(x_231);
x_233 = lean_apply_7(x_232, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_233;
}
}
}
else
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_19, 0);
lean_inc(x_234);
lean_dec(x_19);
x_235 = lean_ctor_get_uint8(x_234, sizeof(void*)*4);
switch (x_235) {
case 0:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_234);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_236, 0, x_17);
x_237 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_238 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
x_239 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_240 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_240, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_241;
}
case 1:
{
lean_object* x_242; 
x_242 = lean_ctor_get(x_15, 6);
lean_inc(x_242);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_234);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_243 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_243, 0, x_17);
x_244 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_245 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_243);
x_246 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6;
x_247 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_247, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_278; lean_object* x_279; uint8_t x_280; 
x_249 = lean_ctor_get(x_234, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_234, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_234, 2);
lean_inc(x_251);
x_252 = lean_ctor_get_uint8(x_234, sizeof(void*)*4 + 1);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 lean_ctor_release(x_234, 2);
 lean_ctor_release(x_234, 3);
 x_253 = x_234;
} else {
 lean_dec_ref(x_234);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_242, 0);
lean_inc(x_254);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 x_255 = x_242;
} else {
 lean_dec_ref(x_242);
 x_255 = lean_box(0);
}
x_278 = lean_ctor_get(x_15, 4);
lean_inc(x_278);
x_279 = l_Lean_Syntax_getArgs(x_278);
lean_dec(x_278);
x_280 = l_Array_isEmpty___rarg(x_279);
lean_dec(x_279);
if (x_280 == 0)
{
lean_object* x_281; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = lean_box(0);
x_256 = x_281;
goto block_277;
}
else
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_15, 5);
lean_inc(x_282);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; 
lean_dec(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_251);
x_283 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_251, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
if (lean_is_scalar(x_255)) {
 x_286 = lean_alloc_ctor(1, 1, 0);
} else {
 x_286 = x_255;
}
lean_ctor_set(x_286, 0, x_284);
x_287 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_288 = l_Lean_Elab_Term_elabTermEnsuringType(x_254, x_286, x_287, x_5, x_6, x_7, x_8, x_9, x_10, x_285);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_289);
if (lean_is_scalar(x_253)) {
 x_292 = lean_alloc_ctor(0, 4, 2);
} else {
 x_292 = x_253;
}
lean_ctor_set(x_292, 0, x_249);
lean_ctor_set(x_292, 1, x_250);
lean_ctor_set(x_292, 2, x_251);
lean_ctor_set(x_292, 3, x_291);
lean_ctor_set_uint8(x_292, sizeof(void*)*4, x_235);
lean_ctor_set_uint8(x_292, sizeof(void*)*4 + 1, x_252);
x_293 = lean_array_push(x_3, x_292);
x_294 = lean_unsigned_to_nat(1u);
x_295 = lean_nat_add(x_2, x_294);
lean_dec(x_2);
x_2 = x_295;
x_3 = x_293;
x_11 = x_290;
goto _start;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = lean_ctor_get(x_288, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_288, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_299 = x_288;
} else {
 lean_dec_ref(x_288);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_301 = lean_ctor_get(x_283, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_283, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_303 = x_283;
} else {
 lean_dec_ref(x_283);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
else
{
lean_object* x_305; 
lean_dec(x_282);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = lean_box(0);
x_256 = x_305;
goto block_277;
}
}
block_277:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_256);
x_257 = lean_ctor_get(x_15, 5);
lean_inc(x_257);
lean_dec(x_15);
x_258 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_258, 0, x_17);
x_259 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_260 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
x_261 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_262 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_263 = l_Lean_Syntax_inhabited;
x_264 = l_Option_get_x21___rarg___closed__3;
x_265 = lean_panic_fn(x_263, x_264);
x_266 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_265, x_262, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_271 = lean_ctor_get(x_257, 0);
lean_inc(x_271);
lean_dec(x_257);
x_272 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_271, x_262, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_271);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
}
}
default: 
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_234);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_306 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_307 = l_unreachable_x21___rarg(x_306);
x_308 = lean_apply_7(x_307, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_308;
}
}
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_309 = lean_ctor_get(x_9, 0);
x_310 = lean_ctor_get(x_9, 1);
x_311 = lean_ctor_get(x_9, 2);
x_312 = lean_ctor_get(x_9, 3);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_9);
x_313 = l_Lean_replaceRef(x_16, x_312);
lean_dec(x_16);
x_314 = l_Lean_replaceRef(x_313, x_312);
lean_dec(x_313);
x_315 = l_Lean_replaceRef(x_314, x_312);
lean_dec(x_312);
lean_dec(x_314);
x_316 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_316, 0, x_309);
lean_ctor_set(x_316, 1, x_310);
lean_ctor_set(x_316, 2, x_311);
lean_ctor_set(x_316, 3, x_315);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_317 = lean_ctor_get(x_15, 4);
lean_inc(x_317);
x_318 = l_Lean_Syntax_getArgs(x_317);
lean_dec(x_317);
lean_inc(x_15);
x_319 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__elabFieldTypeValue), 9, 1);
lean_closure_set(x_319, 0, x_15);
lean_inc(x_10);
lean_inc(x_316);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_320 = l_Lean_Elab_Term_elabBinders___rarg(x_318, x_319, x_5, x_6, x_7, x_8, x_316, x_10, x_11);
lean_dec(x_318);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_324 = lean_ctor_get(x_320, 1);
lean_inc(x_324);
lean_dec(x_320);
x_325 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__3;
x_326 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_325, x_5, x_6, x_7, x_8, x_316, x_10, x_324);
lean_dec(x_10);
lean_dec(x_316);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_320, 1);
lean_inc(x_327);
lean_dec(x_320);
x_328 = lean_ctor_get(x_323, 0);
lean_inc(x_328);
lean_dec(x_323);
lean_inc(x_10);
lean_inc(x_316);
lean_inc(x_8);
lean_inc(x_7);
x_329 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_328, x_5, x_6, x_7, x_8, x_316, x_10, x_327);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_inc(x_17);
x_333 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed), 15, 7);
lean_closure_set(x_333, 0, x_15);
lean_closure_set(x_333, 1, x_17);
lean_closure_set(x_333, 2, x_322);
lean_closure_set(x_333, 3, x_3);
lean_closure_set(x_333, 4, x_2);
lean_closure_set(x_333, 5, x_1);
lean_closure_set(x_333, 6, x_4);
x_334 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_17, x_332, x_330, x_333, x_5, x_6, x_7, x_8, x_316, x_10, x_331);
return x_334;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_316);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_335 = lean_ctor_get(x_329, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_329, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_337 = x_329;
} else {
 lean_dec_ref(x_329);
 x_337 = lean_box(0);
}
if (lean_is_scalar(x_337)) {
 x_338 = lean_alloc_ctor(1, 2, 0);
} else {
 x_338 = x_337;
}
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_336);
return x_338;
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; lean_object* x_344; 
x_339 = lean_ctor_get(x_320, 1);
lean_inc(x_339);
lean_dec(x_320);
x_340 = lean_ctor_get(x_321, 1);
lean_inc(x_340);
lean_dec(x_321);
x_341 = lean_ctor_get(x_322, 0);
lean_inc(x_341);
lean_dec(x_322);
x_342 = lean_ctor_get_uint8(x_15, sizeof(void*)*7);
lean_inc(x_17);
x_343 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed), 15, 7);
lean_closure_set(x_343, 0, x_15);
lean_closure_set(x_343, 1, x_17);
lean_closure_set(x_343, 2, x_340);
lean_closure_set(x_343, 3, x_3);
lean_closure_set(x_343, 4, x_2);
lean_closure_set(x_343, 5, x_1);
lean_closure_set(x_343, 6, x_4);
x_344 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_18__elabImplicitLambda___main___spec__1___rarg(x_17, x_342, x_341, x_343, x_5, x_6, x_7, x_8, x_316, x_10, x_339);
return x_344;
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_316);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_345 = lean_ctor_get(x_320, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_320, 1);
lean_inc(x_346);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_347 = x_320;
} else {
 lean_dec_ref(x_320);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(1, 2, 0);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_345);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
else
{
lean_object* x_349; lean_object* x_350; uint8_t x_351; 
x_349 = lean_ctor_get(x_19, 0);
lean_inc(x_349);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_350 = x_19;
} else {
 lean_dec_ref(x_19);
 x_350 = lean_box(0);
}
x_351 = lean_ctor_get_uint8(x_349, sizeof(void*)*4);
switch (x_351) {
case 0:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_352 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_352, 0, x_17);
x_353 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_354 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_352);
x_355 = l_Lean_Elab_throwAlreadyDeclaredUniverseLevel___rarg___closed__6;
x_356 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
x_357 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_356, x_5, x_6, x_7, x_8, x_316, x_10, x_11);
lean_dec(x_10);
lean_dec(x_316);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_357;
}
case 1:
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_15, 6);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_359 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_359, 0, x_17);
x_360 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_361 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
x_362 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__6;
x_363 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_363, 0, x_361);
lean_ctor_set(x_363, 1, x_362);
x_364 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_363, x_5, x_6, x_7, x_8, x_316, x_10, x_11);
lean_dec(x_10);
lean_dec(x_316);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_365 = lean_ctor_get(x_349, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_349, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_349, 2);
lean_inc(x_367);
x_368 = lean_ctor_get_uint8(x_349, sizeof(void*)*4 + 1);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_369 = x_349;
} else {
 lean_dec_ref(x_349);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_358, 0);
lean_inc(x_370);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_371 = x_358;
} else {
 lean_dec_ref(x_358);
 x_371 = lean_box(0);
}
x_394 = lean_ctor_get(x_15, 4);
lean_inc(x_394);
x_395 = l_Lean_Syntax_getArgs(x_394);
lean_dec(x_394);
x_396 = l_Array_isEmpty___rarg(x_395);
lean_dec(x_395);
if (x_396 == 0)
{
lean_object* x_397; 
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_350);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_397 = lean_box(0);
x_372 = x_397;
goto block_393;
}
else
{
lean_object* x_398; 
x_398 = lean_ctor_get(x_15, 5);
lean_inc(x_398);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; 
lean_dec(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_316);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_367);
x_399 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_367, x_5, x_6, x_7, x_8, x_316, x_10, x_11);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; 
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
if (lean_is_scalar(x_371)) {
 x_402 = lean_alloc_ctor(1, 1, 0);
} else {
 x_402 = x_371;
}
lean_ctor_set(x_402, 0, x_400);
x_403 = 1;
lean_inc(x_10);
lean_inc(x_316);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_404 = l_Lean_Elab_Term_elabTermEnsuringType(x_370, x_402, x_403, x_5, x_6, x_7, x_8, x_316, x_10, x_401);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
if (lean_is_scalar(x_350)) {
 x_407 = lean_alloc_ctor(1, 1, 0);
} else {
 x_407 = x_350;
}
lean_ctor_set(x_407, 0, x_405);
if (lean_is_scalar(x_369)) {
 x_408 = lean_alloc_ctor(0, 4, 2);
} else {
 x_408 = x_369;
}
lean_ctor_set(x_408, 0, x_365);
lean_ctor_set(x_408, 1, x_366);
lean_ctor_set(x_408, 2, x_367);
lean_ctor_set(x_408, 3, x_407);
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_351);
lean_ctor_set_uint8(x_408, sizeof(void*)*4 + 1, x_368);
x_409 = lean_array_push(x_3, x_408);
x_410 = lean_unsigned_to_nat(1u);
x_411 = lean_nat_add(x_2, x_410);
lean_dec(x_2);
x_2 = x_411;
x_3 = x_409;
x_9 = x_316;
x_11 = x_406;
goto _start;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_350);
lean_dec(x_316);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_413 = lean_ctor_get(x_404, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_404, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_415 = x_404;
} else {
 lean_dec_ref(x_404);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_414);
return x_416;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_350);
lean_dec(x_316);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_417 = lean_ctor_get(x_399, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_399, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_419 = x_399;
} else {
 lean_dec_ref(x_399);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
}
else
{
lean_object* x_421; 
lean_dec(x_398);
lean_dec(x_371);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_365);
lean_dec(x_350);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_421 = lean_box(0);
x_372 = x_421;
goto block_393;
}
}
block_393:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_372);
x_373 = lean_ctor_get(x_15, 5);
lean_inc(x_373);
lean_dec(x_15);
x_374 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_374, 0, x_17);
x_375 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__9;
x_376 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
x_377 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___closed__12;
x_378 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_379 = l_Lean_Syntax_inhabited;
x_380 = l_Option_get_x21___rarg___closed__3;
x_381 = lean_panic_fn(x_379, x_380);
x_382 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_381, x_378, x_5, x_6, x_7, x_8, x_316, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_381);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_382, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_385 = x_382;
} else {
 lean_dec_ref(x_382);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_384);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_387 = lean_ctor_get(x_373, 0);
lean_inc(x_387);
lean_dec(x_373);
x_388 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_387, x_378, x_5, x_6, x_7, x_8, x_316, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_387);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_391 = x_388;
} else {
 lean_dec_ref(x_388);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 2, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_389);
lean_ctor_set(x_392, 1, x_390);
return x_392;
}
}
}
}
default: 
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_422 = l_Lean_Elab_Term_getFVarLocalDecl_x21___closed__1;
x_423 = l_unreachable_x21___rarg(x_422);
x_424 = lean_apply_7(x_423, x_5, x_6, x_7, x_8, x_316, x_10, x_11);
return x_424;
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
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___main___rarg), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l___private_Lean_Elab_Structure_11__withFields___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_11__withFields___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_11__withFields(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_11__withFields___rarg), 11, 0);
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
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_whnf___at___private_Lean_Elab_Term_5__isTypeApp_x3f___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 3)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = l___private_Lean_Elab_Structure_12__getResultUniverse___closed__3;
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_12__getResultUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Structure_12__getResultUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_13__collectUsed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_1, x_2);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Meta_inferType___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_collectUsedFVars(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_21 = lean_ctor_get(x_15, 3);
lean_inc(x_21);
lean_dec(x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
lean_dec(x_2);
x_2 = x_24;
x_10 = x_22;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Lean_Elab_Term_collectUsedFVars(x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_2, x_30);
lean_dec(x_2);
x_2 = x_31;
x_10 = x_29;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_17);
if (x_33 == 0)
{
return x_17;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_17, 0);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_13__collectUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Array_forMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__2(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_13__collectUsed___spec__1(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_13__collectUsed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_13__collectUsed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_13__collectUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_13__collectUsed(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_14__removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l___private_Lean_Elab_Inductive_26__removeUnused___closed__1;
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_15 = l___private_Lean_Elab_Structure_13__collectUsed(x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_13, x_16);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Term_removeUnused(x_1, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_14__removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_14__removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_15__withUsed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l___private_Lean_Elab_Structure_14__removeUnused(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_apply_1(x_4, x_18);
x_20 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_16, x_17, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 0);
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_12);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_15__withUsed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_15__withUsed___rarg___boxed), 11, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_15__withUsed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_15__withUsed___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Structure_16__levelMVarToParamFVar___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_inc(x_13);
x_14 = lean_nat_dec_eq(x_11, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_7, 3);
lean_dec(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_7, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_11, x_20);
lean_dec(x_11);
lean_ctor_set(x_7, 1, x_21);
x_22 = l_Lean_Meta_inferTypeRef;
x_23 = lean_st_ref_get(x_22, x_9);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_apply_6(x_24, x_1, x_5, x_6, x_7, x_8, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_11, x_27);
lean_dec(x_11);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_10);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_12);
lean_ctor_set(x_29, 3, x_13);
x_30 = l_Lean_Meta_inferTypeRef;
x_31 = lean_st_ref_get(x_30, x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_32, x_1, x_5, x_6, x_29, x_8, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_35 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
x_36 = l_Lean_throwError___at_Lean_Meta_mkWHNFRef___spec__1___rarg(x_35, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_Structure_16__levelMVarToParamFVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Term_levelMVarToParam_x27(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Structure_16__levelMVarToParamFVar___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_Structure_16__levelMVarToParamFVar___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_16__levelMVarToParamFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_1, x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_16 = l___private_Lean_Elab_Structure_16__levelMVarToParamFVar(x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_2, x_18);
lean_dec(x_2);
x_2 = x_19;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParamFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamFVars___spec__1(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParamFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_17__levelMVarToParamFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_18__levelMVarToParamAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_13 = x_2;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_array_fget(x_2, x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_fset(x_2, x_1, x_16);
x_18 = x_15;
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 2);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_18, sizeof(void*)*4);
x_23 = lean_ctor_get_uint8(x_18, sizeof(void*)*4 + 1);
x_24 = lean_ctor_get(x_18, 3);
lean_inc(x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_21);
x_25 = l___private_Lean_Elab_Structure_16__levelMVarToParamFVar(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_25) == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_1, x_27);
x_29 = x_18;
x_30 = lean_array_fset(x_17, x_1, x_29);
lean_dec(x_1);
x_1 = x_28;
x_2 = x_30;
x_10 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_18);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_18, 3);
lean_dec(x_33);
x_34 = lean_ctor_get(x_18, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_18, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_18, 0);
lean_dec(x_36);
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = !lean_is_exclusive(x_24);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_4);
x_40 = l_Lean_Elab_Term_levelMVarToParam_x27(x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_ctor_set(x_24, 0, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_1, x_43);
x_45 = x_18;
x_46 = lean_array_fset(x_17, x_1, x_45);
lean_dec(x_1);
x_1 = x_44;
x_2 = x_46;
x_10 = x_42;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_24, 0);
lean_inc(x_48);
lean_dec(x_24);
lean_inc(x_4);
x_49 = l_Lean_Elab_Term_levelMVarToParam_x27(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_18, 3, x_52);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_1, x_53);
x_55 = x_18;
x_56 = lean_array_fset(x_17, x_1, x_55);
lean_dec(x_1);
x_1 = x_54;
x_2 = x_56;
x_10 = x_51;
goto _start;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_18);
x_58 = lean_ctor_get(x_25, 1);
lean_inc(x_58);
lean_dec(x_25);
x_59 = lean_ctor_get(x_24, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 x_60 = x_24;
} else {
 lean_dec_ref(x_24);
 x_60 = lean_box(0);
}
lean_inc(x_4);
x_61 = l_Lean_Elab_Term_levelMVarToParam_x27(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
if (lean_is_scalar(x_60)) {
 x_64 = lean_alloc_ctor(1, 1, 0);
} else {
 x_64 = x_60;
}
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(x_65, 0, x_19);
lean_ctor_set(x_65, 1, x_20);
lean_ctor_set(x_65, 2, x_21);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*4, x_22);
lean_ctor_set_uint8(x_65, sizeof(void*)*4 + 1, x_23);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_1, x_66);
x_68 = x_65;
x_69 = lean_array_fset(x_17, x_1, x_68);
lean_dec(x_1);
x_1 = x_67;
x_2 = x_69;
x_10 = x_63;
goto _start;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_25);
if (x_71 == 0)
{
return x_25;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_25, 0);
x_73 = lean_ctor_get(x_25, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_25);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_18__levelMVarToParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_13 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamFVars___spec__1(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
x_15 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_17__levelMVarToParamFVars___spec__1(x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = x_3;
x_18 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_18__levelMVarToParamAux___spec__1___boxed), 10, 2);
lean_closure_set(x_18, 0, x_12);
lean_closure_set(x_18, 1, x_17);
x_19 = x_18;
x_20 = lean_apply_8(x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_18__levelMVarToParamAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_umapMAux___main___at___private_Lean_Elab_Structure_18__levelMVarToParamAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_18__levelMVarToParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_18__levelMVarToParamAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_19__levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l___private_Lean_Elab_Structure_18__levelMVarToParamAux(x_1, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_13, x_17);
lean_dec(x_13);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_16);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_19__levelMVarToParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_19__levelMVarToParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_20__collectUniversesFromFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_4);
x_15 = lean_nat_dec_lt(x_5, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_array_fget(x_4, x_5);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_ctor_get(x_17, 2);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_21 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_24 = l___private_Lean_Meta_InferType_4__getLevelImp(x_22, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(x_25, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_2);
x_30 = l_Lean_Elab_Command_accLevelAtCtor___main(x_28, x_1, x_2, x_6);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_19);
lean_dec(x_2);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
x_5 = x_19;
x_6 = x_39;
x_13 = x_29;
goto _start;
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_24);
if (x_41 == 0)
{
return x_24;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_24, 0);
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_24);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_21);
if (x_45 == 0)
{
return x_21;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_21, 0);
x_47 = lean_ctor_get(x_21, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_21);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_20__collectUniversesFromFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_empty___closed__1;
x_13 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_20__collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_3, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_20__collectUniversesFromFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_20__collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Structure_20__collectUniversesFromFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_20__collectUniversesFromFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_assignLevelMVar___at___private_Lean_Elab_Structure_21__updateResultingUniverse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_st_ref_take(x_6, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_metavar_ctx_assign_level(x_14, x_1, x_2);
lean_ctor_set(x_11, 0, x_15);
x_16 = lean_st_ref_set(x_6, x_11, x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_26 = lean_metavar_ctx_assign_level(x_23, x_1, x_2);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_25);
x_28 = lean_st_ref_set(x_6, x_27, x_12);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
lean_object* _init_l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compute resulting universe level of structure, provide universe explicitly");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_21__updateResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l___private_Lean_Elab_Structure_12__getResultUniverse(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Level_getOffsetAux___main(x_11, x_13);
x_15 = l_Lean_Level_getLevelOffset___main(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 5)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_17 = l___private_Lean_Elab_Structure_20__collectUniversesFromFields(x_15, x_14, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Array_toList___rarg(x_18);
lean_dec(x_18);
x_21 = l_Lean_Level_mkNaryMax___main(x_20);
x_22 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Elab_Structure_21__updateResultingUniverse___spec__1(x_16, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_29 = l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__3;
x_30 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_29, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 0);
x_33 = lean_ctor_get(x_10, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_10);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Lean_Meta_assignLevelMVar___at___private_Lean_Elab_Structure_21__updateResultingUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_assignLevelMVar___at___private_Lean_Elab_Structure_21__updateResultingUniverse___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_21__updateResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_21__updateResultingUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_CollectLevelParams_main___main(x_15, x_1);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = l_Lean_CollectLevelParams_main___main(x_17, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_22__collectLevelParamsInFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Elab_Structure_22__collectLevelParamsInFVar(x_4, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_3 = x_17;
x_4 = x_19;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_23__collectLevelParamsInFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___spec__1(x_1, x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_23__collectLevelParamsInFVars(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_24__collectLevelParamsInStructure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_fget(x_2, x_3);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l___private_Lean_Elab_Structure_22__collectLevelParamsInFVar(x_4, x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_3 = x_17;
x_4 = x_20;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_24__collectLevelParamsInStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Elab_Inductive_29__collectLevelParamsInInductive___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___spec__1(x_1, x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_23__collectLevelParamsInFVars___spec__1(x_2, x_2, x_11, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_24__collectLevelParamsInStructure___spec__1(x_3, x_3, x_11, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_24__collectLevelParamsInStructure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_24__collectLevelParamsInStructure___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_24__collectLevelParamsInStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_24__collectLevelParamsInStructure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_25__addCtorFields___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
x_15 = l_Lean_Elab_Command_StructFieldInfo_inhabited;
x_16 = lean_array_get(x_15, x_1, x_14);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Elab_Term_getFVarLocalDecl_x21(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_mkOptionalNode___closed__2;
x_25 = lean_array_push(x_24, x_17);
x_26 = lean_expr_abstract(x_22, x_25);
lean_dec(x_25);
lean_dec(x_22);
x_27 = lean_ctor_get_uint8(x_16, sizeof(void*)*4);
lean_dec(x_16);
switch (x_27) {
case 0:
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_LocalDecl_userName(x_19);
x_29 = l_Lean_LocalDecl_binderInfo(x_19);
x_30 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
x_31 = l_Lean_mkForall(x_28, x_29, x_30, x_26);
x_2 = x_14;
x_3 = x_31;
x_10 = x_23;
goto _start;
}
case 1:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_LocalDecl_value(x_19);
lean_dec(x_19);
x_34 = lean_expr_instantiate1(x_26, x_33);
lean_dec(x_33);
lean_dec(x_26);
x_2 = x_14;
x_3 = x_34;
x_10 = x_23;
goto _start;
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = l_Lean_LocalDecl_userName(x_19);
x_37 = l_Lean_mkHole___closed__3;
x_38 = l_Lean_Name_appendBefore(x_36, x_37);
x_39 = l_Lean_LocalDecl_binderInfo(x_19);
x_40 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
x_41 = l_Lean_mkForall(x_38, x_39, x_40, x_26);
x_2 = x_14;
x_3 = x_41;
x_10 = x_23;
goto _start;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
return x_18;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
}
}
lean_object* l___private_Lean_Elab_Structure_25__addCtorFields___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_25__addCtorFields___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_25__addCtorFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_25__addCtorFields___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_25__addCtorFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Structure_25__addCtorFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Structure_26__mkCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
x_14 = l_List_map___main___at_Lean_Meta_addGlobalInstanceImp___spec__1(x_2);
x_15 = l_Lean_mkConst(x_13, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_3, x_3, x_16, x_15);
x_18 = lean_array_get_size(x_4);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_9, 3);
x_21 = l_Lean_replaceRef(x_12, x_20);
lean_dec(x_12);
x_22 = l_Lean_replaceRef(x_21, x_20);
lean_dec(x_21);
x_23 = l_Lean_replaceRef(x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
lean_ctor_set(x_9, 3, x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_24 = l___private_Lean_Elab_Structure_25__addCtorFields___main(x_4, x_18, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_7);
lean_inc(x_3);
x_27 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_3, x_25, x_5, x_6, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_array_get_size(x_3);
lean_dec(x_3);
x_34 = lean_ctor_get(x_1, 9);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get_uint8(x_34, sizeof(void*)*4);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_34, 3);
lean_inc(x_36);
lean_dec(x_34);
x_37 = 1;
x_38 = l_Lean_Expr_inferImplicit___main(x_32, x_33, x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_34, 3);
lean_inc(x_40);
lean_dec(x_34);
x_41 = 0;
x_42 = l_Lean_Expr_inferImplicit___main(x_32, x_33, x_41);
lean_dec(x_33);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_30, 0, x_43);
return x_30;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_array_get_size(x_3);
lean_dec(x_3);
x_47 = lean_ctor_get(x_1, 9);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_47, 3);
lean_inc(x_49);
lean_dec(x_47);
x_50 = 1;
x_51 = l_Lean_Expr_inferImplicit___main(x_44, x_46, x_50);
lean_dec(x_46);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_45);
return x_53;
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_47, 3);
lean_inc(x_54);
lean_dec(x_47);
x_55 = 0;
x_56 = l_Lean_Expr_inferImplicit___main(x_44, x_46, x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_45);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_27);
if (x_59 == 0)
{
return x_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_27, 0);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_27);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_24);
if (x_63 == 0)
{
return x_24;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_24, 0);
x_65 = lean_ctor_get(x_24, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_24);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_9, 0);
x_68 = lean_ctor_get(x_9, 1);
x_69 = lean_ctor_get(x_9, 2);
x_70 = lean_ctor_get(x_9, 3);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_9);
x_71 = l_Lean_replaceRef(x_12, x_70);
lean_dec(x_12);
x_72 = l_Lean_replaceRef(x_71, x_70);
lean_dec(x_71);
x_73 = l_Lean_replaceRef(x_72, x_70);
lean_dec(x_70);
lean_dec(x_72);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_68);
lean_ctor_set(x_74, 2, x_69);
lean_ctor_set(x_74, 3, x_73);
lean_inc(x_10);
lean_inc(x_74);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_75 = l___private_Lean_Elab_Structure_25__addCtorFields___main(x_4, x_18, x_17, x_5, x_6, x_7, x_8, x_74, x_10, x_11);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_7);
lean_inc(x_3);
x_78 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_3, x_76, x_5, x_6, x_7, x_8, x_74, x_10, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_79, x_5, x_6, x_7, x_8, x_74, x_10, x_80);
lean_dec(x_10);
lean_dec(x_74);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
lean_object* l___private_Lean_Elab_Structure_26__mkCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Structure_26__mkCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
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
lean_object* l___private_Lean_Elab_Structure_28__addProjections(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_st_ref_get(x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_mk_projections(x_14, x_1, x_2, x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_4);
return x_21;
}
}
}
lean_object* l___private_Lean_Elab_Structure_28__addProjections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_Structure_28__addProjections(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Structure_29__mkAuxConstructions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
lean_inc(x_13);
x_15 = l_Lean_Environment_contains(x_13, x_14);
x_16 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_13);
x_17 = l_Lean_Environment_contains(x_13, x_16);
x_18 = l_Lean_Expr_heq_x3f___closed__2;
x_19 = l_Lean_Environment_contains(x_13, x_18);
x_52 = lean_st_ref_take(x_7, x_11);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_mk_rec_on(x_56, x_1);
lean_ctor_set(x_53, 0, x_57);
x_58 = lean_st_ref_set(x_7, x_53, x_54);
if (x_15 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_20 = x_59;
goto block_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_st_ref_take(x_7, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_62, 0);
x_66 = lean_mk_cases_on(x_65, x_1);
lean_ctor_set(x_62, 0, x_66);
x_67 = lean_st_ref_set(x_7, x_62, x_63);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_20 = x_68;
goto block_51;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_62, 0);
x_70 = lean_ctor_get(x_62, 1);
x_71 = lean_ctor_get(x_62, 2);
x_72 = lean_ctor_get(x_62, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_62);
x_73 = lean_mk_cases_on(x_69, x_1);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_70);
lean_ctor_set(x_74, 2, x_71);
lean_ctor_set(x_74, 3, x_72);
x_75 = lean_st_ref_set(x_7, x_74, x_63);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_20 = x_76;
goto block_51;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_53, 0);
x_78 = lean_ctor_get(x_53, 1);
x_79 = lean_ctor_get(x_53, 2);
x_80 = lean_ctor_get(x_53, 3);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_53);
x_81 = lean_mk_rec_on(x_77, x_1);
x_82 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
lean_ctor_set(x_82, 2, x_79);
lean_ctor_set(x_82, 3, x_80);
x_83 = lean_st_ref_set(x_7, x_82, x_54);
if (x_15 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_20 = x_84;
goto block_51;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_st_ref_take(x_7, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 3);
lean_inc(x_92);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 lean_ctor_release(x_87, 2);
 lean_ctor_release(x_87, 3);
 x_93 = x_87;
} else {
 lean_dec_ref(x_87);
 x_93 = lean_box(0);
}
x_94 = lean_mk_cases_on(x_89, x_1);
if (lean_is_scalar(x_93)) {
 x_95 = lean_alloc_ctor(0, 4, 0);
} else {
 x_95 = x_93;
}
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_90);
lean_ctor_set(x_95, 2, x_91);
lean_ctor_set(x_95, 3, x_92);
x_96 = lean_st_ref_set(x_7, x_95, x_88);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_20 = x_97;
goto block_51;
}
}
block_51:
{
if (x_15 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_12;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
if (x_17 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_12;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
if (x_19 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_12;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_12);
x_27 = lean_st_ref_take(x_7, x_20);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_mk_no_confusion(x_31, x_1);
lean_ctor_set(x_28, 0, x_32);
x_33 = lean_st_ref_set(x_7, x_28, x_29);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 1);
x_42 = lean_ctor_get(x_28, 2);
x_43 = lean_ctor_get(x_28, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_44 = lean_mk_no_confusion(x_40, x_1);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
x_46 = lean_st_ref_set(x_7, x_45, x_29);
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
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_29__mkAuxConstructions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Structure_29__mkAuxConstructions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_mkId___at___private_Lean_Elab_Structure_30__addDefaults___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_1__mkIdImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* _init_l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Basic_1__regTraceClasses___closed__2;
x_2 = l_Lean_Elab_logDbgTrace___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp___lambda__1___boxed), 4, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
x_13 = l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2___closed__1;
x_14 = l_Lean_MonadTracer_trace___at_Lean_Meta_isLevelDefEq___spec__2(x_13, x_12, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Meta_Closure_1__mkAuxDefinitionImp(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_15);
return x_16;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_fget(x_1, x_2);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l___private_Lean_Meta_AppBuilder_1__mkIdImp(x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_23 = l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2(x_16, x_17, x_20, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_take(x_8, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = 0;
x_31 = lean_set_reducibility_status(x_29, x_16, x_30);
lean_ctor_set(x_26, 0, x_31);
x_32 = lean_st_ref_set(x_8, x_26, x_27);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
lean_dec(x_2);
x_2 = x_35;
x_9 = x_33;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
x_39 = lean_ctor_get(x_26, 2);
x_40 = lean_ctor_get(x_26, 3);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_41 = 0;
x_42 = lean_set_reducibility_status(x_37, x_16, x_41);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
lean_ctor_set(x_43, 2, x_39);
lean_ctor_set(x_43, 3, x_40);
x_44 = lean_st_ref_set(x_8, x_43, x_27);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_2, x_46);
lean_dec(x_2);
x_2 = x_47;
x_9 = x_45;
goto _start;
}
}
else
{
uint8_t x_49; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_23);
if (x_49 == 0)
{
return x_23;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_23, 0);
x_51 = lean_ctor_get(x_23, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_23);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_19, 0);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_19);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_30__addDefaults(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Meta_getLocalInstances___at_Lean_Elab_Term_removeUnused___spec__1___rarg(x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__3___boxed), 9, 2);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_13);
x_15 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_1, x_11, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_15;
}
}
lean_object* l_Lean_Meta_mkId___at___private_Lean_Elab_Structure_30__addDefaults___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkId___at___private_Lean_Elab_Structure_30__addDefaults___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_30__addDefaults___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__2(lean_object* x_1) {
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
x_9 = l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__2(x_5);
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
x_15 = l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__2(x_11);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_Array_filterMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_array_fget(x_1, x_2);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Elab_Term_getFVarLocalDecl_x21(x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_Elab_Command_StructFieldInfo_isSubobject(x_31);
lean_dec(x_31);
if (x_36 == 0)
{
uint8_t x_37; 
lean_dec(x_34);
x_37 = 0;
x_15 = x_37;
x_16 = x_35;
goto block_30;
}
else
{
uint8_t x_38; uint8_t x_39; 
x_38 = l_Lean_LocalDecl_binderInfo(x_34);
lean_dec(x_34);
x_39 = l_Lean_BinderInfo_isInstImplicit(x_38);
x_15 = x_39;
x_16 = x_35;
goto block_30;
}
}
else
{
uint8_t x_40; 
lean_dec(x_31);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
return x_33;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_33, 0);
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_33);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
block_30:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_2 = x_18;
x_10 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_lt(x_3, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
lean_dec(x_2);
x_23 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_2 = x_22;
x_3 = x_23;
x_10 = x_16;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_array_fswap(x_1, x_2, x_3);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_2, x_26);
lean_dec(x_2);
x_28 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_1 = x_25;
x_2 = x_27;
x_3 = x_28;
x_10 = x_16;
goto _start;
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__4(lean_object* x_1) {
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
x_7 = l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__4(x_5);
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
x_11 = l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__4(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_addGlobalInstance___at___private_Lean_Elab_Structure_31__elabStructureView___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_6, 3);
x_14 = lean_add_instance(x_12, x_1, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_setEnv___at_Lean_Elab_Term_declareTacticSyntax___spec__3(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_io_error_to_string(x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_io_error_to_string(x_24);
x_27 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_13);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Meta_addGlobalInstance___at___private_Lean_Elab_Structure_31__elabStructureView___spec__5(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_1 = x_12;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
}
lean_object* l_Array_filterAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_default");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = x_2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_fget(x_2, x_1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_fset(x_2, x_1, x_15);
x_17 = x_14;
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_inferType___at_Lean_Elab_Term_throwTypeMismatchError___spec__2(x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
x_23 = l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__2;
x_24 = l_Lean_Name_append___main(x_22, x_23);
lean_dec(x_22);
x_25 = lean_ctor_get(x_17, 3);
lean_inc(x_25);
lean_dec(x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = l_Lean_Expr_Inhabited;
x_27 = l_Option_get_x21___rarg___closed__3;
x_28 = lean_panic_fn(x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_1, x_31);
x_33 = x_30;
x_34 = lean_array_fset(x_16, x_1, x_33);
lean_dec(x_1);
x_1 = x_32;
x_2 = x_34;
x_9 = x_21;
goto _start;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_25, 0);
lean_inc(x_36);
lean_dec(x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_1, x_39);
x_41 = x_38;
x_42 = lean_array_fset(x_16, x_1, x_41);
lean_dec(x_1);
x_1 = x_40;
x_2 = x_42;
x_9 = x_21;
goto _start;
}
}
else
{
uint8_t x_44; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_19, 0);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_19);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l___private_Lean_Elab_Structure_19__levelMVarToParam(x_6, x_1, x_2, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
if (x_4 == 0)
{
x_17 = x_5;
x_18 = x_16;
goto block_125;
}
else
{
lean_object* x_126; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_126 = l___private_Lean_Elab_Structure_21__updateResultingUniverse(x_15, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_17 = x_127;
x_18 = x_128;
goto block_125;
}
else
{
uint8_t x_129; 
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
return x_126;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_126);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
block_125:
{
lean_object* x_19; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_19 = l___private_Lean_Elab_Structure_24__collectLevelParamsInStructure(x_6, x_1, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_3, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 3);
lean_inc(x_23);
x_24 = l_Lean_Elab_sortDeclLevelParams(x_22, x_23, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_unsigned_to_nat(0u);
lean_inc(x_6);
x_31 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_1, x_1, x_30, x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_3);
x_32 = l___private_Lean_Elab_Structure_26__mkCtor(x_3, x_29, x_31, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_31);
x_35 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_31, x_17, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_instantiateMVars___at_Lean_Elab_Term_MVarErrorContext_logError___spec__1(x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_3, 4);
lean_inc(x_41);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_41);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_array_get_size(x_31);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*2 + 3);
x_49 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_49, 0, x_29);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*3, x_48);
lean_inc(x_49);
x_50 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_49, x_7, x_8, x_9, x_10, x_11, x_12, x_40);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
lean_inc(x_11);
lean_inc(x_7);
x_52 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_49, x_7, x_8, x_9, x_10, x_11, x_12, x_51);
lean_dec(x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
lean_inc(x_15);
x_54 = l_Array_filterAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__1(x_15, x_30, x_30);
x_55 = l_Array_toList___rarg(x_54);
lean_dec(x_54);
x_56 = l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__2(x_55);
x_57 = lean_ctor_get_uint8(x_3, sizeof(void*)*11);
lean_inc(x_7);
x_58 = l___private_Lean_Elab_Structure_28__addProjections(x_41, x_56, x_57, x_7, x_8, x_9, x_10, x_11, x_12, x_53);
lean_dec(x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l___private_Lean_Elab_Structure_29__mkAuxConstructions(x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_59);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_15);
x_62 = l_Array_filterMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__3(x_15, x_30, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Array_toList___rarg(x_63);
lean_dec(x_63);
x_66 = l_List_map___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__4(x_65);
x_67 = lean_ctor_get(x_47, 1);
lean_inc(x_67);
lean_dec(x_47);
x_68 = 0;
x_69 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_7);
x_70 = l_Lean_Elab_Term_applyAttributesAt(x_41, x_67, x_68, x_69, x_7, x_8, x_9, x_10, x_11, x_12, x_64);
lean_dec(x_67);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_List_forM___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__6(x_66, x_7, x_8, x_9, x_10, x_11, x_12, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
lean_inc(x_15);
x_75 = l_Array_filterAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__7(x_15, x_30, x_30);
x_76 = x_75;
x_77 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___boxed), 9, 2);
lean_closure_set(x_77, 0, x_30);
lean_closure_set(x_77, 1, x_76);
x_78 = x_77;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_79 = lean_apply_7(x_78, x_7, x_8, x_9, x_10, x_11, x_12, x_73);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__9(x_3, x_6, x_31, x_30, x_74);
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_3);
x_83 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__10(x_15, x_15, x_30, x_82);
lean_dec(x_15);
x_84 = l___private_Lean_Elab_Structure_30__addDefaults(x_83, x_80, x_7, x_8, x_9, x_10, x_11, x_12, x_81);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_74);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_79);
if (x_85 == 0)
{
return x_79;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_79, 0);
x_87 = lean_ctor_get(x_79, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_79);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_72);
if (x_89 == 0)
{
return x_72;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_72, 0);
x_91 = lean_ctor_get(x_72, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_72);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_66);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_70);
if (x_93 == 0)
{
return x_70;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_70, 0);
x_95 = lean_ctor_get(x_70, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_70);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_62);
if (x_97 == 0)
{
return x_62;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_62, 0);
x_99 = lean_ctor_get(x_62, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_62);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_101 = !lean_is_exclusive(x_58);
if (x_101 == 0)
{
return x_58;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_58, 0);
x_103 = lean_ctor_get(x_58, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_58);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_105 = !lean_is_exclusive(x_52);
if (x_105 == 0)
{
return x_52;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_52, 0);
x_107 = lean_ctor_get(x_52, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_52);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_41);
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_109 = !lean_is_exclusive(x_50);
if (x_109 == 0)
{
return x_50;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_50, 0);
x_111 = lean_ctor_get(x_50, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_50);
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
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_35);
if (x_113 == 0)
{
return x_35;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_35, 0);
x_115 = lean_ctor_get(x_35, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_35);
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
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_117 = !lean_is_exclusive(x_32);
if (x_117 == 0)
{
return x_32;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_32, 0);
x_119 = lean_ctor_get(x_32, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_32);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_121 = !lean_is_exclusive(x_19);
if (x_121 == 0)
{
return x_19;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_19, 0);
x_123 = lean_ctor_get(x_19, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_19);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_133 = !lean_is_exclusive(x_14);
if (x_133 == 0)
{
return x_14;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_14, 0);
x_135 = lean_ctor_get(x_14, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_14);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_16 = l___private_Lean_Elab_Structure_12__getResultUniverse(x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_5);
x_19 = l_Lean_Elab_Command_shouldInferResultUniverse(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 5);
lean_inc(x_22);
lean_inc(x_4);
lean_inc(x_3);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_31__elabStructureView___lambda__1___boxed), 13, 5);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_4);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_20);
lean_closure_set(x_23, 4, x_1);
x_24 = l___private_Lean_Elab_Structure_15__withUsed___rarg(x_22, x_3, x_4, x_23, x_5, x_6, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
return x_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_14, 0);
x_35 = lean_ctor_get(x_14, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_14);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 10);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_31__elabStructureView___lambda__2), 11, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Elab_Structure_11__withFields___main___rarg(x_12, x_14, x_4, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_31__elabStructureView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected Type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_31__elabStructureView___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_31__elabStructureView___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_31__elabStructureView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_31__elabStructureView___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 6);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 8);
lean_inc(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_10);
x_11 = l_Lean_Elab_Term_elabType(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_37; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_37 = l___private_Lean_Elab_Structure_4__validStructType(x_12);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_1);
x_38 = l___private_Lean_Elab_Structure_31__elabStructureView___closed__3;
x_39 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_19__elabTermAux___main___spec__1___rarg(x_10, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_10);
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
lean_dec(x_10);
x_14 = x_13;
goto block_36;
}
block_36:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_31__elabStructureView___lambda__3), 11, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_12);
lean_closure_set(x_16, 2, x_9);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_6, 3);
x_19 = l_Lean_replaceRef(x_15, x_18);
lean_dec(x_15);
x_20 = l_Lean_replaceRef(x_19, x_18);
lean_dec(x_19);
x_21 = l_Lean_replaceRef(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
lean_ctor_set(x_6, 3, x_21);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_empty___closed__1;
x_24 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_1, x_22, x_23, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_6, 0);
x_26 = lean_ctor_get(x_6, 1);
x_27 = lean_ctor_get(x_6, 2);
x_28 = lean_ctor_get(x_6, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_6);
x_29 = l_Lean_replaceRef(x_15, x_28);
lean_dec(x_15);
x_30 = l_Lean_replaceRef(x_29, x_28);
lean_dec(x_29);
x_31 = l_Lean_replaceRef(x_30, x_28);
lean_dec(x_28);
lean_dec(x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_26);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Array_empty___closed__1;
x_35 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_1, x_33, x_34, x_16, x_2, x_3, x_4, x_5, x_32, x_7, x_14);
return x_35;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_11);
if (x_44 == 0)
{
return x_11;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_11, 0);
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_11);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l_Lean_Meta_addGlobalInstance___at___private_Lean_Elab_Structure_31__elabStructureView___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_addGlobalInstance___at___private_Lean_Elab_Structure_31__elabStructureView___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__9(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Structure_31__elabStructureView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_Structure_31__elabStructureView___lambda__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 11, 1);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_2);
lean_ctor_set(x_20, 2, x_3);
lean_ctor_set(x_20, 3, x_4);
lean_ctor_set(x_20, 4, x_6);
lean_ctor_set(x_20, 5, x_7);
lean_ctor_set(x_20, 6, x_12);
lean_ctor_set(x_20, 7, x_8);
lean_ctor_set(x_20, 8, x_9);
lean_ctor_set(x_20, 9, x_10);
lean_ctor_set(x_20, 10, x_11);
lean_ctor_set_uint8(x_20, sizeof(void*)*11, x_5);
x_21 = l___private_Lean_Elab_Structure_31__elabStructureView(x_20, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_Elab_Term_resetMessageLog(x_13, x_14, x_15, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(x_5);
lean_inc(x_4);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__1___boxed), 19, 11);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_22);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_12);
lean_closure_set(x_23, 7, x_7);
lean_closure_set(x_23, 8, x_8);
lean_closure_set(x_23, 9, x_9);
lean_closure_set(x_23, 10, x_10);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_24, 0, x_11);
lean_closure_set(x_24, 1, x_23);
x_25 = l_Lean_Elab_Term_withLevelNames___rarg(x_4, x_24, x_13, x_14, x_15, x_16, x_17, x_18, x_21);
return x_25;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("classTk");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_elabModifiers___rarg___lambda__3___closed__2;
x_2 = l_Lean_Elab_Command_elabStructure___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Type");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SourceInfo_inhabited___closed__1;
x_2 = l_Lean_Elab_Command_elabStructure___closed__3;
x_3 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_elabStructure___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Level_elabLevel___main___closed__6;
x_2 = l_Lean_myMacro____x40_Lean_Util_Trace___hyg_45____closed__11;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_empty___closed__1;
x_2 = l_Lean_Elab_Command_elabStructure___closed__6;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_nullKind___closed__2;
x_2 = l_Lean_Elab_Command_elabStructure___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_elabStructure___closed__5;
x_2 = l_Lean_Elab_Command_elabStructure___closed__8;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_elabTypeStx___closed__2;
x_2 = l_Lean_Elab_Command_elabStructure___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_elabStructure___closed__11() {
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
x_11 = l_Lean_Elab_Command_elabStructure___closed__2;
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
goto block_78;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = l_Lean_Elab_Command_elabStructure___closed__11;
x_80 = l_Lean_Elab_Modifiers_addAttribute(x_1, x_79);
x_24 = x_80;
goto block_78;
}
block_78:
{
lean_object* x_25; 
if (x_20 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = l_Lean_Syntax_getArg(x_19, x_8);
lean_dec(x_19);
x_73 = l_Lean_Syntax_getArg(x_72, x_13);
lean_dec(x_72);
x_74 = l_Lean_Syntax_getArgs(x_73);
lean_dec(x_73);
x_75 = l_Array_empty___closed__1;
x_76 = l_Array_foldlStepMAux___main___at_Lean_Elab_expandDeclId___spec__1(x_15, x_74, x_8, x_75);
lean_dec(x_74);
x_25 = x_76;
goto block_71;
}
else
{
lean_object* x_77; 
lean_dec(x_19);
x_77 = l_Array_empty___closed__1;
x_25 = x_77;
goto block_71;
}
block_71:
{
lean_object* x_26; lean_object* x_27; 
if (x_23 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Lean_Syntax_getArg(x_22, x_8);
lean_dec(x_22);
x_65 = l_Lean_Syntax_getArg(x_64, x_13);
lean_dec(x_64);
x_26 = x_65;
x_27 = x_7;
goto block_63;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_22);
x_66 = l_Lean_Elab_Command_getCurrMacroScope(x_3, x_4, x_7);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Elab_Command_getMainModule___rarg(x_4, x_67);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Elab_Command_elabStructure___closed__10;
x_26 = x_70;
x_27 = x_69;
goto block_63;
}
block_63:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_Elab_Command_getLevelNames___rarg(x_4, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_3);
x_31 = l_Lean_Elab_Command_expandDeclId(x_14, x_24, x_3, x_4, x_30);
lean_dec(x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 2);
lean_inc(x_35);
lean_dec(x_32);
lean_inc(x_3);
lean_inc(x_2);
x_36 = l___private_Lean_Elab_Structure_2__expandCtor(x_2, x_24, x_34, x_3, x_4, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l___private_Lean_Elab_Structure_3__expandFields(x_2, x_24, x_34, x_3, x_4, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_34);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_34);
x_43 = lean_st_ref_get(x_4, x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l___private_Lean_Elab_Command_4__getVarDecls(x_44);
lean_dec(x_44);
x_47 = lean_box(x_12);
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__2___boxed), 19, 11);
lean_closure_set(x_48, 0, x_2);
lean_closure_set(x_48, 1, x_24);
lean_closure_set(x_48, 2, x_29);
lean_closure_set(x_48, 3, x_35);
lean_closure_set(x_48, 4, x_47);
lean_closure_set(x_48, 5, x_34);
lean_closure_set(x_48, 6, x_25);
lean_closure_set(x_48, 7, x_26);
lean_closure_set(x_48, 8, x_37);
lean_closure_set(x_48, 9, x_40);
lean_closure_set(x_48, 10, x_17);
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg___boxed), 9, 2);
lean_closure_set(x_49, 0, x_46);
lean_closure_set(x_49, 1, x_48);
x_50 = l_Lean_Elab_Command_liftTermElabM___rarg(x_42, x_49, x_3, x_4, x_45);
return x_50;
}
else
{
uint8_t x_51; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_39, 0);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_39);
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
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_36);
if (x_55 == 0)
{
return x_36;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_36, 0);
x_57 = lean_ctor_get(x_36, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_36);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_17);
lean_dec(x_3);
lean_dec(x_2);
x_59 = !lean_is_exclusive(x_31);
if (x_59 == 0)
{
return x_31;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_31, 0);
x_61 = lean_ctor_get(x_31, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_31);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_6);
if (x_81 == 0)
{
return x_6;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_6, 0);
x_83 = lean_ctor_get(x_6, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_6);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = l_Lean_Elab_Command_elabStructure___lambda__1(x_1, x_2, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = l_Lean_Elab_Command_elabStructure___lambda__2(x_1, x_2, x_3, x_4, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_21;
}
}
lean_object* l_Lean_Elab_Command_elabStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_elabStructure(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Closure(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_DeclModifiers(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
lean_object* initialize_Lean_Elab_Inductive(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Structure(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Closure(lean_io_mk_world());
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
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__1 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__1();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__1);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__2 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__2();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__2);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__3 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__3();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__3);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__4 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__4();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__4);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__5 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__5();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__5);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__6 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__6();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__6);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__7 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__7();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__7);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__8 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__8();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__8);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__9 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__9();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__9);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__10 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__10();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__10);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__11 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__11();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__11);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__12 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__12();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__12);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__13 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__13();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__13);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__14 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__14();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__14);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__15 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__15();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__15);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__16 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__16();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__16);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__17 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__17();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__17);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__18 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__18();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__18);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__19 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__19();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__19);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__20 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__20();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__20);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__21 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__21();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__21);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__22 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__22();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__22);
l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__23 = _init_l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__23();
lean_mark_persistent(l_Lean_Elab_elabModifiers___at___private_Lean_Elab_Structure_2__expandCtor___spec__1___closed__23);
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
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__10 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__10();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__10);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__11 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__11();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__11);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__12 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__12();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__12);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__13 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__13();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__13);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__14 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__14();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__14);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__15 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__15();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__15);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__16 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__16();
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
l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__1);
l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__2);
l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__3 = _init_l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_21__updateResultingUniverse___closed__3);
l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2___closed__1 = _init_l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxDefinition___at___private_Lean_Elab_Structure_30__addDefaults___spec__2___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__1 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__1);
l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__2 = _init_l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_31__elabStructureView___spec__8___closed__2);
l___private_Lean_Elab_Structure_31__elabStructureView___closed__1 = _init_l___private_Lean_Elab_Structure_31__elabStructureView___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_31__elabStructureView___closed__1);
l___private_Lean_Elab_Structure_31__elabStructureView___closed__2 = _init_l___private_Lean_Elab_Structure_31__elabStructureView___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_31__elabStructureView___closed__2);
l___private_Lean_Elab_Structure_31__elabStructureView___closed__3 = _init_l___private_Lean_Elab_Structure_31__elabStructureView___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_31__elabStructureView___closed__3);
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
l_Lean_Elab_Command_elabStructure___closed__9 = _init_l_Lean_Elab_Command_elabStructure___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__9);
l_Lean_Elab_Command_elabStructure___closed__10 = _init_l_Lean_Elab_Command_elabStructure___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__10);
l_Lean_Elab_Command_elabStructure___closed__11 = _init_l_Lean_Elab_Command_elabStructure___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_elabStructure___closed__11);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
