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
lean_object* l_Lean_Elab_Term_getEnv___rarg(lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandOptDeclSig(lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__1;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__3;
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__4;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__2;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__14;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__5;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9;
extern lean_object* l_Option_get_x21___rarg___closed__3;
lean_object* l_Lean_Syntax_getIdAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__3;
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_withDeclId___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_12__removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Structure_14__levelMVarToParamFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Structure_3__expandFields(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isInternalSubobjectFieldName(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__7;
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse___closed__3;
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLetDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structExplicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_applyVisibility(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_4__validStructType___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__8;
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__4;
lean_object* l_Lean_Elab_Term_ensureHasType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__4;
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__2;
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1;
lean_object* l_Lean_Elab_Command_mkDeclName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__12;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__5;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__10;
lean_object* l___private_Lean_Elab_Structure_9__withParents(lean_object*);
uint8_t l___private_Lean_Elab_Structure_7__containsFieldName(lean_object*, lean_object*);
lean_object* l_Lean_Level_getLevelOffset___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_13__withUsed(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields(lean_object*);
lean_object* l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_type___elambda__1___closed__5;
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_13__withUsed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getStructureFieldsFlattened(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
lean_object* l_Lean_Elab_Command_elabStructure___closed__8;
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse___closed__1;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__15;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__4;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6;
lean_object* l_Lean_Elab_Command_elabStructure___closed__4;
lean_object* l_Lean_Elab_Term_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__2;
lean_object* l___private_Lean_Elab_Structure_1__defaultCtorName;
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l___private_Lean_Elab_Structure_14__levelMVarToParamFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3;
lean_object* l_Lean_Elab_Command_elabStructure___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse___closed__2;
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l_Lean_Level_getOffsetAux___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__5;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main(lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_13__withUsed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__9;
uint8_t l___private_Lean_Elab_Structure_4__validStructType(lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__3;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__5;
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerClassAttr___closed__2;
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__11;
extern lean_object* l___private_Lean_Elab_Quotation_5__explodeHeadPat___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__5;
extern lean_object* l_Lean_nullKind___closed__2;
lean_object* l___private_Lean_Elab_Structure_2__expandCtor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__3;
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__10;
extern lean_object* l_Lean_Parser_Level_hole___elambda__1___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_inhabited;
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__2;
lean_object* l_Lean_Elab_Command_elabStructure___closed__6;
lean_object* l___private_Lean_Elab_Structure_3__expandFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2;
lean_object* l___private_Lean_Elab_Command_7__mkTermState(lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__7;
lean_object* l_Lean_Elab_Command_getCurrMacroScope(lean_object*, lean_object*);
extern lean_object* l_Lean_SourceInfo_inhabited___closed__1;
lean_object* l_Lean_Elab_Command_getMainModule(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__2;
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__8;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1;
lean_object* l_Lean_Elab_Command_elabStructure___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__4;
lean_object* l_Lean_Elab_Command_elabStructure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Modifiers_addAttribute(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_structInstBinder___elambda__1___closed__2;
lean_object* l_Lean_Elab_expandDeclSig(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__2;
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__11;
lean_object* l_Lean_Elab_Term_elabType(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__6;
lean_object* l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_9__getVarDecls(lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
extern lean_object* l_Lean_prodToExpr___rarg___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Structure_6__findFieldInfo_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getLevelNames(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabModifiers(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__1;
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Elab_Command_CtorView_inhabited___closed__1;
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__13;
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__1;
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_Modifiers_isPrivate(lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields(lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3;
lean_object* l___private_Lean_Elab_Structure_12__removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___closed__7;
lean_object* l_Lean_Level_mkNaryMax___main(lean_object*);
lean_object* l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__2;
extern lean_object* l_Lean_Parser_Command_structImplicitBinder___elambda__1___closed__2;
lean_object* l_Lean_Meta_mkProjection___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_7__containsFieldName___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidFieldModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___closed__3;
lean_object* l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Command_classTk___elambda__1___closed__2;
lean_object* l_Lean_Elab_Command_checkValidFieldModifier___closed__6;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__5;
uint8_t lean_is_class(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___closed__1;
lean_object* l___private_Lean_Elab_Structure_18__collectUniversesFromFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Structure_18__collectUniversesFromFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkProjection___main___closed__3;
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
lean_object* l___private_Lean_Elab_Structure_2__expandCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(6u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = l_Lean_Syntax_isNone(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_Syntax_getArg(x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_Syntax_getArg(x_9, x_8);
lean_inc(x_3);
x_11 = l_Lean_Elab_Command_elabModifiers(x_10, x_3, x_4);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(2u);
x_15 = l_Lean_Syntax_getArg(x_9, x_14);
x_16 = l_Lean_Syntax_isNone(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getIdAt(x_9, x_17);
lean_inc(x_18);
x_19 = l_Lean_Name_append___main(x_2, x_18);
x_20 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
lean_inc(x_3);
x_21 = l_Lean_Elab_Command_checkValidCtorModifier(x_9, x_12, x_3, x_13);
if (x_16 == 0)
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Elab_Command_applyVisibility(x_9, x_20, x_19, x_3, x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = 1;
x_27 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_27, 0, x_9);
lean_ctor_set(x_27, 1, x_12);
lean_ctor_set(x_27, 2, x_18);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
x_30 = 1;
x_31 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_12);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*4, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_dec(x_21);
x_42 = l_Lean_Elab_Command_applyVisibility(x_9, x_20, x_19, x_3, x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = 0;
x_46 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_46, 0, x_9);
lean_ctor_set(x_46, 1, x_12);
lean_ctor_set(x_46, 2, x_18);
lean_ctor_set(x_46, 3, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_45);
lean_ctor_set(x_42, 0, x_46);
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = 0;
x_50 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_50, 0, x_9);
lean_ctor_set(x_50, 1, x_12);
lean_ctor_set(x_50, 2, x_18);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set_uint8(x_50, sizeof(void*)*4, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
return x_42;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_ctor_get(x_42, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_42);
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
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_21);
if (x_56 == 0)
{
return x_21;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_21, 0);
x_58 = lean_ctor_get(x_21, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_21);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_9);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_11);
if (x_60 == 0)
{
return x_11;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_11, 0);
x_62 = lean_ctor_get(x_11, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_11);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_6);
lean_dec(x_3);
x_64 = l___private_Lean_Elab_Structure_1__defaultCtorName;
x_65 = l_Lean_Name_append___main(x_2, x_64);
x_66 = l_Lean_Elab_Command_CtorView_inhabited___closed__1;
x_67 = 0;
x_68 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_64);
lean_ctor_set(x_68, 3, x_65);
lean_ctor_set_uint8(x_68, sizeof(void*)*4, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_4);
return x_69;
}
}
}
lean_object* l___private_Lean_Elab_Structure_2__expandCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_2__expandCtor(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkProjection___main___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("', identifiers starting with '_' are reserved to the system");
return x_1;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__4;
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
x_35 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__2;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__5;
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
x_1 = lean_mk_string("unexpected kind of structure field");
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
lean_inc(x_11);
x_100 = l_Lean_Syntax_getKind(x_11);
x_101 = l_Lean_Parser_Command_structExplicitBinder___elambda__1___closed__2;
x_102 = lean_name_eq(x_100, x_101);
if (x_102 == 0)
{
lean_object* x_103; uint8_t x_104; 
x_103 = l_Lean_Parser_Command_structImplicitBinder___elambda__1___closed__2;
x_104 = lean_name_eq(x_100, x_103);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = l_Lean_Parser_Command_structInstBinder___elambda__1___closed__2;
x_106 = lean_name_eq(x_100, x_105);
lean_dec(x_100);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
lean_dec(x_13);
lean_dec(x_5);
x_107 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3;
x_108 = l_Lean_Elab_Command_throwError___rarg(x_11, x_107, x_6, x_7);
lean_dec(x_11);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
return x_108;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_108);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
else
{
uint8_t x_113; 
x_113 = 3;
x_14 = x_113;
x_15 = x_7;
goto block_99;
}
}
else
{
uint8_t x_114; 
lean_dec(x_100);
x_114 = 1;
x_14 = x_114;
x_15 = x_7;
goto block_99;
}
}
else
{
uint8_t x_115; 
lean_dec(x_100);
x_115 = 0;
x_14 = x_115;
x_15 = x_7;
goto block_99;
}
block_99:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Syntax_getArg(x_11, x_16);
lean_inc(x_6);
x_18 = l_Lean_Elab_Command_elabModifiers(x_17, x_6, x_15);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Syntax_getArg(x_11, x_21);
x_23 = l_Lean_Syntax_isNone(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Lean_BinderInfo_beq(x_14, x_24);
lean_inc(x_6);
x_26 = l_Lean_Elab_Command_checkValidFieldModifier(x_11, x_19, x_6, x_20);
if (x_23 == 0)
{
uint8_t x_93; 
x_93 = 1;
x_27 = x_93;
goto block_92;
}
else
{
uint8_t x_94; 
x_94 = 0;
x_27 = x_94;
goto block_92;
}
block_92:
{
lean_object* x_28; lean_object* x_29; 
if (x_25 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_unsigned_to_nat(4u);
x_69 = l_Lean_Syntax_getArg(x_11, x_68);
x_70 = l_Lean_Elab_expandDeclSig(x_69);
lean_dec(x_69);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 1);
x_73 = lean_ctor_get(x_26, 1);
lean_inc(x_73);
lean_dec(x_26);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_70, 1, x_74);
x_28 = x_70;
x_29 = x_73;
goto block_67;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_70, 0);
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_70);
x_77 = lean_ctor_get(x_26, 1);
lean_inc(x_77);
lean_dec(x_26);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_76);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
x_28 = x_79;
x_29 = x_77;
goto block_67;
}
}
else
{
uint8_t x_80; 
lean_dec(x_70);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_26);
if (x_80 == 0)
{
return x_26;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_26, 0);
x_82 = lean_ctor_get(x_26, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_26);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_26, 1);
lean_inc(x_84);
lean_dec(x_26);
x_85 = lean_unsigned_to_nat(4u);
x_86 = l_Lean_Syntax_getArg(x_11, x_85);
x_87 = l_Lean_Elab_expandOptDeclSig(x_86);
lean_dec(x_86);
x_28 = x_87;
x_29 = x_84;
goto block_67;
}
else
{
uint8_t x_88; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_88 = !lean_is_exclusive(x_26);
if (x_88 == 0)
{
return x_26;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_26, 0);
x_90 = lean_ctor_get(x_26, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_26);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
block_67:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_unsigned_to_nat(2u);
x_33 = l_Lean_Syntax_getArg(x_11, x_32);
x_34 = l_Lean_Syntax_getArgs(x_33);
lean_dec(x_33);
if (x_25 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
lean_inc(x_6);
x_36 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_2, x_11, x_14, x_19, x_27, x_30, x_31, x_35, x_34, x_16, x_5, x_6, x_29);
lean_dec(x_34);
lean_dec(x_11);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_4 = x_13;
x_5 = x_37;
x_7 = x_38;
goto _start;
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_unsigned_to_nat(5u);
x_45 = l_Lean_Syntax_getArg(x_11, x_44);
x_46 = l_Lean_Syntax_isNone(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = l_Lean_Syntax_getArg(x_45, x_16);
lean_dec(x_45);
x_48 = l_Lean_Syntax_getArg(x_47, x_12);
lean_dec(x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_inc(x_6);
x_50 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_2, x_11, x_14, x_19, x_27, x_30, x_31, x_49, x_34, x_16, x_5, x_6, x_29);
lean_dec(x_34);
lean_dec(x_11);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_4 = x_13;
x_5 = x_51;
x_7 = x_52;
goto _start;
}
else
{
uint8_t x_54; 
lean_dec(x_13);
lean_dec(x_6);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
return x_50;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_50, 0);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_45);
x_58 = lean_box(0);
lean_inc(x_6);
x_59 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1(x_2, x_11, x_14, x_19, x_27, x_30, x_31, x_58, x_34, x_16, x_5, x_6, x_29);
lean_dec(x_34);
lean_dec(x_11);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_4 = x_13;
x_5 = x_60;
x_7 = x_61;
goto _start;
}
else
{
uint8_t x_63; 
lean_dec(x_13);
lean_dec(x_6);
x_63 = !lean_is_exclusive(x_59);
if (x_63 == 0)
{
return x_59;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_59);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_95 = !lean_is_exclusive(x_18);
if (x_95 == 0)
{
return x_18;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_18, 0);
x_97 = lean_ctor_get(x_18, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_18);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_3__expandFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_unsigned_to_nat(7u);
x_6 = l_Lean_Syntax_getArg(x_1, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Syntax_getArg(x_6, x_7);
lean_dec(x_6);
x_9 = l_Lean_Syntax_getArgs(x_8);
lean_dec(x_8);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(x_1, x_2, x_9, x_7, x_10, x_3, x_4);
lean_dec(x_9);
return x_11;
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_3__expandFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_3__expandFields(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getAppFn___main(x_2);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Elab_Term_getEnv___rarg(x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_6);
x_11 = l_Lean_isStructure(x_9, x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_free_object(x_7);
x_12 = l_Lean_Name_toString___closed__1;
x_13 = l_Lean_Name_toStringWithSep___main(x_12, x_6);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_17 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
x_19 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_Term_throwError___rarg(x_1, x_19, x_3, x_10);
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
else
{
lean_dec(x_3);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
lean_inc(x_6);
x_27 = l_Lean_isStructure(x_25, x_6);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = l_Lean_Name_toString___closed__1;
x_29 = l_Lean_Name_toStringWithSep___main(x_28, x_6);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__6;
x_35 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Term_throwError___rarg(x_1, x_35, x_3, x_26);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_3);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_26);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
x_42 = l___private_Lean_Elab_Structure_5__checkParentIsStructure___closed__3;
x_43 = l_Lean_Elab_Term_throwError___rarg(x_1, x_42, x_3, x_4);
return x_43;
}
}
}
lean_object* l___private_Lean_Elab_Structure_5__checkParentIsStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_box(0);
x_13 = 1;
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_13);
x_15 = lean_array_push(x_2, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
x_18 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(x_4, x_5, x_6, x_7, x_17, x_15, x_8, x_10, x_11);
return x_18;
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
x_84 = l_Lean_Elab_Term_throwError___rarg(x_1, x_83, x_8, x_15);
lean_dec(x_1);
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
x_26 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_8, x_17, x_25, x_20);
lean_inc(x_8);
lean_inc(x_24);
x_27 = l_Lean_Elab_Term_inferType(x_1, x_24, x_8, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_1);
lean_inc(x_13);
x_30 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed), 11, 8);
lean_closure_set(x_30, 0, x_13);
lean_closure_set(x_30, 1, x_6);
lean_closure_set(x_30, 2, x_5);
lean_closure_set(x_30, 3, x_1);
lean_closure_set(x_30, 4, x_2);
lean_closure_set(x_30, 5, x_3);
lean_closure_set(x_30, 6, x_4);
lean_closure_set(x_30, 7, x_7);
x_31 = l_Lean_Elab_Term_withLetDecl___rarg(x_1, x_13, x_28, x_24, x_30, x_8, x_29);
lean_dec(x_1);
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
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_8);
x_39 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_1, x_37);
x_40 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_8, x_17, x_38, x_20);
lean_dec(x_1);
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
x_43 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_1, x_41);
x_44 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_8, x_17, x_42, x_20);
lean_dec(x_1);
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
x_58 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_8, x_17, x_57, x_50);
lean_inc(x_8);
lean_inc(x_56);
x_59 = l_Lean_Elab_Term_inferType(x_1, x_56, x_8, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_1);
lean_inc(x_13);
x_62 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___lambda__1___boxed), 11, 8);
lean_closure_set(x_62, 0, x_13);
lean_closure_set(x_62, 1, x_6);
lean_closure_set(x_62, 2, x_5);
lean_closure_set(x_62, 3, x_1);
lean_closure_set(x_62, 4, x_2);
lean_closure_set(x_62, 5, x_3);
lean_closure_set(x_62, 6, x_4);
lean_closure_set(x_62, 7, x_7);
x_63 = l_Lean_Elab_Term_withLetDecl___rarg(x_1, x_13, x_60, x_56, x_62, x_8, x_61);
lean_dec(x_1);
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
x_71 = l___private_Lean_Elab_Term_2__fromMetaException(x_8, x_1, x_68);
x_72 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_8, x_17, x_69, x_50);
lean_dec(x_1);
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
lean_dec(x_3);
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
lean_object* l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_box(0);
x_13 = 2;
lean_inc(x_9);
x_14 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_13);
x_15 = lean_array_push(x_2, x_14);
lean_inc(x_4);
x_16 = l_Lean_getStructureFieldsFlattened(x_3, x_4);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__1___boxed), 6, 3);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_7);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg(x_8, x_9, x_4, x_16, x_18, x_15, x_17, x_10, x_11);
return x_19;
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_7, x_2);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_11);
x_12 = l_Lean_Elab_Term_elabType(x_11, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
x_15 = l___private_Lean_Elab_Structure_5__checkParentIsStructure(x_11, x_13, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Name_eraseMacroScopes(x_16);
x_19 = l_Lean_Name_getString_x21(x_18);
lean_dec(x_18);
x_20 = l___private_Lean_Elab_Structure_9__withParents___main___rarg___closed__1;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_name_mk_string(x_22, x_21);
x_24 = l___private_Lean_Elab_Structure_7__containsFieldName(x_3, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = l_Lean_Elab_Term_getEnv___rarg(x_17);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
lean_inc(x_11);
lean_inc(x_16);
lean_inc(x_26);
lean_inc(x_23);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_9__withParents___main___rarg___lambda__2), 11, 8);
lean_closure_set(x_29, 0, x_23);
lean_closure_set(x_29, 1, x_3);
lean_closure_set(x_29, 2, x_26);
lean_closure_set(x_29, 3, x_16);
lean_closure_set(x_29, 4, x_2);
lean_closure_set(x_29, 5, x_1);
lean_closure_set(x_29, 6, x_4);
lean_closure_set(x_29, 7, x_11);
if (x_28 == 0)
{
uint8_t x_30; lean_object* x_31; 
lean_dec(x_26);
lean_dec(x_16);
x_30 = 0;
x_31 = l_Lean_Elab_Term_withLocalDecl___rarg(x_11, x_23, x_30, x_13, x_29, x_5, x_27);
lean_dec(x_11);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_is_class(x_26, x_16);
if (x_32 == 0)
{
uint8_t x_33; lean_object* x_34; 
x_33 = 0;
x_34 = l_Lean_Elab_Term_withLocalDecl___rarg(x_11, x_23, x_33, x_13, x_29, x_5, x_27);
lean_dec(x_11);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; 
x_35 = 3;
x_36 = l_Lean_Elab_Term_withLocalDecl___rarg(x_11, x_23, x_35, x_13, x_29, x_5, x_27);
lean_dec(x_11);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_37, 0, x_23);
x_38 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_39 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_40 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_41 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_Term_throwError___rarg(x_11, x_41, x_5, x_17);
lean_dec(x_11);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
return x_42;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_15, 0);
x_49 = lean_ctor_get(x_15, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_15);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
return x_12;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_12, 0);
x_53 = lean_ctor_get(x_12, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_12);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
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
lean_object* x_5; lean_object* x_6; lean_object* x_68; 
x_68 = lean_ctor_get(x_1, 5);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_box(0);
x_5 = x_69;
x_6 = x_4;
goto block_67;
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_3);
lean_inc(x_71);
x_72 = l_Lean_Elab_Term_elabType(x_71, x_3, x_4);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_3);
lean_inc(x_2);
x_75 = l_Lean_Elab_Term_mkForall(x_71, x_2, x_73, x_3, x_74);
lean_dec(x_71);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_ctor_set(x_68, 0, x_76);
x_5 = x_68;
x_6 = x_77;
goto block_67;
}
else
{
uint8_t x_78; 
lean_free_object(x_68);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 0);
x_80 = lean_ctor_get(x_75, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_75);
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
lean_free_object(x_68);
lean_dec(x_71);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_72);
if (x_82 == 0)
{
return x_72;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_72, 0);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_72);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
lean_dec(x_68);
lean_inc(x_3);
lean_inc(x_86);
x_87 = l_Lean_Elab_Term_elabType(x_86, x_3, x_4);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_3);
lean_inc(x_2);
x_90 = l_Lean_Elab_Term_mkForall(x_86, x_2, x_88, x_3, x_89);
lean_dec(x_86);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_91);
x_5 = x_93;
x_6 = x_92;
goto block_67;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_86);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_87, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_100 = x_87;
} else {
 lean_dec_ref(x_87);
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
}
block_67:
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
lean_inc(x_12);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_elabTermAux___main(x_5, x_13, x_13, x_12, x_3, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_mkLambda(x_12, x_2, x_15, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
x_20 = l_Lean_Elab_Term_ensureHasType(x_12, x_5, x_18, x_3, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_7, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
lean_ctor_set(x_7, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_free_object(x_7);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
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
lean_free_object(x_7);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_7, 0);
lean_inc(x_40);
lean_dec(x_7);
x_41 = 1;
lean_inc(x_3);
lean_inc(x_40);
lean_inc(x_5);
x_42 = l_Lean_Elab_Term_elabTermAux___main(x_5, x_41, x_41, x_40, x_3, x_6);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_3);
x_45 = l_Lean_Elab_Term_mkLambda(x_40, x_2, x_43, x_3, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_5);
x_48 = l_Lean_Elab_Term_ensureHasType(x_40, x_5, x_46, x_3, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
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
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_5);
lean_ctor_set(x_53, 1, x_52);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_5);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_48, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_57 = x_48;
} else {
 lean_dec_ref(x_48);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_40);
lean_dec(x_5);
lean_dec(x_3);
x_59 = lean_ctor_get(x_45, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_61 = x_45;
} else {
 lean_dec_ref(x_45);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_40);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_65 = x_42;
} else {
 lean_dec_ref(x_42);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = 0;
x_11 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_2);
lean_ctor_set_uint8(x_11, sizeof(void*)*3, x_10);
x_12 = lean_array_push(x_3, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_4, x_13);
x_15 = l___private_Lean_Elab_Structure_10__withFields___main___rarg(x_5, x_14, x_12, x_6, x_8, x_9);
return x_15;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_array_fget(x_1, x_2);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = l_Lean_Syntax_getArgs(x_11);
lean_dec(x_11);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__1), 4, 1);
lean_closure_set(x_13, 0, x_10);
lean_inc(x_5);
x_14 = l_Lean_Elab_Term_elabBinders___rarg(x_12, x_13, x_5, x_6);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_10, 3);
lean_inc(x_19);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_findMAux___main___at___private_Lean_Elab_Structure_6__findFieldInfo_x3f___spec__1(x_19, x_3, x_20);
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_17) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__3;
x_24 = l_Lean_Elab_Term_throwError___rarg(x_22, x_23, x_5, x_16);
lean_dec(x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_inc(x_5);
x_27 = l_Lean_Elab_Term_inferType(x_26, x_25, x_5, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_dec(x_10);
lean_inc(x_19);
x_31 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed), 9, 6);
lean_closure_set(x_31, 0, x_19);
lean_closure_set(x_31, 1, x_17);
lean_closure_set(x_31, 2, x_3);
lean_closure_set(x_31, 3, x_2);
lean_closure_set(x_31, 4, x_1);
lean_closure_set(x_31, 5, x_4);
x_32 = l_Lean_Elab_Term_withLocalDecl___rarg(x_26, x_19, x_30, x_28, x_31, x_5, x_29);
lean_dec(x_26);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_26);
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
lean_dec(x_10);
lean_inc(x_19);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed), 9, 6);
lean_closure_set(x_40, 0, x_19);
lean_closure_set(x_40, 1, x_18);
lean_closure_set(x_40, 2, x_3);
lean_closure_set(x_40, 3, x_2);
lean_closure_set(x_40, 4, x_1);
lean_closure_set(x_40, 5, x_4);
x_41 = l_Lean_Elab_Term_withLocalDecl___rarg(x_38, x_19, x_39, x_37, x_40, x_5, x_16);
lean_dec(x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_21);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_21, 0);
x_44 = lean_ctor_get_uint8(x_43, sizeof(void*)*3);
switch (x_44) {
case 0:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_free_object(x_21);
lean_dec(x_43);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_ctor_get(x_10, 0);
lean_inc(x_45);
lean_dec(x_10);
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_19);
x_47 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_48 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Elab_Term_throwError___rarg(x_45, x_50, x_5, x_16);
lean_dec(x_45);
return x_51;
}
case 1:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_21);
lean_dec(x_43);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_10, 0);
lean_inc(x_52);
lean_dec(x_10);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_19);
x_54 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_55 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6;
x_57 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_Term_throwError___rarg(x_52, x_57, x_5, x_16);
lean_dec(x_52);
return x_58;
}
else
{
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_59; 
lean_dec(x_19);
x_59 = !lean_is_exclusive(x_43);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_43, 0);
x_61 = lean_ctor_get(x_43, 1);
x_62 = lean_ctor_get(x_43, 2);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_18);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_18, 0);
x_65 = lean_ctor_get(x_10, 0);
lean_inc(x_65);
lean_inc(x_5);
lean_inc(x_61);
x_66 = l_Lean_Elab_Term_inferType(x_65, x_61, x_5, x_16);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_10, 6);
lean_inc(x_69);
lean_dec(x_10);
lean_ctor_set(x_18, 0, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = l_Lean_Syntax_inhabited;
x_71 = l_Option_get_x21___rarg___closed__3;
x_72 = lean_panic_fn(x_70, x_71);
lean_inc(x_5);
x_73 = l_Lean_Elab_Term_ensureHasType(x_72, x_18, x_64, x_5, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_ctor_set(x_21, 0, x_74);
lean_ctor_set(x_43, 2, x_21);
x_76 = lean_array_push(x_3, x_43);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_2, x_77);
lean_dec(x_2);
x_2 = x_78;
x_3 = x_76;
x_6 = x_75;
goto _start;
}
else
{
uint8_t x_80; 
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_60);
lean_free_object(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_73);
if (x_80 == 0)
{
return x_73;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_73, 0);
x_82 = lean_ctor_get(x_73, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_73);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_free_object(x_21);
x_84 = !lean_is_exclusive(x_69);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_69, 0);
lean_inc(x_5);
x_86 = l_Lean_Elab_Term_ensureHasType(x_85, x_18, x_64, x_5, x_68);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_ctor_set(x_69, 0, x_87);
lean_ctor_set(x_43, 2, x_69);
x_89 = lean_array_push(x_3, x_43);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_2, x_90);
lean_dec(x_2);
x_2 = x_91;
x_3 = x_89;
x_6 = x_88;
goto _start;
}
else
{
uint8_t x_93; 
lean_free_object(x_69);
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_86);
if (x_93 == 0)
{
return x_86;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_86, 0);
x_95 = lean_ctor_get(x_86, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_86);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_69, 0);
lean_inc(x_97);
lean_dec(x_69);
lean_inc(x_5);
x_98 = l_Lean_Elab_Term_ensureHasType(x_97, x_18, x_64, x_5, x_68);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_43, 2, x_101);
x_102 = lean_array_push(x_3, x_43);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_add(x_2, x_103);
lean_dec(x_2);
x_2 = x_104;
x_3 = x_102;
x_6 = x_100;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_98, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_108 = x_98;
} else {
 lean_dec_ref(x_98);
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
}
}
else
{
uint8_t x_110; 
lean_free_object(x_18);
lean_dec(x_64);
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_60);
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_66);
if (x_110 == 0)
{
return x_66;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_66, 0);
x_112 = lean_ctor_get(x_66, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_66);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_18, 0);
lean_inc(x_114);
lean_dec(x_18);
x_115 = lean_ctor_get(x_10, 0);
lean_inc(x_115);
lean_inc(x_5);
lean_inc(x_61);
x_116 = l_Lean_Elab_Term_inferType(x_115, x_61, x_5, x_16);
lean_dec(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_10, 6);
lean_inc(x_119);
lean_dec(x_10);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_117);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = l_Lean_Syntax_inhabited;
x_122 = l_Option_get_x21___rarg___closed__3;
x_123 = lean_panic_fn(x_121, x_122);
lean_inc(x_5);
x_124 = l_Lean_Elab_Term_ensureHasType(x_123, x_120, x_114, x_5, x_118);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_ctor_set(x_21, 0, x_125);
lean_ctor_set(x_43, 2, x_21);
x_127 = lean_array_push(x_3, x_43);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_add(x_2, x_128);
lean_dec(x_2);
x_2 = x_129;
x_3 = x_127;
x_6 = x_126;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_60);
lean_free_object(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_ctor_get(x_124, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_133 = x_124;
} else {
 lean_dec_ref(x_124);
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
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_free_object(x_21);
x_135 = lean_ctor_get(x_119, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_136 = x_119;
} else {
 lean_dec_ref(x_119);
 x_136 = lean_box(0);
}
lean_inc(x_5);
x_137 = l_Lean_Elab_Term_ensureHasType(x_135, x_120, x_114, x_5, x_118);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
if (lean_is_scalar(x_136)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_136;
}
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_43, 2, x_140);
x_141 = lean_array_push(x_3, x_43);
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_nat_add(x_2, x_142);
lean_dec(x_2);
x_2 = x_143;
x_3 = x_141;
x_6 = x_139;
goto _start;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_136);
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_ctor_get(x_137, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_137, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_147 = x_137;
} else {
 lean_dec_ref(x_137);
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
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_114);
lean_free_object(x_43);
lean_dec(x_61);
lean_dec(x_60);
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_116, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_116, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_151 = x_116;
} else {
 lean_dec_ref(x_116);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_ctor_get(x_43, 0);
x_154 = lean_ctor_get(x_43, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_43);
x_155 = lean_ctor_get(x_18, 0);
lean_inc(x_155);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_156 = x_18;
} else {
 lean_dec_ref(x_18);
 x_156 = lean_box(0);
}
x_157 = lean_ctor_get(x_10, 0);
lean_inc(x_157);
lean_inc(x_5);
lean_inc(x_154);
x_158 = l_Lean_Elab_Term_inferType(x_157, x_154, x_5, x_16);
lean_dec(x_157);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_10, 6);
lean_inc(x_161);
lean_dec(x_10);
if (lean_is_scalar(x_156)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_156;
}
lean_ctor_set(x_162, 0, x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = l_Lean_Syntax_inhabited;
x_164 = l_Option_get_x21___rarg___closed__3;
x_165 = lean_panic_fn(x_163, x_164);
lean_inc(x_5);
x_166 = l_Lean_Elab_Term_ensureHasType(x_165, x_162, x_155, x_5, x_160);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
lean_ctor_set(x_21, 0, x_167);
x_169 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_169, 0, x_153);
lean_ctor_set(x_169, 1, x_154);
lean_ctor_set(x_169, 2, x_21);
lean_ctor_set_uint8(x_169, sizeof(void*)*3, x_44);
x_170 = lean_array_push(x_3, x_169);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_nat_add(x_2, x_171);
lean_dec(x_2);
x_2 = x_172;
x_3 = x_170;
x_6 = x_168;
goto _start;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_154);
lean_dec(x_153);
lean_free_object(x_21);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_166, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_166, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_176 = x_166;
} else {
 lean_dec_ref(x_166);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_free_object(x_21);
x_178 = lean_ctor_get(x_161, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_179 = x_161;
} else {
 lean_dec_ref(x_161);
 x_179 = lean_box(0);
}
lean_inc(x_5);
x_180 = l_Lean_Elab_Term_ensureHasType(x_178, x_162, x_155, x_5, x_160);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec(x_180);
if (lean_is_scalar(x_179)) {
 x_183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_183 = x_179;
}
lean_ctor_set(x_183, 0, x_181);
x_184 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_184, 0, x_153);
lean_ctor_set(x_184, 1, x_154);
lean_ctor_set(x_184, 2, x_183);
lean_ctor_set_uint8(x_184, sizeof(void*)*3, x_44);
x_185 = lean_array_push(x_3, x_184);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_add(x_2, x_186);
lean_dec(x_2);
x_2 = x_187;
x_3 = x_185;
x_6 = x_182;
goto _start;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_179);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_ctor_get(x_180, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_180, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_191 = x_180;
} else {
 lean_dec_ref(x_180);
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
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = lean_ctor_get(x_158, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_158, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_195 = x_158;
} else {
 lean_dec_ref(x_158);
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
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_free_object(x_21);
lean_dec(x_43);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_ctor_get(x_10, 5);
lean_inc(x_197);
lean_dec(x_10);
x_198 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_198, 0, x_19);
x_199 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9;
x_200 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
x_201 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12;
x_202 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_203 = l_Lean_Syntax_inhabited;
x_204 = l_Option_get_x21___rarg___closed__3;
x_205 = lean_panic_fn(x_203, x_204);
x_206 = l_Lean_Elab_Term_throwError___rarg(x_205, x_202, x_5, x_16);
lean_dec(x_205);
return x_206;
}
else
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_197, 0);
lean_inc(x_207);
lean_dec(x_197);
x_208 = l_Lean_Elab_Term_throwError___rarg(x_207, x_202, x_5, x_16);
lean_dec(x_207);
return x_208;
}
}
}
}
default: 
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_free_object(x_21);
lean_dec(x_43);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1___closed__1;
x_210 = l_unreachable_x21___rarg(x_209);
x_211 = lean_apply_2(x_210, x_5, x_16);
return x_211;
}
}
}
else
{
lean_object* x_212; uint8_t x_213; 
x_212 = lean_ctor_get(x_21, 0);
lean_inc(x_212);
lean_dec(x_21);
x_213 = lean_ctor_get_uint8(x_212, sizeof(void*)*3);
switch (x_213) {
case 0:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_212);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_214 = lean_ctor_get(x_10, 0);
lean_inc(x_214);
lean_dec(x_10);
x_215 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_215, 0, x_19);
x_216 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_217 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_215);
x_218 = l_Lean_Elab_Command_throwAlreadyDeclaredUniverseLevel___rarg___closed__5;
x_219 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_Elab_Term_throwError___rarg(x_214, x_219, x_5, x_16);
lean_dec(x_214);
return x_220;
}
case 1:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_212);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_221 = lean_ctor_get(x_10, 0);
lean_inc(x_221);
lean_dec(x_10);
x_222 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_222, 0, x_19);
x_223 = l___private_Lean_Elab_Structure_8__processSubfields___main___rarg___closed__3;
x_224 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_222);
x_225 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__6;
x_226 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_Elab_Term_throwError___rarg(x_221, x_226, x_5, x_16);
lean_dec(x_221);
return x_227;
}
else
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_19);
x_228 = lean_ctor_get(x_212, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_212, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 x_230 = x_212;
} else {
 lean_dec_ref(x_212);
 x_230 = lean_box(0);
}
x_231 = lean_ctor_get(x_18, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_232 = x_18;
} else {
 lean_dec_ref(x_18);
 x_232 = lean_box(0);
}
x_233 = lean_ctor_get(x_10, 0);
lean_inc(x_233);
lean_inc(x_5);
lean_inc(x_229);
x_234 = l_Lean_Elab_Term_inferType(x_233, x_229, x_5, x_16);
lean_dec(x_233);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_10, 6);
lean_inc(x_237);
lean_dec(x_10);
if (lean_is_scalar(x_232)) {
 x_238 = lean_alloc_ctor(1, 1, 0);
} else {
 x_238 = x_232;
}
lean_ctor_set(x_238, 0, x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_239 = l_Lean_Syntax_inhabited;
x_240 = l_Option_get_x21___rarg___closed__3;
x_241 = lean_panic_fn(x_239, x_240);
lean_inc(x_5);
x_242 = l_Lean_Elab_Term_ensureHasType(x_241, x_238, x_231, x_5, x_236);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_243);
if (lean_is_scalar(x_230)) {
 x_246 = lean_alloc_ctor(0, 3, 1);
} else {
 x_246 = x_230;
}
lean_ctor_set(x_246, 0, x_228);
lean_ctor_set(x_246, 1, x_229);
lean_ctor_set(x_246, 2, x_245);
lean_ctor_set_uint8(x_246, sizeof(void*)*3, x_213);
x_247 = lean_array_push(x_3, x_246);
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_nat_add(x_2, x_248);
lean_dec(x_2);
x_2 = x_249;
x_3 = x_247;
x_6 = x_244;
goto _start;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_251 = lean_ctor_get(x_242, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_242, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_253 = x_242;
} else {
 lean_dec_ref(x_242);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_237, 0);
lean_inc(x_255);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 x_256 = x_237;
} else {
 lean_dec_ref(x_237);
 x_256 = lean_box(0);
}
lean_inc(x_5);
x_257 = l_Lean_Elab_Term_ensureHasType(x_255, x_238, x_231, x_5, x_236);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
if (lean_is_scalar(x_256)) {
 x_260 = lean_alloc_ctor(1, 1, 0);
} else {
 x_260 = x_256;
}
lean_ctor_set(x_260, 0, x_258);
if (lean_is_scalar(x_230)) {
 x_261 = lean_alloc_ctor(0, 3, 1);
} else {
 x_261 = x_230;
}
lean_ctor_set(x_261, 0, x_228);
lean_ctor_set(x_261, 1, x_229);
lean_ctor_set(x_261, 2, x_260);
lean_ctor_set_uint8(x_261, sizeof(void*)*3, x_213);
x_262 = lean_array_push(x_3, x_261);
x_263 = lean_unsigned_to_nat(1u);
x_264 = lean_nat_add(x_2, x_263);
lean_dec(x_2);
x_2 = x_264;
x_3 = x_262;
x_6 = x_259;
goto _start;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_256);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = lean_ctor_get(x_257, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_257, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_268 = x_257;
} else {
 lean_dec_ref(x_257);
 x_268 = lean_box(0);
}
if (lean_is_scalar(x_268)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_268;
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_267);
return x_269;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = lean_ctor_get(x_234, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_234, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_272 = x_234;
} else {
 lean_dec_ref(x_234);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_212);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_274 = lean_ctor_get(x_10, 5);
lean_inc(x_274);
lean_dec(x_10);
x_275 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_275, 0, x_19);
x_276 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__9;
x_277 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
x_278 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___closed__12;
x_279 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_280 = l_Lean_Syntax_inhabited;
x_281 = l_Option_get_x21___rarg___closed__3;
x_282 = lean_panic_fn(x_280, x_281);
x_283 = l_Lean_Elab_Term_throwError___rarg(x_282, x_279, x_5, x_16);
lean_dec(x_282);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_274, 0);
lean_inc(x_284);
lean_dec(x_274);
x_285 = l_Lean_Elab_Term_throwError___rarg(x_284, x_279, x_5, x_16);
lean_dec(x_284);
return x_285;
}
}
}
}
default: 
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_212);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_286 = l___private_Lean_Elab_SyntheticMVars_2__resumePostponed___lambda__1___closed__1;
x_287 = l_unreachable_x21___rarg(x_286);
x_288 = lean_apply_2(x_287, x_5, x_16);
return x_288;
}
}
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_14);
if (x_289 == 0)
{
return x_14;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_14, 0);
x_291 = lean_ctor_get(x_14, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_14);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
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
lean_object* l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Structure_10__withFields___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
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
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_whnf(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 3)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_dec(x_5);
x_14 = l___private_Lean_Elab_Structure_11__getResultUniverse___closed__3;
x_15 = l_Lean_Elab_Term_throwError___rarg(x_1, x_14, x_3, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_dec(x_3);
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
lean_object* l___private_Lean_Elab_Structure_11__getResultUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Structure_11__getResultUniverse(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
lean_inc(x_6);
x_14 = l_Lean_Elab_Term_inferType(x_1, x_11, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_6);
x_17 = l_Lean_Elab_Term_collectUsedFVars(x_1, x_5, x_15, x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_13;
x_5 = x_18;
x_7 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_6);
x_15 = l_Lean_Elab_Term_inferType(x_1, x_14, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_6);
x_18 = l_Lean_Elab_Term_collectUsedFVars(x_1, x_5, x_16, x_6, x_17);
x_19 = lean_ctor_get(x_11, 2);
lean_inc(x_19);
lean_dec(x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_4 = x_13;
x_5 = x_20;
x_7 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 0);
lean_inc(x_25);
lean_dec(x_19);
lean_inc(x_6);
x_26 = l_Lean_Elab_Term_collectUsedFVars(x_1, x_23, x_25, x_6, x_24);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_4 = x_13;
x_5 = x_27;
x_7 = x_28;
goto _start;
}
}
else
{
uint8_t x_30; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_15);
if (x_30 == 0)
{
return x_15;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_15);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_12__removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_inc(x_5);
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1(x_1, x_3, x_3, x_7, x_8, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
x_12 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2(x_1, x_4, x_4, x_7, x_10, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Elab_Term_removeUnused(x_1, x_2, x_13, x_5, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_5);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
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
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_12__removeUnused___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_12__removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_12__removeUnused(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_13__withUsed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l___private_Lean_Elab_Structure_12__removeUnused(x_1, x_2, x_3, x_4, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_6);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 2);
lean_dec(x_19);
x_20 = lean_ctor_get(x_11, 1);
lean_dec(x_20);
lean_ctor_set(x_11, 2, x_14);
lean_ctor_set(x_11, 1, x_13);
x_21 = lean_apply_3(x_5, x_15, x_6, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 3);
x_24 = lean_ctor_get(x_11, 4);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_13);
lean_ctor_set(x_25, 2, x_14);
lean_ctor_set(x_25, 3, x_23);
lean_ctor_set(x_25, 4, x_24);
lean_ctor_set(x_6, 0, x_25);
x_26 = lean_apply_3(x_5, x_15, x_6, x_12);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_27 = lean_ctor_get(x_6, 1);
x_28 = lean_ctor_get(x_6, 2);
x_29 = lean_ctor_get(x_6, 3);
x_30 = lean_ctor_get(x_6, 4);
x_31 = lean_ctor_get(x_6, 5);
x_32 = lean_ctor_get(x_6, 6);
x_33 = lean_ctor_get(x_6, 7);
x_34 = lean_ctor_get(x_6, 8);
x_35 = lean_ctor_get(x_6, 9);
x_36 = lean_ctor_get_uint8(x_6, sizeof(void*)*10);
x_37 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 1);
x_38 = lean_ctor_get_uint8(x_6, sizeof(void*)*10 + 2);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_6);
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_11, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_11, 4);
lean_inc(x_41);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 lean_ctor_release(x_11, 2);
 lean_ctor_release(x_11, 3);
 lean_ctor_release(x_11, 4);
 x_42 = x_11;
} else {
 lean_dec_ref(x_11);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(0, 5, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_13);
lean_ctor_set(x_43, 2, x_14);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_41);
x_44 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_27);
lean_ctor_set(x_44, 2, x_28);
lean_ctor_set(x_44, 3, x_29);
lean_ctor_set(x_44, 4, x_30);
lean_ctor_set(x_44, 5, x_31);
lean_ctor_set(x_44, 6, x_32);
lean_ctor_set(x_44, 7, x_33);
lean_ctor_set(x_44, 8, x_34);
lean_ctor_set(x_44, 9, x_35);
lean_ctor_set_uint8(x_44, sizeof(void*)*10, x_36);
lean_ctor_set_uint8(x_44, sizeof(void*)*10 + 1, x_37);
lean_ctor_set_uint8(x_44, sizeof(void*)*10 + 2, x_38);
x_45 = lean_apply_3(x_5, x_15, x_44, x_12);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
return x_8;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_8, 0);
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_8);
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
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_13__withUsed___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_13__withUsed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Structure_13__withUsed___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_14__levelMVarToParamFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Term_inferType(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Term_levelMVarToParam_x27(x_7, x_3, x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_21 = x_18;
} else {
 lean_dec_ref(x_18);
 x_21 = lean_box(0);
}
x_22 = lean_box(0);
if (lean_is_scalar(x_21)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_21;
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
return x_6;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_6);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_14__levelMVarToParamFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_14__levelMVarToParamFVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_2, x_3);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
lean_inc(x_5);
x_15 = l___private_Lean_Elab_Structure_14__levelMVarToParamFVar(x_1, x_12, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_3 = x_14;
x_4 = x_18;
x_6 = x_17;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_14);
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(x_1, x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_15__levelMVarToParamFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_15__levelMVarToParamFVars(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_array_fget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_fset(x_3, x_2, x_13);
x_15 = x_12;
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_19 = lean_ctor_get(x_15, 2);
lean_inc(x_19);
lean_inc(x_5);
lean_inc(x_17);
x_20 = l___private_Lean_Elab_Structure_14__levelMVarToParamFVar(x_1, x_17, x_4, x_5, x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
lean_dec(x_16);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
x_26 = x_15;
x_27 = lean_array_fset(x_14, x_2, x_26);
lean_dec(x_2);
x_2 = x_25;
x_3 = x_27;
x_4 = x_23;
x_6 = x_22;
goto _start;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_15, 2);
lean_dec(x_30);
x_31 = lean_ctor_get(x_15, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_15, 0);
lean_dec(x_32);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = !lean_is_exclusive(x_19);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_5);
x_37 = l_Lean_Elab_Term_levelMVarToParam_x27(x_36, x_34, x_5, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_19, 0, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_2, x_42);
x_44 = x_15;
x_45 = lean_array_fset(x_14, x_2, x_44);
lean_dec(x_2);
x_2 = x_43;
x_3 = x_45;
x_4 = x_41;
x_6 = x_39;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_47 = lean_ctor_get(x_19, 0);
lean_inc(x_47);
lean_dec(x_19);
lean_inc(x_5);
x_48 = l_Lean_Elab_Term_levelMVarToParam_x27(x_47, x_34, x_5, x_33);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_15, 2, x_53);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_2, x_54);
x_56 = x_15;
x_57 = lean_array_fset(x_14, x_2, x_56);
lean_dec(x_2);
x_2 = x_55;
x_3 = x_57;
x_4 = x_52;
x_6 = x_50;
goto _start;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_dec(x_20);
x_60 = lean_ctor_get(x_21, 1);
lean_inc(x_60);
lean_dec(x_21);
x_61 = lean_ctor_get(x_19, 0);
lean_inc(x_61);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_62 = x_19;
} else {
 lean_dec_ref(x_19);
 x_62 = lean_box(0);
}
lean_inc(x_5);
x_63 = l_Lean_Elab_Term_levelMVarToParam_x27(x_61, x_60, x_5, x_59);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_66);
x_69 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_69, 0, x_16);
lean_ctor_set(x_69, 1, x_17);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set_uint8(x_69, sizeof(void*)*3, x_18);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_add(x_2, x_70);
x_72 = x_69;
x_73 = lean_array_fset(x_14, x_2, x_72);
lean_dec(x_2);
x_2 = x_71;
x_3 = x_73;
x_4 = x_67;
x_6 = x_65;
goto _start;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_20);
if (x_75 == 0)
{
return x_20;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_20, 0);
x_77 = lean_ctor_get(x_20, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_20);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = x_4;
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamAux___spec__1___boxed), 6, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_8);
lean_inc(x_6);
x_11 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(x_1, x_2, x_9, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
x_15 = l_Array_forMAux___main___at___private_Lean_Elab_Structure_15__levelMVarToParamFVars___spec__1(x_1, x_3, x_9, x_14, x_6, x_13);
lean_dec(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = x_10;
x_20 = lean_apply_3(x_19, x_18, x_6, x_17);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
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
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at___private_Lean_Elab_Structure_16__levelMVarToParamAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Structure_16__levelMVarToParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Structure_16__levelMVarToParamAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l___private_Lean_Elab_Structure_16__levelMVarToParamAux(x_1, x_2, x_3, x_4, x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
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
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_17__levelMVarToParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_17__levelMVarToParam(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_array_fget(x_5, x_6);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_8);
x_17 = l_Lean_Elab_Term_inferType(x_1, x_16, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_8);
x_20 = l_Lean_Elab_Term_getLevel(x_1, x_18, x_8, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_8);
x_23 = l_Lean_Elab_Term_instantiateLevelMVars(x_1, x_21, x_8, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_3);
x_26 = l_Lean_Elab_Command_accLevelAtCtor___main(x_24, x_2, x_3, x_7);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_3);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_Term_throwError___rarg(x_1, x_29, x_8, x_25);
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
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
lean_dec(x_26);
x_6 = x_15;
x_7 = x_35;
x_9 = x_25;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 0);
x_39 = lean_ctor_get(x_20, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_20);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_17);
if (x_41 == 0)
{
return x_17;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_18__collectUniversesFromFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_empty___closed__1;
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_4, x_4, x_7, x_8, x_5, x_6);
return x_9;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_18__collectUniversesFromFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Structure_18__collectUniversesFromFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_18__collectUniversesFromFields(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l___private_Lean_Elab_Structure_11__getResultUniverse(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Level_getOffsetAux___main(x_7, x_9);
x_11 = l_Lean_Level_getLevelOffset___main(x_7);
lean_dec(x_7);
if (lean_obj_tag(x_11) == 5)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_Structure_18__collectUniversesFromFields(x_1, x_11, x_10, x_2, x_4, x_8);
lean_dec(x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_toList___rarg(x_14);
lean_dec(x_14);
x_17 = l_Lean_Level_mkNaryMax___main(x_16);
x_18 = l_Lean_Elab_Term_assignLevelMVar(x_12, x_17, x_4, x_15);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Elab_Term_instantiateMVars(x_1, x_3, x_4, x_19);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_25 = l___private_Lean_Elab_Structure_19__updateResultingUniverse___closed__3;
x_26 = l_Lean_Elab_Term_throwError___rarg(x_1, x_25, x_4, x_8);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_6);
if (x_27 == 0)
{
return x_6;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_6, 0);
x_29 = lean_ctor_get(x_6, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_6);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_19__updateResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_19__updateResultingUniverse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Elab_Term_inferType(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Term_instantiateMVars(x_1, x_7, x_4, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_CollectLevelParams_main___main(x_11, x_2);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_9);
x_15 = l_Lean_CollectLevelParams_main___main(x_13, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_6);
if (x_17 == 0)
{
return x_6;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
lean_inc(x_6);
x_14 = l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar(x_1, x_5, x_11, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_4 = x_13;
x_5 = x_15;
x_7 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_6);
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
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(x_1, x_2, x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Structure_21__collectLevelParamsInFVars(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_6);
x_15 = l___private_Lean_Elab_Structure_20__collectLevelParamsInFVar(x_1, x_5, x_14, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_4 = x_13;
x_5 = x_16;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Elab_Command_mkDef___lambda__1___closed__5;
lean_inc(x_5);
x_9 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(x_1, x_2, x_2, x_7, x_8, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
x_12 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_21__collectLevelParamsInFVars___spec__1(x_1, x_3, x_3, x_7, x_10, x_5, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1(x_1, x_4, x_4, x_7, x_13, x_5, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
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
else
{
uint8_t x_27; 
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
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
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_1);
x_10 = l___private_Lean_Elab_Structure_17__levelMVarToParam(x_1, x_7, x_2, x_3, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
if (x_5 == 0)
{
x_13 = x_6;
x_14 = x_12;
goto block_54;
}
else
{
lean_object* x_55; 
lean_inc(x_8);
x_55 = l___private_Lean_Elab_Structure_19__updateResultingUniverse(x_1, x_11, x_6, x_8, x_12);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_13 = x_56;
x_14 = x_57;
goto block_54;
}
else
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
block_54:
{
lean_object* x_15; 
lean_inc(x_8);
x_15 = l___private_Lean_Elab_Structure_22__collectLevelParamsInStructure(x_1, x_7, x_2, x_11, x_8, x_14);
lean_dec(x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 3);
lean_inc(x_19);
lean_dec(x_4);
x_20 = l_Lean_Elab_Command_sortDeclLevelParams(x_18, x_19, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_2);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Elab_Term_throwError___rarg(x_1, x_23, x_8, x_17);
lean_dec(x_1);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
lean_inc(x_8);
x_26 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_13, x_8, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_8);
x_29 = l_Lean_Elab_Term_mkForall(x_1, x_7, x_27, x_8, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_List_toString___at_Lean_Elab_OpenDecl_HasToString___spec__2(x_25);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__3;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_38 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_30);
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Elab_Term_throwError___rarg(x_1, x_40, x_8, x_31);
lean_dec(x_1);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_26);
if (x_46 == 0)
{
return x_26;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_26, 0);
x_48 = lean_ctor_get(x_26, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_26);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_15);
if (x_50 == 0)
{
return x_15;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_15, 0);
x_52 = lean_ctor_get(x_15, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_15);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_10);
if (x_62 == 0)
{
return x_10;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_10, 0);
x_64 = lean_ctor_get(x_10, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_10);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_box(0);
lean_inc(x_6);
x_10 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_8, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_2);
x_12 = l___private_Lean_Elab_Structure_11__getResultUniverse(x_1, x_2, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
x_15 = l_Lean_Elab_Command_shouldInferResultUniverse(x_1, x_13, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_3, 5);
lean_inc(x_18);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___boxed), 9, 6);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_5);
lean_closure_set(x_19, 3, x_3);
lean_closure_set(x_19, 4, x_16);
lean_closure_set(x_19, 5, x_2);
x_20 = l___private_Lean_Elab_Structure_13__withUsed___rarg(x_1, x_18, x_4, x_5, x_19, x_6, x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_18);
lean_dec(x_1);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 10);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_23__elabStructureView___lambda__2), 7, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_1);
lean_closure_set(x_9, 3, x_4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Elab_Structure_10__withFields___main___rarg(x_8, x_10, x_5, x_9, x_6, x_7);
return x_11;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_23__elabStructureView___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected Type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_23__elabStructureView___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_23__elabStructureView___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Structure_23__elabStructureView___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Structure_23__elabStructureView___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Structure_23__elabStructureView___lambda__3), 7, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_4);
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_1);
x_12 = l___private_Lean_Elab_Structure_23__elabStructureView___closed__3;
x_13 = l_Lean_Elab_Term_throwError___rarg(x_5, x_12, x_2, x_8);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Array_empty___closed__1;
x_20 = l___private_Lean_Elab_Structure_9__withParents___main___rarg(x_1, x_18, x_19, x_11, x_2, x_8);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
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
x_16 = l___private_Lean_Elab_Structure_23__elabStructureView(x_15, x_13, x_14);
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
lean_object* l_Lean_Elab_Command_elabStructure___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
x_12 = l_Lean_Elab_Command_mkDeclName(x_1, x_2, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
x_15 = l_Lean_Elab_Command_getLevelNames(x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_3);
x_18 = l___private_Lean_Elab_Structure_2__expandCtor(x_3, x_13, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
x_21 = l___private_Lean_Elab_Structure_3__expandFields(x_3, x_13, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_13);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_13);
x_25 = lean_box(x_5);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabStructure___lambda__2___boxed), 14, 11);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_4);
lean_closure_set(x_26, 3, x_16);
lean_closure_set(x_26, 4, x_25);
lean_closure_set(x_26, 5, x_13);
lean_closure_set(x_26, 6, x_6);
lean_closure_set(x_26, 7, x_7);
lean_closure_set(x_26, 8, x_19);
lean_closure_set(x_26, 9, x_22);
lean_closure_set(x_26, 10, x_8);
lean_inc(x_10);
x_27 = l___private_Lean_Elab_Command_2__getState(x_10, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l___private_Lean_Elab_Command_9__getVarDecls(x_28);
lean_dec(x_28);
lean_inc(x_10);
x_31 = l___private_Lean_Elab_Command_2__getState(x_10, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Elab_Command_6__mkTermContext(x_10, x_32, x_24);
x_35 = l___private_Lean_Elab_Command_7__mkTermState(x_32);
lean_dec(x_32);
x_36 = l_Lean_Elab_Term_elabBinders___rarg(x_30, x_26, x_34, x_35);
lean_dec(x_30);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
lean_inc(x_10);
x_38 = l___private_Lean_Elab_Command_2__getState(x_10, x_33);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_ctor_get(x_37, 2);
lean_inc(x_43);
lean_dec(x_37);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_dec(x_45);
x_46 = lean_ctor_get(x_40, 0);
lean_dec(x_46);
lean_ctor_set(x_40, 1, x_43);
lean_ctor_set(x_40, 0, x_42);
x_47 = l___private_Lean_Elab_Command_3__setState(x_40, x_10, x_41);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_40, 2);
x_59 = lean_ctor_get(x_40, 3);
x_60 = lean_ctor_get(x_40, 4);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_40);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_42);
lean_ctor_set(x_61, 1, x_43);
lean_ctor_set(x_61, 2, x_58);
lean_ctor_set(x_61, 3, x_59);
lean_ctor_set(x_61, 4, x_60);
x_62 = l___private_Lean_Elab_Command_3__setState(x_61, x_10, x_41);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_69 = x_62;
} else {
 lean_dec_ref(x_62);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_37);
lean_dec(x_10);
x_71 = !lean_is_exclusive(x_38);
if (x_71 == 0)
{
return x_38;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_38, 0);
x_73 = lean_ctor_get(x_38, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_38);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_36, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_36, 1);
lean_inc(x_76);
lean_dec(x_36);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_10);
x_78 = l___private_Lean_Elab_Command_2__getState(x_10, x_33);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_79 = lean_ctor_get(x_76, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_ctor_get(x_76, 2);
lean_inc(x_83);
lean_dec(x_76);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_80, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_80, 0);
lean_dec(x_86);
lean_ctor_set(x_80, 1, x_83);
lean_ctor_set(x_80, 0, x_82);
x_87 = l___private_Lean_Elab_Command_3__setState(x_80, x_10, x_81);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
lean_ctor_set_tag(x_87, 1);
lean_ctor_set(x_87, 0, x_77);
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_77);
x_92 = !lean_is_exclusive(x_87);
if (x_92 == 0)
{
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_ctor_get(x_80, 2);
x_97 = lean_ctor_get(x_80, 3);
x_98 = lean_ctor_get(x_80, 4);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_80);
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_82);
lean_ctor_set(x_99, 1, x_83);
lean_ctor_set(x_99, 2, x_96);
lean_ctor_set(x_99, 3, x_97);
lean_ctor_set(x_99, 4, x_98);
x_100 = l___private_Lean_Elab_Command_3__setState(x_99, x_10, x_81);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
 lean_ctor_set_tag(x_103, 1);
}
lean_ctor_set(x_103, 0, x_77);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_77);
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_106 = x_100;
} else {
 lean_dec_ref(x_100);
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
else
{
uint8_t x_108; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_10);
x_108 = !lean_is_exclusive(x_78);
if (x_108 == 0)
{
return x_78;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_78, 0);
x_110 = lean_ctor_get(x_78, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_78);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_36);
x_112 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_113 = l_unreachable_x21___rarg(x_112);
x_114 = lean_apply_2(x_113, x_10, x_33);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
lean_dec(x_116);
x_117 = lean_box(0);
lean_ctor_set(x_114, 0, x_117);
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_114);
if (x_121 == 0)
{
return x_114;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_114, 0);
x_123 = lean_ctor_get(x_114, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_114);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_10);
x_125 = !lean_is_exclusive(x_31);
if (x_125 == 0)
{
return x_31;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_31, 0);
x_127 = lean_ctor_get(x_31, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_31);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_10);
x_129 = !lean_is_exclusive(x_27);
if (x_129 == 0)
{
return x_27;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_27, 0);
x_131 = lean_ctor_get(x_27, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_27);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_133 = !lean_is_exclusive(x_21);
if (x_133 == 0)
{
return x_21;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_21, 0);
x_135 = lean_ctor_get(x_21, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_21);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_18);
if (x_137 == 0)
{
return x_18;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_18, 0);
x_139 = lean_ctor_get(x_18, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_18);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_141 = !lean_is_exclusive(x_15);
if (x_141 == 0)
{
return x_15;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_15, 0);
x_143 = lean_ctor_get(x_15, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_15);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = !lean_is_exclusive(x_12);
if (x_145 == 0)
{
return x_12;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_12, 0);
x_147 = lean_ctor_get(x_12, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_12);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
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
lean_closure_set(x_30, 2, x_2);
lean_closure_set(x_30, 3, x_27);
lean_closure_set(x_30, 4, x_29);
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
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Elab_Command_elabStructure___lambda__3(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
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
l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1 = _init_l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_1__defaultCtorName___closed__1);
l___private_Lean_Elab_Structure_1__defaultCtorName = _init_l___private_Lean_Elab_Structure_1__defaultCtorName();
lean_mark_persistent(l___private_Lean_Elab_Structure_1__defaultCtorName);
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
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__4 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__4();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__4);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__5 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__5();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__1___closed__5);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__1);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__2);
l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3 = _init_l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3();
lean_mark_persistent(l_Array_iterateMAux___main___at___private_Lean_Elab_Structure_3__expandFields___spec__2___closed__3);
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
l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__1 = _init_l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__1);
l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__2 = _init_l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__2);
l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__3 = _init_l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_23__elabStructureView___lambda__1___closed__3);
l___private_Lean_Elab_Structure_23__elabStructureView___closed__1 = _init_l___private_Lean_Elab_Structure_23__elabStructureView___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Structure_23__elabStructureView___closed__1);
l___private_Lean_Elab_Structure_23__elabStructureView___closed__2 = _init_l___private_Lean_Elab_Structure_23__elabStructureView___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Structure_23__elabStructureView___closed__2);
l___private_Lean_Elab_Structure_23__elabStructureView___closed__3 = _init_l___private_Lean_Elab_Structure_23__elabStructureView___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Structure_23__elabStructureView___closed__3);
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
