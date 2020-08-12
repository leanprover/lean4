// Lean compiler output
// Module: Lean.Elab.Inductive
// Imports: Init Lean.Util.ReplaceLevel Lean.Util.ReplaceExpr Lean.Util.CollectLevelParams Lean.Util.Constructions Lean.Elab.Command Lean.Elab.CollectFVars Lean.Elab.Definition
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
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__5;
lean_object* l_Lean_Elab_Term_getLevelNames(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__3;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_prod_x3f___closed__2;
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__6;
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__5;
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__15;
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3;
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassExpensive___main(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__4;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_26__withUsed(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_2__checkNumParams(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_InductiveView_inhabited;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForall(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_inhabited___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3;
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClassQuick___main(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Lean_Elab_Inductive_16__elabCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__7;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls(lean_object*);
lean_object* l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* lean_dbg_trace(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_6__mkTermContext(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_27__updateParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_24__traceIndTypes(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__10;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at___private_Lean_MetavarContext_2__visit___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabInductiveViews___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___closed__1;
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_3__setState(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_26__withUsed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_ElabHeaderResult_inhabited;
lean_object* l___private_Lean_Elab_Inductive_32__applyInferMod___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2;
lean_object* l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_29__mkIndFVar2Const___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main___closed__1;
lean_object* l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__9;
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__14;
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__10;
lean_object* l___private_Lean_Elab_Inductive_25__removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__8;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main___closed__2;
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9;
lean_object* l___private_Lean_Elab_Term_3__fromMetaState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_ibelow(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_whnf(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_CtorView_inhabited;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__7;
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1;
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6;
lean_object* l_Lean_Elab_Term_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Inhabited___closed__2;
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_3__checkUnsafe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_dbgTrace___rarg___closed__1;
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getLevelOffset___main(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6;
lean_object* l___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabInductiveViews___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isParam(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_16__elabCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_below(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DepElim_getUnusedLevelParam___closed__1;
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevel(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux(lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam___closed__2;
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_isType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_2__checkNumParams___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_5__mkTypeFor(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__2;
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Meta_addGlobalInstance___spec__1(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam___closed__1;
extern lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_29__mkIndFVar2Const(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__12;
lean_object* l_Lean_Elab_Term_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_22__collectUniverses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1;
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_33__mkInductiveDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__11;
lean_object* lean_mk_brec_on(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_22__collectUniverses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermAux___main(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3;
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux___main(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* lean_expr_dbg_to_string(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1;
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__3;
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1;
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__6;
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux___boxed(lean_object*);
lean_object* lean_mk_no_confusion(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__5;
lean_object* l_Lean_Meta_mkFreshId___rarg(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_31__mkCtor2InferMod___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2;
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___main___at___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerClassAttr___closed__2;
lean_object* l___private_Lean_Elab_Inductive_10__checkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4;
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__2;
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_2__getState(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_29__mkIndFVar2Const___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_31__mkCtor2InferMod(lean_object*);
lean_object* lean_mk_binduction_on(lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l_Lean_Elab_Term_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Inductive_27__updateParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4;
lean_object* lean_local_ctx_mk_local_decl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__1;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__1;
uint8_t l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
uint8_t l_Lean_BinderInfo_beq(uint8_t, uint8_t);
lean_object* l___private_Lean_Elab_Inductive_4__checkLevelNames(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at___private_Lean_MetavarContext_2__visit___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__4;
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Command_7__mkTermState(lean_object*);
uint8_t l_Lean_Level_occurs___main(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam___boxed(lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
lean_object* l_List_foldl___main___at___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_InductiveView_inhabited___closed__1;
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__9;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam___closed__3;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1;
extern uint8_t l_Bool_Inhabited;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1;
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__8;
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
extern lean_object* l_Std_HashMap_find_x21___rarg___closed__1;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__6;
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__11;
extern lean_object* l_Lean_Elab_Command_Attribute_inhabited;
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_29__mkIndFVar2Const___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__2;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__8;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__7;
lean_object* l___private_Lean_Elab_Command_8__getVarDecls(lean_object*);
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_12__elabHeader(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__2;
lean_object* l_Lean_Elab_Command_getEnv(lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__9;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_rec_on(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2;
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__1;
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_Elab_Command_CtorView_inhabited___closed__1;
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__4;
lean_object* l_Lean_Elab_Command_CtorView_inhabited___closed__2;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_32__applyInferMod(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_replace___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_11__instantiateForallAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__13;
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__3;
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__5;
lean_object* l_Lean_Expr_inferImplicit___main(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__6;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_4__checkLevelNames___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Level_mkNaryMax___main(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8;
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_26__withUsed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Elab_Term_2__fromMetaException(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateLevelMVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam;
lean_object* l_Std_HashMapImp_insert___at_Lean_ClassState_addEntry___spec__6(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_CollectLevelParams_main___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
lean_object* l___private_Lean_Elab_Inductive_25__removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_mkForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__12;
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5;
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5;
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_33__mkInductiveDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3;
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_3__checkUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in inductive declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in inductive declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in inductive declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_8, x_9);
if (x_5 == 0)
{
uint8_t x_53; 
x_53 = 0;
x_11 = x_53;
goto block_52;
}
else
{
uint8_t x_54; 
x_54 = 1;
x_11 = x_54;
goto block_52;
}
block_52:
{
uint8_t x_12; 
if (x_6 == 0)
{
uint8_t x_50; 
x_50 = 0;
x_12 = x_50;
goto block_49;
}
else
{
uint8_t x_51; 
x_51 = 1;
x_12 = x_51;
goto block_49;
}
block_49:
{
uint8_t x_13; 
if (x_10 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_dec_eq(x_8, x_41);
lean_dec(x_8);
if (x_42 == 0)
{
x_13 = x_10;
goto block_40;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = l_Lean_Elab_Command_Attribute_inhabited;
x_44 = lean_array_get(x_43, x_7, x_9);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_registerClassAttr___closed__2;
x_47 = lean_name_eq(x_45, x_46);
lean_dec(x_45);
x_13 = x_47;
goto block_40;
}
}
else
{
uint8_t x_48; 
lean_dec(x_8);
x_48 = 1;
x_13 = x_48;
goto block_40;
}
block_40:
{
uint8_t x_14; 
if (x_13 == 0)
{
uint8_t x_38; 
x_38 = 0;
x_14 = x_38;
goto block_37;
}
else
{
uint8_t x_39; 
x_39 = 1;
x_14 = x_39;
goto block_37;
}
block_37:
{
lean_object* x_15; 
if (x_11 == 0)
{
x_15 = x_4;
goto block_30;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__9;
x_32 = l_Lean_Elab_Command_throwError___rarg(x_1, x_31, x_3, x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_32);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
block_30:
{
if (x_12 == 0)
{
if (x_14 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__3;
x_17 = l_Lean_Elab_Command_throwError___rarg(x_1, x_16, x_3, x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_15);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__6;
x_25 = l_Lean_Elab_Command_throwError___rarg(x_1, x_24, x_3, x_15);
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
}
}
}
}
}
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidInductiveModifier(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in constructor declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'unsafe' in constructor declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in constructor declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in constructor declaration");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 3);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_9);
if (x_5 == 0)
{
uint8_t x_58; 
x_58 = 0;
x_12 = x_58;
goto block_57;
}
else
{
uint8_t x_59; 
x_59 = 1;
x_12 = x_59;
goto block_57;
}
block_57:
{
uint8_t x_13; 
if (x_6 == 0)
{
uint8_t x_55; 
x_55 = 0;
x_13 = x_55;
goto block_54;
}
else
{
uint8_t x_56; 
x_56 = 1;
x_13 = x_56;
goto block_54;
}
block_54:
{
uint8_t x_14; 
if (x_7 == 0)
{
uint8_t x_52; 
x_52 = 0;
x_14 = x_52;
goto block_51;
}
else
{
uint8_t x_53; 
x_53 = 1;
x_14 = x_53;
goto block_51;
}
block_51:
{
uint8_t x_15; 
if (x_11 == 0)
{
uint8_t x_49; 
x_49 = 1;
x_15 = x_49;
goto block_48;
}
else
{
uint8_t x_50; 
x_50 = 0;
x_15 = x_50;
goto block_48;
}
block_48:
{
uint8_t x_16; 
if (x_15 == 0)
{
uint8_t x_46; 
x_46 = 0;
x_16 = x_46;
goto block_45;
}
else
{
uint8_t x_47; 
x_47 = 1;
x_16 = x_47;
goto block_45;
}
block_45:
{
lean_object* x_17; 
if (x_12 == 0)
{
if (x_13 == 0)
{
x_17 = x_4;
goto block_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Elab_Command_checkValidCtorModifier___closed__9;
x_34 = l_Lean_Elab_Command_throwError___rarg(x_1, x_33, x_3, x_4);
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
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_39 = l_Lean_Elab_Command_checkValidCtorModifier___closed__12;
x_40 = l_Lean_Elab_Command_throwError___rarg(x_1, x_39, x_3, x_4);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
block_32:
{
if (x_14 == 0)
{
if (x_16 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_Elab_Command_checkValidCtorModifier___closed__3;
x_21 = l_Lean_Elab_Command_throwError___rarg(x_1, x_20, x_3, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = l_Lean_Elab_Command_checkValidCtorModifier___closed__6;
x_27 = l_Lean_Elab_Command_throwError___rarg(x_1, x_26, x_3, x_17);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
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
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidCtorModifier(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_CtorView_inhabited___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
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
lean_object* _init_l_Lean_Elab_Command_CtorView_inhabited___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Command_CtorView_inhabited___closed__1;
x_4 = 0;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*5, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Elab_Command_CtorView_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_CtorView_inhabited___closed__2;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_InductiveView_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Command_CtorView_inhabited___closed__1;
x_5 = lean_box(0);
x_6 = l_Array_empty___closed__1;
x_7 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_3);
lean_ctor_set(x_7, 6, x_1);
lean_ctor_set(x_7, 7, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_Elab_Command_InductiveView_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_InductiveView_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_InductiveView_inhabited___closed__1;
x_2 = l_Lean_LocalContext_Inhabited___closed__2;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Expr_Inhabited___closed__1;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_ElabHeaderResult_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, resultant type is not a sort");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_Elab_Term_getLCtx(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Elab_Term_getLocalInsts(x_6, x_10);
x_12 = lean_ctor_get(x_1, 6);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_inc(x_6);
x_16 = l_Lean_Elab_Term_mkFreshLevelMVar(x_15, x_6, x_14);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_mkLevelSucc(x_17);
x_20 = l_Lean_mkSort(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_2, x_21);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_9);
lean_ctor_set(x_23, 2, x_13);
lean_ctor_set(x_23, 3, x_5);
lean_ctor_set(x_23, 4, x_20);
x_24 = lean_array_push(x_3, x_23);
x_25 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(x_4, x_22, x_24, x_6, x_18);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_dec(x_11);
x_28 = lean_ctor_get(x_12, 0);
lean_inc(x_28);
lean_dec(x_12);
x_29 = lean_box(0);
x_30 = 1;
lean_inc(x_6);
lean_inc(x_28);
x_31 = l_Lean_Elab_Term_elabTermAux___main(x_29, x_30, x_30, x_28, x_6, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_2, x_35);
lean_inc(x_32);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_9);
lean_ctor_set(x_37, 2, x_26);
lean_ctor_set(x_37, 3, x_5);
lean_ctor_set(x_37, 4, x_32);
x_38 = lean_array_push(x_3, x_37);
lean_inc(x_6);
x_39 = l_Lean_Elab_Term_isTypeFormerType(x_34, x_32, x_6, x_33);
lean_dec(x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_4);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3;
x_44 = l_Lean_Elab_Term_throwError___rarg(x_28, x_43, x_6, x_42);
lean_dec(x_28);
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
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_28);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
lean_dec(x_39);
x_50 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(x_4, x_36, x_38, x_6, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_4);
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
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_31);
if (x_55 == 0)
{
return x_31;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_31, 0);
x_57 = lean_ctor_get(x_31, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_31);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_ctor_get(x_9, 5);
lean_inc(x_10);
x_11 = l_Lean_Syntax_getArgs(x_10);
lean_dec(x_10);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___boxed), 7, 4);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_1);
x_13 = l_Lean_Elab_Term_elabBinders___rarg(x_11, x_12, x_4, x_5);
lean_dec(x_11);
return x_13;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Inductive_1__elabHeaderAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, number of parameters mismatch in mutually inductive datatypes");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 3);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
lean_dec(x_13);
x_15 = lean_nat_dec_eq(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_12);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3;
x_19 = l_Lean_Elab_Term_throwError___rarg(x_17, x_18, x_4, x_5);
lean_dec(x_17);
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
lean_dec(x_10);
x_3 = x_12;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_2__checkNumParams(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get(x_4, x_1, x_5);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
lean_dec(x_7);
x_9 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1(x_8, x_1, x_5, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_9);
if (x_14 == 0)
{
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 0);
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_9);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Inductive_2__checkNumParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_2__checkNumParams(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, cannot mix unsafe and safe declarations in a mutually inductive datatypes");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*2 + 3);
lean_dec(x_14);
if (x_15 == 0)
{
if (x_1 == 0)
{
uint8_t x_26; 
x_26 = 1;
x_16 = x_26;
goto block_25;
}
else
{
uint8_t x_27; 
x_27 = 0;
x_16 = x_27;
goto block_25;
}
}
else
{
if (x_1 == 0)
{
uint8_t x_28; 
x_28 = 0;
x_16 = x_28;
goto block_25;
}
else
{
uint8_t x_29; 
x_29 = 1;
x_16 = x_29;
goto block_25;
}
}
block_25:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_12);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3;
x_19 = l_Lean_Elab_Term_throwError___rarg(x_17, x_18, x_4, x_5);
lean_dec(x_17);
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
lean_dec(x_13);
x_3 = x_12;
goto _start;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_3__checkUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get(x_4, x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*2 + 3);
lean_dec(x_8);
x_10 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1(x_9, x_1, x_5, x_2, x_3);
return x_10;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_3__checkUnsafe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_3__checkUnsafe(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, universe parameters mismatch in mutually inductive datatypes");
return x_1;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 4);
lean_inc(x_13);
x_14 = l_List_beq___main___at_Lean_Elab_OpenDecl_HasToString___spec__1(x_13, x_1);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3;
x_17 = l_Lean_Elab_Term_throwError___rarg(x_15, x_16, x_4, x_5);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_dec(x_10);
x_3 = x_12;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_4__checkLevelNames(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_lt(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Elab_Command_InductiveView_inhabited;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_1, x_10);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1(x_12, x_1, x_10, x_2, x_3);
lean_dec(x_12);
return x_13;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Inductive_4__checkLevelNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_4__checkLevelNames(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Inductive_5__mkTypeFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Term_mkForall___boxed), 5, 3);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_Elab_Term_withLocalContext___rarg(x_4, x_5, x_10, x_2, x_3);
return x_11;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected inductive resulting type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3;
x_5 = l_Lean_Elab_Term_throwError___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 4);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_5, 4, x_9);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
x_11 = l_Lean_Meta_forallTelescopeReducing___rarg(x_2, x_10, x_8, x_5);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_13, x_7);
lean_ctor_set(x_11, 1, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_11);
x_17 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_16, x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_3);
x_22 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_20);
x_23 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_21, x_7);
lean_ctor_set(x_11, 1, x_23);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
lean_inc(x_3);
x_26 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_24);
x_27 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_25, x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 2);
x_32 = lean_ctor_get(x_5, 3);
x_33 = lean_ctor_get(x_5, 4);
x_34 = lean_ctor_get(x_5, 5);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = l_Lean_TraceState_Inhabited___closed__1;
x_37 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_37, 0, x_29);
lean_ctor_set(x_37, 1, x_30);
lean_ctor_set(x_37, 2, x_31);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_34);
x_38 = l_Array_iterateM_u2082Aux___main___at_Lean_PrettyPrinter_Parenthesizer_compileParserBody___main___spec__3___closed__1;
x_39 = l_Lean_Meta_forallTelescopeReducing___rarg(x_2, x_38, x_35, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
x_43 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_41, x_33);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_47 = x_39;
} else {
 lean_dec_ref(x_39);
 x_47 = lean_box(0);
}
lean_inc(x_3);
x_48 = l___private_Lean_Elab_Term_2__fromMetaException(x_3, x_1, x_45);
x_49 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_3, x_4, x_46, x_33);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_7__getResultingType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Inductive_7__getResultingType(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_isExprDefEq(x_3, x_1, x_4, x_5);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1___boxed), 5, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_expr_instantiate1(x_1, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
x_12 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main(x_3, x_4, x_11, x_9, x_5, x_7, x_8);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_expr_instantiate1(x_1, x_6);
x_10 = lean_expr_instantiate1(x_2, x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
x_13 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main(x_4, x_5, x_12, x_9, x_10, x_7, x_8);
return x_13;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutually inductive types, resulting universe mismatch, given ");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("expected type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutually inductive types, binder annotation mismatch at parameter '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutually inductive types, type mismatch at parameter '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__10;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutually inductive types, parameter name mismatch '");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
x_8 = l_Lean_Elab_Term_whnf(x_1, x_4, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_nat_dec_lt(x_3, x_2);
if (x_11 == 0)
{
switch (lean_obj_tag(x_9)) {
case 3:
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
x_16 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_12, 4, x_16);
lean_inc(x_9);
lean_inc(x_5);
x_17 = l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult(x_5, x_9, x_15, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_6);
x_21 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_6, x_10, x_20, x_14);
x_22 = lean_unbox(x_19);
lean_dec(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_free_object(x_17);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_9);
x_24 = l_Lean_indentExpr(x_23);
x_25 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__3;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_MessageData_ofList___closed__3;
x_28 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__6;
x_30 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_5);
x_32 = l_Lean_indentExpr(x_31);
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Elab_Term_throwError___rarg(x_1, x_33, x_6, x_21);
lean_dec(x_1);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_17, 1, x_21);
lean_ctor_set(x_17, 0, x_35);
return x_17;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
lean_inc(x_6);
x_38 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_6, x_10, x_37, x_14);
x_39 = lean_unbox(x_36);
lean_dec(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_9);
x_41 = l_Lean_indentExpr(x_40);
x_42 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__3;
x_43 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Lean_MessageData_ofList___closed__3;
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__6;
x_47 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_48, 0, x_5);
x_49 = l_Lean_indentExpr(x_48);
x_50 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Elab_Term_throwError___rarg(x_1, x_50, x_6, x_38);
lean_dec(x_1);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_38);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_17, 0);
x_56 = lean_ctor_get(x_17, 1);
lean_inc(x_6);
x_57 = l___private_Lean_Elab_Term_2__fromMetaException(x_6, x_1, x_55);
x_58 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_6, x_10, x_56, x_14);
lean_dec(x_1);
lean_ctor_set(x_17, 1, x_58);
lean_ctor_set(x_17, 0, x_57);
return x_17;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_17, 0);
x_60 = lean_ctor_get(x_17, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_17);
lean_inc(x_6);
x_61 = l___private_Lean_Elab_Term_2__fromMetaException(x_6, x_1, x_59);
x_62 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_6, x_10, x_60, x_14);
lean_dec(x_1);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_64 = lean_ctor_get(x_12, 0);
x_65 = lean_ctor_get(x_12, 1);
x_66 = lean_ctor_get(x_12, 2);
x_67 = lean_ctor_get(x_12, 3);
x_68 = lean_ctor_get(x_12, 4);
x_69 = lean_ctor_get(x_12, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_12);
x_70 = lean_ctor_get(x_6, 0);
lean_inc(x_70);
x_71 = l_Lean_TraceState_Inhabited___closed__1;
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_64);
lean_ctor_set(x_72, 1, x_65);
lean_ctor_set(x_72, 2, x_66);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set(x_72, 5, x_69);
lean_inc(x_9);
lean_inc(x_5);
x_73 = l___private_Lean_Elab_Inductive_8__eqvFirstTypeResult(x_5, x_9, x_70, x_72);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
lean_inc(x_6);
x_77 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_6, x_10, x_75, x_68);
x_78 = lean_unbox(x_74);
lean_dec(x_74);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_76);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_9);
x_80 = l_Lean_indentExpr(x_79);
x_81 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__3;
x_82 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
x_83 = l_Lean_MessageData_ofList___closed__3;
x_84 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__6;
x_86 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_87, 0, x_5);
x_88 = l_Lean_indentExpr(x_87);
x_89 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Elab_Term_throwError___rarg(x_1, x_89, x_6, x_77);
lean_dec(x_1);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_91 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_76;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_77);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_9);
lean_dec(x_5);
x_93 = lean_ctor_get(x_73, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_73, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_95 = x_73;
} else {
 lean_dec_ref(x_73);
 x_95 = lean_box(0);
}
lean_inc(x_6);
x_96 = l___private_Lean_Elab_Term_2__fromMetaException(x_6, x_1, x_93);
x_97 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_6, x_10, x_94, x_68);
lean_dec(x_1);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint64_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_9, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_9, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_9, 2);
lean_inc(x_101);
x_102 = lean_ctor_get_uint64(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_103 = (uint8_t)((x_102 << 24) >> 61);
lean_inc(x_1);
x_104 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__1___boxed), 8, 5);
lean_closure_set(x_104, 0, x_101);
lean_closure_set(x_104, 1, x_3);
lean_closure_set(x_104, 2, x_1);
lean_closure_set(x_104, 3, x_2);
lean_closure_set(x_104, 4, x_5);
x_105 = l_Lean_Elab_Term_withLocalDecl___rarg(x_1, x_99, x_103, x_100, x_104, x_6, x_10);
lean_dec(x_1);
return x_105;
}
default: 
{
lean_object* x_106; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_106 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg(x_1, x_6, x_10);
lean_dec(x_1);
return x_106;
}
}
}
else
{
lean_object* x_107; 
lean_inc(x_6);
x_107 = l_Lean_Elab_Term_whnf(x_1, x_5, x_6, x_10);
if (lean_obj_tag(x_107) == 0)
{
if (lean_obj_tag(x_9) == 7)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 7)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint64_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint64_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; 
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_9, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_9, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_9, 2);
lean_inc(x_112);
x_113 = lean_ctor_get_uint64(x_9, sizeof(void*)*3);
lean_dec(x_9);
x_114 = lean_ctor_get(x_108, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_108, 1);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 2);
lean_inc(x_116);
x_117 = lean_ctor_get_uint64(x_108, sizeof(void*)*3);
lean_dec(x_108);
x_118 = lean_name_eq(x_110, x_114);
x_119 = (uint8_t)((x_113 << 24) >> 61);
x_120 = (uint8_t)((x_117 << 24) >> 61);
x_121 = l_Lean_BinderInfo_beq(x_119, x_120);
lean_inc(x_1);
x_122 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__2___boxed), 8, 5);
lean_closure_set(x_122, 0, x_112);
lean_closure_set(x_122, 1, x_116);
lean_closure_set(x_122, 2, x_3);
lean_closure_set(x_122, 3, x_1);
lean_closure_set(x_122, 4, x_2);
if (x_118 == 0)
{
uint8_t x_187; 
x_187 = 0;
x_123 = x_187;
goto block_186;
}
else
{
uint8_t x_188; 
x_188 = 1;
x_123 = x_188;
goto block_186;
}
block_186:
{
uint8_t x_124; 
if (x_121 == 0)
{
uint8_t x_184; 
x_184 = 0;
x_124 = x_184;
goto block_183;
}
else
{
uint8_t x_185; 
x_185 = 1;
x_124 = x_185;
goto block_183;
}
block_183:
{
lean_object* x_125; lean_object* x_138; 
if (x_123 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_111);
x_169 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_169, 0, x_110);
x_170 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__15;
x_171 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Lean_PrettyPrinter_Parenthesizer_node_parenthesizer___closed__8;
x_173 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_174, 0, x_114);
x_175 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_177 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lean_Elab_Term_throwError___rarg(x_1, x_177, x_6, x_109);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
return x_178;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_178, 0);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_178);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
else
{
lean_dec(x_114);
x_138 = x_109;
goto block_168;
}
block_137:
{
if (x_124 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_122);
lean_dec(x_111);
x_126 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_126, 0, x_110);
x_127 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__9;
x_128 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_126);
x_129 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_130 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lean_Elab_Term_throwError___rarg(x_1, x_130, x_6, x_125);
lean_dec(x_1);
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
x_136 = l_Lean_Elab_Term_withLocalDecl___rarg(x_1, x_110, x_119, x_111, x_122, x_6, x_125);
lean_dec(x_1);
return x_136;
}
}
block_168:
{
lean_object* x_139; 
lean_inc(x_6);
lean_inc(x_115);
lean_inc(x_111);
x_139 = l_Lean_Elab_Term_isDefEq(x_1, x_111, x_115, x_6, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
lean_dec(x_122);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_143, 0, x_110);
x_144 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__12;
x_145 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l___private_Lean_Meta_RecursorInfo_5__getMajorPosDepElim___closed__5;
x_147 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_148, 0, x_111);
x_149 = l_Lean_indentExpr(x_148);
x_150 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_MessageData_ofList___closed__3;
x_152 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_153 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__6;
x_154 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_155, 0, x_115);
x_156 = l_Lean_indentExpr(x_155);
x_157 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_Elab_Term_throwError___rarg(x_1, x_157, x_6, x_142);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
return x_158;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_158, 0);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_158);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
else
{
lean_object* x_163; 
lean_dec(x_115);
x_163 = lean_ctor_get(x_139, 1);
lean_inc(x_163);
lean_dec(x_139);
x_125 = x_163;
goto block_137;
}
}
else
{
uint8_t x_164; 
lean_dec(x_122);
lean_dec(x_115);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_6);
lean_dec(x_1);
x_164 = !lean_is_exclusive(x_139);
if (x_164 == 0)
{
return x_139;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_139, 0);
x_166 = lean_ctor_get(x_139, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_139);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_108);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_189 = lean_ctor_get(x_107, 1);
lean_inc(x_189);
lean_dec(x_107);
x_190 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg(x_1, x_6, x_189);
lean_dec(x_1);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_191 = lean_ctor_get(x_107, 1);
lean_inc(x_191);
lean_dec(x_107);
x_192 = l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg(x_1, x_6, x_191);
lean_dec(x_1);
return x_192;
}
}
else
{
uint8_t x_193; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_193 = !lean_is_exclusive(x_107);
if (x_193 == 0)
{
return x_107;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_107, 0);
x_195 = lean_ctor_get(x_107, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_107);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_8);
if (x_197 == 0)
{
return x_8;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_8, 0);
x_199 = lean_ctor_get(x_8, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_8);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_9__checkParamsAndResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Inductive_10__checkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = l___private_Lean_Elab_Inductive_5__mkTypeFor(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
x_17 = l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main(x_15, x_2, x_16, x_11, x_13, x_4, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_13);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_6);
if (x_26 == 0)
{
return x_6;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_6);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_12 = lean_array_get(x_11, x_1, x_3);
lean_inc(x_5);
lean_inc(x_2);
x_13 = l___private_Lean_Elab_Inductive_10__checkHeader(x_12, x_2, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_3, x_16);
lean_dec(x_3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_3 = x_17;
x_4 = x_18;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Inductive_11__checkHeaders___main(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Inductive_11__checkHeaders___main(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_11__checkHeaders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Inductive_11__checkHeaders(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_12__elabHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_empty___closed__1;
lean_inc(x_2);
x_6 = l___private_Lean_Elab_Inductive_1__elabHeaderAux___main(x_1, x_4, x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_array_get_size(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_dec_lt(x_11, x_10);
lean_dec(x_10);
if (x_12 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_13; 
lean_free_object(x_6);
lean_inc(x_2);
x_13 = l___private_Lean_Elab_Inductive_3__checkUnsafe(x_8, x_2, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_2);
x_15 = l___private_Lean_Elab_Inductive_2__checkNumParams(x_8, x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = l___private_Lean_Elab_Inductive_11__checkHeaders___main(x_8, x_16, x_4, x_18, x_2, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_8);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_8);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
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
lean_dec(x_8);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
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
lean_dec(x_8);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
x_38 = lean_array_get_size(x_36);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_dec_lt(x_39, x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
else
{
lean_object* x_42; 
lean_inc(x_2);
x_42 = l___private_Lean_Elab_Inductive_3__checkUnsafe(x_36, x_2, x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_2);
x_44 = l___private_Lean_Elab_Inductive_2__checkNumParams(x_36, x_2, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
x_48 = l___private_Lean_Elab_Inductive_11__checkHeaders___main(x_36, x_45, x_4, x_47, x_2, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_36);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_36);
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_54 = x_48;
} else {
 lean_dec_ref(x_48);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_36);
lean_dec(x_2);
x_56 = lean_ctor_get(x_44, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_58 = x_44;
} else {
 lean_dec_ref(x_44);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_36);
lean_dec(x_2);
x_60 = lean_ctor_get(x_42, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_62 = x_42;
} else {
 lean_dec_ref(x_42);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_6);
if (x_64 == 0)
{
return x_6;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_6, 0);
x_66 = lean_ctor_get(x_6, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_6);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
x_12 = lean_array_push(x_2, x_7);
x_13 = l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(x_3, x_4, x_5, x_6, x_11, x_12, x_8, x_9);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_apply_4(x_4, x_3, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_array_fget(x_2, x_5);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_13, 4);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
x_19 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_13, 4, x_19);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Meta_Basic_11__instantiateForallAux___main(x_3, x_20, x_15, x_18, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_7);
x_24 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_7, x_8, x_23, x_17);
lean_inc(x_1);
x_25 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1___boxed), 9, 6);
lean_closure_set(x_25, 0, x_5);
lean_closure_set(x_25, 1, x_6);
lean_closure_set(x_25, 2, x_1);
lean_closure_set(x_25, 3, x_2);
lean_closure_set(x_25, 4, x_3);
lean_closure_set(x_25, 5, x_4);
x_26 = 0;
x_27 = l_Lean_Elab_Term_withLocalDecl___rarg(x_1, x_14, x_26, x_22, x_25, x_7, x_24);
lean_dec(x_1);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_7);
x_31 = l___private_Lean_Elab_Term_2__fromMetaException(x_7, x_1, x_29);
x_32 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_7, x_8, x_30, x_17);
lean_dec(x_1);
lean_ctor_set(x_21, 1, x_32);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
lean_inc(x_7);
x_35 = l___private_Lean_Elab_Term_2__fromMetaException(x_7, x_1, x_33);
x_36 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_7, x_8, x_34, x_17);
lean_dec(x_1);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_13, 0);
x_39 = lean_ctor_get(x_13, 1);
x_40 = lean_ctor_get(x_13, 2);
x_41 = lean_ctor_get(x_13, 3);
x_42 = lean_ctor_get(x_13, 4);
x_43 = lean_ctor_get(x_13, 5);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_13);
x_44 = lean_ctor_get(x_7, 0);
lean_inc(x_44);
x_45 = l_Lean_TraceState_Inhabited___closed__1;
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_43);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l___private_Lean_Meta_Basic_11__instantiateForallAux___main(x_3, x_47, x_15, x_44, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_7);
x_51 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_7, x_8, x_50, x_42);
lean_inc(x_1);
x_52 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1___boxed), 9, 6);
lean_closure_set(x_52, 0, x_5);
lean_closure_set(x_52, 1, x_6);
lean_closure_set(x_52, 2, x_1);
lean_closure_set(x_52, 3, x_2);
lean_closure_set(x_52, 4, x_3);
lean_closure_set(x_52, 5, x_4);
x_53 = 0;
x_54 = l_Lean_Elab_Term_withLocalDecl___rarg(x_1, x_14, x_53, x_49, x_52, x_7, x_51);
lean_dec(x_1);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_inc(x_7);
x_58 = l___private_Lean_Elab_Term_2__fromMetaException(x_7, x_1, x_55);
x_59 = l___private_Lean_Elab_Term_3__fromMetaState(x_1, x_7, x_8, x_56, x_42);
lean_dec(x_1);
if (lean_is_scalar(x_57)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_57;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg), 8, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_2, x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_fset(x_2, x_1, x_10);
x_12 = x_9;
lean_inc(x_3);
lean_inc(x_12);
x_13 = l___private_Lean_Elab_Inductive_5__mkTypeFor(x_12, x_3, x_4);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_1, x_19);
x_21 = x_18;
x_22 = lean_array_fset(x_11, x_1, x_21);
lean_dec(x_1);
x_1 = x_20;
x_2 = x_22;
x_4 = x_15;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_5 = x_1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___spec__1), 4, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = x_7;
lean_inc(x_3);
x_9 = lean_apply_2(x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_13 = lean_array_get(x_12, x_1, x_6);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Array_empty___closed__1;
x_20 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_13__withInductiveLocalDeclsAux___rarg), 8, 6);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_10);
lean_closure_set(x_20, 2, x_14);
lean_closure_set(x_20, 3, x_2);
lean_closure_set(x_20, 4, x_6);
lean_closure_set(x_20, 5, x_19);
x_21 = l_Lean_Elab_Term_withLocalContext___rarg(x_15, x_16, x_20, x_3, x_11);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_inferType(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_whnf(x_1, x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Expr_isSort(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 1;
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
uint8_t x_14; lean_object* x_15; 
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = l_Lean_Expr_isSort(x_16);
lean_dec(x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_19 = 1;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_8);
if (x_25 == 0)
{
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_8, 0);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_8);
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
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
return x_5;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_15__isInductiveFamily___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Inductive_15__isInductiveFamily(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructor resulting type must be specified in inductive family declaration");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor resulting type");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor resulting type, type expected");
return x_1;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_33; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_33 = lean_ctor_get(x_1, 4);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 0)
{
if (x_3 == 0)
{
x_9 = x_4;
x_10 = x_7;
goto block_32;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3;
x_35 = l_Lean_Elab_Term_throwError___rarg(x_8, x_34, x_6, x_7);
lean_dec(x_8);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_box(0);
x_42 = 1;
lean_inc(x_6);
x_43 = l_Lean_Elab_Term_elabTermAux___main(x_41, x_42, x_42, x_40, x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_6);
lean_inc(x_44);
x_46 = l___private_Lean_Elab_Inductive_7__getResultingType(x_8, x_44, x_6, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = l_Lean_Expr_getAppFn___main(x_47);
x_50 = lean_expr_eqv(x_49, x_4);
lean_dec(x_4);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_44);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_47);
x_52 = l_Lean_indentExpr(x_51);
x_53 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6;
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Lean_Elab_Term_throwError___rarg(x_8, x_54, x_6, x_48);
lean_dec(x_8);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
return x_55;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_55);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
lean_object* x_60; 
lean_inc(x_6);
lean_inc(x_47);
x_60 = l_Lean_Elab_Term_isType(x_8, x_47, x_6, x_48);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_unbox(x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_44);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_47);
x_65 = l_Lean_indentExpr(x_64);
x_66 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9;
x_67 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Elab_Term_throwError___rarg(x_8, x_67, x_6, x_63);
lean_dec(x_8);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_dec(x_47);
x_73 = lean_ctor_get(x_60, 1);
lean_inc(x_73);
lean_dec(x_60);
x_9 = x_44;
x_10 = x_73;
goto block_32;
}
}
else
{
uint8_t x_74; 
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_46);
if (x_78 == 0)
{
return x_46;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_46, 0);
x_80 = lean_ctor_get(x_46, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_46);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_43);
if (x_82 == 0)
{
return x_43;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_43, 0);
x_84 = lean_ctor_get(x_43, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_43);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
block_32:
{
lean_object* x_11; 
lean_inc(x_6);
x_11 = l_Lean_Elab_Term_mkForall(x_8, x_5, x_9, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Elab_Term_mkForall(x_8, x_2, x_12, x_6, x_13);
lean_dec(x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_11);
if (x_28 == 0)
{
return x_11;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_13 = l_Lean_Syntax_getArgs(x_12);
lean_dec(x_12);
x_14 = lean_box(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___boxed), 7, 4);
lean_closure_set(x_15, 0, x_10);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_1);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_elabBinders___rarg(x_13, x_15, x_5, x_6);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(x_1, x_2, x_3, x_11, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_17);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_4, 1, x_22);
lean_ctor_set(x_4, 0, x_17);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_free_object(x_4);
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
lean_free_object(x_4);
lean_dec(x_11);
lean_dec(x_5);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_4, 0);
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_4);
x_35 = lean_ctor_get(x_33, 3);
lean_inc(x_35);
x_36 = l_Lean_Syntax_getArgs(x_35);
lean_dec(x_35);
x_37 = lean_box(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_38 = lean_alloc_closure((void*)(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___boxed), 7, 4);
lean_closure_set(x_38, 0, x_33);
lean_closure_set(x_38, 1, x_2);
lean_closure_set(x_38, 2, x_37);
lean_closure_set(x_38, 3, x_1);
lean_inc(x_5);
x_39 = l_Lean_Elab_Term_elabBinders___rarg(x_36, x_38, x_5, x_6);
lean_dec(x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(x_1, x_2, x_3, x_34, x_5, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_43);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_54 = x_39;
} else {
 lean_dec_ref(x_39);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_16__elabCtors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_4);
lean_inc(x_1);
x_8 = l___private_Lean_Elab_Inductive_15__isInductiveFamily(x_7, x_1, x_4, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_6, 7);
x_12 = l_Array_toList___rarg(x_11);
x_13 = lean_unbox(x_9);
lean_dec(x_9);
x_14 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(x_1, x_2, x_13, x_12, x_4, x_10);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1(x_1, x_2, x_8, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l___private_Lean_Elab_Inductive_16__elabCtors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Inductive_16__elabCtors(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_3);
x_13 = l_Lean_Elab_Term_levelMVarToParam_x27(x_12, x_2, x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_9, 1, x_16);
x_18 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_11, x_17, x_3, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_20, 0, x_1);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_1, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_18, 0, x_25);
return x_18;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_28);
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_9, 0);
x_35 = lean_ctor_get(x_9, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_9);
lean_inc(x_3);
x_36 = l_Lean_Elab_Term_levelMVarToParam_x27(x_35, x_2, x_3, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_33, x_40, x_3, x_38);
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
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_48 = x_43;
} else {
 lean_dec_ref(x_43);
 x_48 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_46);
lean_ctor_set(x_1, 0, x_41);
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_47);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_1, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_1);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_55 = x_51;
} else {
 lean_dec_ref(x_51);
 x_55 = lean_box(0);
}
lean_inc(x_3);
x_56 = l_Lean_Elab_Term_levelMVarToParam_x27(x_54, x_2, x_3, x_4);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
if (lean_is_scalar(x_55)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_55;
}
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_59);
x_62 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_52, x_60, x_3, x_58);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_64);
return x_71;
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_3);
x_14 = l_Lean_Elab_Term_levelMVarToParam_x27(x_12, x_2, x_3, x_4);
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
lean_inc(x_3);
x_19 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_13, x_18, x_3, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_9, 2, x_22);
lean_ctor_set(x_9, 1, x_17);
x_24 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_11, x_23, x_3, x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_ctor_set(x_1, 1, x_28);
lean_ctor_set(x_26, 0, x_1);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_26);
lean_ctor_set(x_1, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_24, 0, x_31);
return x_24;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_36 = x_32;
} else {
 lean_dec_ref(x_32);
 x_36 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_34);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_33);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
x_42 = lean_ctor_get(x_9, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
lean_inc(x_3);
x_43 = l_Lean_Elab_Term_levelMVarToParam_x27(x_41, x_2, x_3, x_4);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
lean_inc(x_3);
x_48 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_42, x_47, x_3, x_45);
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
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set(x_53, 2, x_51);
x_54 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_39, x_52, x_3, x_50);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_60 = x_55;
} else {
 lean_dec_ref(x_55);
 x_60 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_53);
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_59);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_56);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_63 = lean_ctor_get(x_1, 0);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_1);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
 x_68 = lean_box(0);
}
lean_inc(x_3);
x_69 = l_Lean_Elab_Term_levelMVarToParam_x27(x_66, x_2, x_3, x_4);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
lean_inc(x_3);
x_74 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__1(x_67, x_73, x_3, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec(x_75);
if (lean_is_scalar(x_68)) {
 x_79 = lean_alloc_ctor(0, 3, 0);
} else {
 x_79 = x_68;
}
lean_ctor_set(x_79, 0, x_65);
lean_ctor_set(x_79, 1, x_72);
lean_ctor_set(x_79, 2, x_77);
x_80 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_64, x_78, x_3, x_76);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_86 = x_81;
} else {
 lean_dec_ref(x_81);
 x_86 = lean_box(0);
}
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_79);
lean_ctor_set(x_87, 1, x_84);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_83)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_83;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_82);
return x_89;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_17__levelMVarToParamAux___rarg), 4, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_17__levelMVarToParamAux___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Inductive_17__levelMVarToParamAux(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_List_mapM___main___at___private_Lean_Elab_Inductive_17__levelMVarToParamAux___spec__2(x_1, x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_18__levelMVarToParam___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_18__levelMVarToParam___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Inductive_18__levelMVarToParam(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected empty inductive declaration");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected inductive type resulting type");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3;
x_6 = l_Lean_Elab_Term_throwError___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_3);
x_9 = l___private_Lean_Elab_Inductive_7__getResultingType(x_1, x_8, x_3, x_4);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 3)
{
uint8_t x_11; 
lean_dec(x_3);
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
x_18 = l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6;
x_19 = l_Lean_Elab_Term_throwError___rarg(x_1, x_18, x_3, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
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
}
lean_object* l___private_Lean_Elab_Inductive_19__getResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Inductive_19__getResultingUniverse(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tmp_ind_univ_param");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_tmpIndParam___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_tmpIndParam___closed__2;
x_2 = l_Lean_mkLevelParam(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_tmpIndParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_tmpIndParam___closed__3;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot infer resulting universe level of inductive datatype, given level contains metavariables ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", provide universe explicitly");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_3);
x_5 = l_Lean_Elab_Term_instantiateLevelMVars(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Level_hasMVar(x_7);
if (x_9 == 0)
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = 0;
x_11 = lean_box(x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; 
lean_free_object(x_5);
x_12 = l_Lean_Level_getLevelOffset___main(x_7);
if (lean_obj_tag(x_12) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Elab_Command_tmpIndParam;
x_15 = l_Lean_Elab_Term_assignLevelMVar(x_13, x_14, x_3, x_8);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
x_24 = l_Lean_mkSort(x_7);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
x_28 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__6;
x_29 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Elab_Term_throwError___rarg(x_1, x_29, x_3, x_8);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_5, 0);
x_32 = lean_ctor_get(x_5, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_5);
x_33 = l_Lean_Level_hasMVar(x_31);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_3);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Level_getLevelOffset___main(x_31);
if (lean_obj_tag(x_37) == 5)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_31);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Elab_Command_tmpIndParam;
x_40 = l_Lean_Elab_Term_assignLevelMVar(x_38, x_39, x_3, x_32);
lean_dec(x_3);
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
x_43 = 1;
x_44 = lean_box(x_43);
if (lean_is_scalar(x_42)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_42;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_37);
x_46 = l_Lean_mkSort(x_31);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__6;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Elab_Term_throwError___rarg(x_1, x_51, x_3, x_32);
return x_52;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_shouldInferResultUniverse(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = lean_level_eq(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_5, x_10);
lean_dec(x_5);
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_5);
return x_9;
}
}
}
}
uint8_t l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2(x_1, x_2, x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Command_accLevelAtCtor___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compute resulting universe level of inductive datatype, provide universe explicitly");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Command_accLevelAtCtor___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_3, x_9);
lean_dec(x_3);
x_1 = x_6;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_3);
x_12 = lean_level_eq(x_1, x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Level_occurs___main(x_2, x_1);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(x_4, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_push(x_4, x_1);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_18 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__2;
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
}
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
lean_inc(x_3);
x_22 = l_Lean_Elab_Command_accLevelAtCtor___main(x_20, x_2, x_3, x_4);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
lean_dec(x_21);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_1 = x_21;
x_4 = x_26;
goto _start;
}
}
default: 
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_3, x_28);
lean_dec(x_3);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Level_occurs___main(x_2, x_1);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(x_4, x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_array_push(x_4, x_1);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_1);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_4);
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_4);
lean_dec(x_1);
x_35 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__2;
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = lean_level_eq(x_1, x_2);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Level_occurs___main(x_2, x_1);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(x_4, x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_array_push(x_4, x_1);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; 
lean_dec(x_1);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_4);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec(x_4);
lean_dec(x_1);
x_42 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__2;
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec(x_1);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_4);
return x_43;
}
}
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_Elab_Command_accLevelAtCtor___main___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_accLevelAtCtor___main(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_accLevelAtCtor___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_accLevelAtCtor(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_expr_instantiate1(x_1, x_7);
x_11 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_2, x_3, x_4, x_5, x_10, x_6, x_8, x_9);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_instantiate1(x_1, x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_2, x_3, x_4, x_10, x_9, x_5, x_7, x_8);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 0)
{
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_4, x_15);
x_17 = (uint8_t)((x_14 << 24) >> 61);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1___boxed), 9, 6);
lean_closure_set(x_18, 0, x_13);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_16);
lean_closure_set(x_18, 5, x_6);
x_19 = l_Lean_Elab_Term_withLocalDecl___rarg(x_1, x_11, x_17, x_12, x_18, x_7, x_8);
lean_dec(x_1);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
}
else
{
if (lean_obj_tag(x_5) == 7)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_5, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_dec(x_5);
lean_inc(x_7);
lean_inc(x_22);
x_25 = l_Lean_Elab_Term_getLevel(x_1, x_22, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_7);
x_28 = l_Lean_Elab_Term_instantiateLevelMVars(x_1, x_26, x_7, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_3);
x_31 = l_Lean_Elab_Command_accLevelAtCtor___main(x_29, x_2, x_3, x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Elab_Term_throwError___rarg(x_1, x_34, x_7, x_30);
lean_dec(x_1);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = (uint8_t)((x_24 << 24) >> 61);
lean_inc(x_1);
x_38 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2___boxed), 8, 5);
lean_closure_set(x_38, 0, x_23);
lean_closure_set(x_38, 1, x_1);
lean_closure_set(x_38, 2, x_2);
lean_closure_set(x_38, 3, x_3);
lean_closure_set(x_38, 4, x_36);
x_39 = l_Lean_Elab_Term_withLocalDecl___rarg(x_1, x_21, x_37, x_22, x_38, x_7, x_30);
lean_dec(x_1);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
return x_25;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_25, 0);
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_25);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_8);
return x_44;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_1, x_2, x_3, x_5, x_4, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_21__collectUniversesFromCtorType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_Inductive_20__collectUniversesFromCtorTypeAux___main(x_1, x_2, x_3, x_4, x_12, x_5, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_5 = x_14;
x_6 = x_11;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_10, 2);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_5 = x_14;
x_6 = x_11;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l___private_Lean_Elab_Inductive_22__collectUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Array_empty___closed__1;
x_9 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2(x_1, x_2, x_3, x_4, x_8, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_22__collectUniverses___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_22__collectUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Inductive_22__collectUniverses(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
return x_8;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Elab_Command_tmpIndParam;
x_4 = lean_level_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Level_replace___main(x_7, x_5);
x_9 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(x_1, x_6);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Level_replace___main(x_12, x_10);
x_14 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_AbstractMVars_abstractExprMVars___main___closed__3;
x_2 = l_Lean_Expr_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; uint8_t x_11; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_ptr_addr(x_3);
x_7 = x_2 == 0 ? 0 : x_6 % x_2;
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_array_uget(x_8, x_7);
x_10 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_11 = x_10 == x_6;
if (x_11 == 0)
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = l_Lean_Level_replace___main(x_5, x_12);
lean_inc(x_3);
x_14 = lean_expr_update_sort(x_3, x_13);
x_15 = lean_array_uset(x_8, x_7, x_3);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_14);
x_17 = lean_array_uset(x_16, x_7, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2(x_1, x_20);
lean_inc(x_3);
x_22 = lean_expr_update_const(x_3, x_21);
x_23 = lean_array_uset(x_8, x_7, x_3);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
lean_inc(x_22);
x_25 = lean_array_uset(x_24, x_7, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_5);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_28, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_29, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_inc(x_3);
x_38 = lean_array_uset(x_37, x_7, x_3);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_expr_update_app(x_3, x_31, x_35);
lean_inc(x_40);
x_41 = lean_array_uset(x_39, x_7, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_40);
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_inc(x_3);
x_46 = lean_array_uset(x_45, x_7, x_3);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_expr_update_app(x_3, x_31, x_43);
lean_inc(x_48);
x_49 = lean_array_uset(x_47, x_7, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
case 6:
{
lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_5);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_55 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_52, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_53, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_inc(x_3);
x_63 = lean_array_uset(x_62, x_7, x_3);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = (uint8_t)((x_54 << 24) >> 61);
x_66 = lean_expr_update_lambda(x_3, x_65, x_56, x_60);
lean_inc(x_66);
x_67 = lean_array_uset(x_64, x_7, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_58, 1, x_68);
lean_ctor_set(x_58, 0, x_66);
return x_58;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_inc(x_3);
x_72 = lean_array_uset(x_71, x_7, x_3);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = (uint8_t)((x_54 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_3, x_74, x_56, x_69);
lean_inc(x_75);
x_76 = lean_array_uset(x_73, x_7, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
case 7:
{
lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_8);
lean_dec(x_5);
x_79 = lean_ctor_get(x_3, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_82 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_79, x_4);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_80, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_inc(x_3);
x_90 = lean_array_uset(x_89, x_7, x_3);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = (uint8_t)((x_81 << 24) >> 61);
x_93 = lean_expr_update_forall(x_3, x_92, x_83, x_87);
lean_inc(x_93);
x_94 = lean_array_uset(x_91, x_7, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_85, 1, x_95);
lean_ctor_set(x_85, 0, x_93);
return x_85;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_85, 0);
x_97 = lean_ctor_get(x_85, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_85);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_inc(x_3);
x_99 = lean_array_uset(x_98, x_7, x_3);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = (uint8_t)((x_81 << 24) >> 61);
x_102 = lean_expr_update_forall(x_3, x_101, x_83, x_96);
lean_inc(x_102);
x_103 = lean_array_uset(x_100, x_7, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
case 8:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_8);
lean_dec(x_5);
x_106 = lean_ctor_get(x_3, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_3, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_3, 3);
lean_inc(x_108);
lean_inc(x_1);
x_109 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_106, x_4);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_1);
x_112 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_107, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_108, x_114);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_inc(x_3);
x_120 = lean_array_uset(x_119, x_7, x_3);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_expr_update_let(x_3, x_110, x_113, x_117);
lean_inc(x_122);
x_123 = lean_array_uset(x_121, x_7, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_115, 1, x_124);
lean_ctor_set(x_115, 0, x_122);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_inc(x_3);
x_128 = lean_array_uset(x_127, x_7, x_3);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_expr_update_let(x_3, x_110, x_113, x_125);
lean_inc(x_130);
x_131 = lean_array_uset(x_129, x_7, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
case 10:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_8);
lean_dec(x_5);
x_134 = lean_ctor_get(x_3, 1);
lean_inc(x_134);
x_135 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_134, x_4);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_inc(x_3);
x_140 = lean_array_uset(x_139, x_7, x_3);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_expr_update_mdata(x_3, x_137);
lean_inc(x_142);
x_143 = lean_array_uset(x_141, x_7, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_135, 1, x_144);
lean_ctor_set(x_135, 0, x_142);
return x_135;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_145 = lean_ctor_get(x_135, 0);
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_135);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_inc(x_3);
x_148 = lean_array_uset(x_147, x_7, x_3);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_expr_update_mdata(x_3, x_145);
lean_inc(x_150);
x_151 = lean_array_uset(x_149, x_7, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
case 11:
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_8);
lean_dec(x_5);
x_154 = lean_ctor_get(x_3, 2);
lean_inc(x_154);
x_155 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_2, x_154, x_4);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_inc(x_3);
x_160 = lean_array_uset(x_159, x_7, x_3);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_162 = lean_expr_update_proj(x_3, x_157);
lean_inc(x_162);
x_163 = lean_array_uset(x_161, x_7, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_155, 1, x_164);
lean_ctor_set(x_155, 0, x_162);
return x_155;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_155, 0);
x_166 = lean_ctor_get(x_155, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_155);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_inc(x_3);
x_168 = lean_array_uset(x_167, x_7, x_3);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_expr_update_proj(x_3, x_165);
lean_inc(x_170);
x_171 = lean_array_uset(x_169, x_7, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
case 12:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_174 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___closed__1;
x_175 = l_unreachable_x21___rarg(x_174);
x_176 = lean_apply_1(x_175, x_4);
return x_176;
}
default: 
{
lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_3);
lean_ctor_set(x_177, 1, x_4);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_178 = lean_ctor_get(x_4, 1);
lean_inc(x_178);
x_179 = lean_array_uget(x_178, x_7);
lean_dec(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_4);
return x_180;
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_5, 1);
x_9 = 8192;
x_10 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_11 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_9, x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_5, 1, x_12);
x_13 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_7);
lean_ctor_set(x_2, 1, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_18 = 8192;
x_19 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_20 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_18, x_16, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_17);
x_23 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_14);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_29 = x_24;
} else {
 lean_dec_ref(x_24);
 x_29 = lean_box(0);
}
x_30 = 8192;
x_31 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_32 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_30, x_27, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
if (lean_is_scalar(x_29)) {
 x_34 = lean_alloc_ctor(0, 3, 0);
} else {
 x_34 = x_29;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_28);
x_35 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__3(x_1, x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Level_replace___main(x_7, x_5);
x_9 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_6);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_Level_replace___main(x_12, x_10);
x_14 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; uint8_t x_11; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_ptr_addr(x_3);
x_7 = x_2 == 0 ? 0 : x_6 % x_2;
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_array_uget(x_8, x_7);
x_10 = lean_ptr_addr(x_9);
lean_dec(x_9);
x_11 = x_10 == x_6;
if (x_11 == 0)
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = l_Lean_Level_replace___main(x_5, x_12);
lean_inc(x_3);
x_14 = lean_expr_update_sort(x_3, x_13);
x_15 = lean_array_uset(x_8, x_7, x_3);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
lean_inc(x_14);
x_17 = lean_array_uset(x_16, x_7, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
case 4:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
x_21 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__5(x_1, x_20);
lean_inc(x_3);
x_22 = lean_expr_update_const(x_3, x_21);
x_23 = lean_array_uset(x_8, x_7, x_3);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
lean_inc(x_22);
x_25 = lean_array_uset(x_24, x_7, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_5);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_28, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_29, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_inc(x_3);
x_38 = lean_array_uset(x_37, x_7, x_3);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_expr_update_app(x_3, x_31, x_35);
lean_inc(x_40);
x_41 = lean_array_uset(x_39, x_7, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_40);
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_inc(x_3);
x_46 = lean_array_uset(x_45, x_7, x_3);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_expr_update_app(x_3, x_31, x_43);
lean_inc(x_48);
x_49 = lean_array_uset(x_47, x_7, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
case 6:
{
lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_5);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_55 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_52, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_53, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_inc(x_3);
x_63 = lean_array_uset(x_62, x_7, x_3);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = (uint8_t)((x_54 << 24) >> 61);
x_66 = lean_expr_update_lambda(x_3, x_65, x_56, x_60);
lean_inc(x_66);
x_67 = lean_array_uset(x_64, x_7, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_58, 1, x_68);
lean_ctor_set(x_58, 0, x_66);
return x_58;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_inc(x_3);
x_72 = lean_array_uset(x_71, x_7, x_3);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = (uint8_t)((x_54 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_3, x_74, x_56, x_69);
lean_inc(x_75);
x_76 = lean_array_uset(x_73, x_7, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
case 7:
{
lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_8);
lean_dec(x_5);
x_79 = lean_ctor_get(x_3, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_82 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_79, x_4);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_80, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_inc(x_3);
x_90 = lean_array_uset(x_89, x_7, x_3);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = (uint8_t)((x_81 << 24) >> 61);
x_93 = lean_expr_update_forall(x_3, x_92, x_83, x_87);
lean_inc(x_93);
x_94 = lean_array_uset(x_91, x_7, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_85, 1, x_95);
lean_ctor_set(x_85, 0, x_93);
return x_85;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_85, 0);
x_97 = lean_ctor_get(x_85, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_85);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_inc(x_3);
x_99 = lean_array_uset(x_98, x_7, x_3);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = (uint8_t)((x_81 << 24) >> 61);
x_102 = lean_expr_update_forall(x_3, x_101, x_83, x_96);
lean_inc(x_102);
x_103 = lean_array_uset(x_100, x_7, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
case 8:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_8);
lean_dec(x_5);
x_106 = lean_ctor_get(x_3, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_3, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_3, 3);
lean_inc(x_108);
lean_inc(x_1);
x_109 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_106, x_4);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_1);
x_112 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_107, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_108, x_114);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_inc(x_3);
x_120 = lean_array_uset(x_119, x_7, x_3);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_expr_update_let(x_3, x_110, x_113, x_117);
lean_inc(x_122);
x_123 = lean_array_uset(x_121, x_7, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_115, 1, x_124);
lean_ctor_set(x_115, 0, x_122);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_inc(x_3);
x_128 = lean_array_uset(x_127, x_7, x_3);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_expr_update_let(x_3, x_110, x_113, x_125);
lean_inc(x_130);
x_131 = lean_array_uset(x_129, x_7, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
case 10:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_8);
lean_dec(x_5);
x_134 = lean_ctor_get(x_3, 1);
lean_inc(x_134);
x_135 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_134, x_4);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_inc(x_3);
x_140 = lean_array_uset(x_139, x_7, x_3);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_expr_update_mdata(x_3, x_137);
lean_inc(x_142);
x_143 = lean_array_uset(x_141, x_7, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_135, 1, x_144);
lean_ctor_set(x_135, 0, x_142);
return x_135;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_145 = lean_ctor_get(x_135, 0);
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_135);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_inc(x_3);
x_148 = lean_array_uset(x_147, x_7, x_3);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_expr_update_mdata(x_3, x_145);
lean_inc(x_150);
x_151 = lean_array_uset(x_149, x_7, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
case 11:
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_8);
lean_dec(x_5);
x_154 = lean_ctor_get(x_3, 2);
lean_inc(x_154);
x_155 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_2, x_154, x_4);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_inc(x_3);
x_160 = lean_array_uset(x_159, x_7, x_3);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_162 = lean_expr_update_proj(x_3, x_157);
lean_inc(x_162);
x_163 = lean_array_uset(x_161, x_7, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_155, 1, x_164);
lean_ctor_set(x_155, 0, x_162);
return x_155;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_155, 0);
x_166 = lean_ctor_get(x_155, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_155);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_inc(x_3);
x_168 = lean_array_uset(x_167, x_7, x_3);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_expr_update_proj(x_3, x_165);
lean_inc(x_170);
x_171 = lean_array_uset(x_169, x_7, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
case 12:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_174 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___closed__1;
x_175 = l_unreachable_x21___rarg(x_174);
x_176 = lean_apply_1(x_175, x_4);
return x_176;
}
default: 
{
lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_3);
lean_ctor_set(x_177, 1, x_4);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_178 = lean_ctor_get(x_4, 1);
lean_inc(x_178);
x_179 = lean_array_uget(x_178, x_7);
lean_dec(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_4);
return x_180;
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_5, 1);
x_9 = 8192;
x_10 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_11 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_9, x_8, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_5, 1, x_12);
x_13 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_1, x_7);
lean_ctor_set(x_2, 1, x_13);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
x_17 = lean_ctor_get(x_5, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_5);
x_18 = 8192;
x_19 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_20 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_18, x_16, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_17);
x_23 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_1, x_14);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_22);
return x_2;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 lean_ctor_release(x_24, 2);
 x_29 = x_24;
} else {
 lean_dec_ref(x_24);
 x_29 = lean_box(0);
}
x_30 = 8192;
x_31 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_32 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_30, x_27, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
if (lean_is_scalar(x_29)) {
 x_34 = lean_alloc_ctor(0, 3, 0);
} else {
 x_34 = x_29;
}
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_28);
x_35 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_1, x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_accLevelAtCtor___main___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_3);
x_6 = l___private_Lean_Elab_Inductive_19__getResultingUniverse(x_1, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Level_getOffsetAux___main(x_7, x_9);
x_11 = l_Lean_Level_getLevelOffset___main(x_7);
lean_dec(x_7);
x_12 = l_Lean_Level_isParam(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_3);
x_13 = l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2;
x_14 = l_Lean_Elab_Term_throwError___rarg(x_1, x_13, x_4, x_8);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_inc(x_3);
x_19 = l___private_Lean_Elab_Inductive_22__collectUniverses(x_1, x_11, x_10, x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Array_toList___rarg(x_21);
lean_dec(x_21);
x_23 = l_Lean_Level_mkNaryMax___main(x_22);
x_24 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_23, x_3);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = l_Array_toList___rarg(x_25);
lean_dec(x_25);
x_28 = l_Lean_Level_mkNaryMax___main(x_27);
x_29 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__6(x_28, x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_6);
if (x_35 == 0)
{
return x_6;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__4(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Inductive_23__updateResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Inductive_23__updateResultingUniverse(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
lean_object* _init_l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("  >> ");
return x_1;
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = l_Lean_Name_toString___closed__1;
x_10 = l_Lean_Name_toStringWithSep___main(x_9, x_8);
x_11 = l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1___closed__1;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Array_iterateMAux___main___at_Lean_ppGoal___spec__6___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_expr_dbg_to_string(x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = l_Lean_Meta_dbgTrace___rarg___closed__1;
x_19 = lean_dbg_trace(x_17, x_18);
lean_inc(x_2);
x_20 = lean_apply_2(x_19, x_2, x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_1 = x_7;
x_3 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
lean_object* l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_6, 2);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_2);
x_9 = l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1(x_8, x_2, x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_1 = x_7;
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
lean_dec(x_7);
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
lean_object* l___private_Lean_Elab_Inductive_24__traceIndTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__2(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_4);
x_10 = l_Lean_Elab_Term_collectUsedFVars(x_1, x_2, x_9, x_4, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_2 = x_11;
x_3 = x_8;
x_5 = x_12;
goto _start;
}
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_inc(x_4);
x_10 = l_Lean_Elab_Term_collectUsedFVars(x_1, x_2, x_9, x_4, x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
lean_dec(x_7);
lean_inc(x_4);
x_14 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__1(x_1, x_11, x_13, x_4, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_2 = x_15;
x_3 = x_8;
x_5 = x_16;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_25__removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l___private_Lean_Elab_Definition_1__removeUnused___closed__1;
lean_inc(x_4);
x_7 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__2(x_1, x_6, x_3, x_4, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Elab_Term_removeUnused(x_1, x_2, x_8, x_4, x_9);
return x_10;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_foldlM___main___at___private_Lean_Elab_Inductive_25__removeUnused___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Inductive_25__removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Inductive_25__removeUnused(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Inductive_26__withUsed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
x_7 = l___private_Lean_Elab_Inductive_25__removeUnused(x_1, x_2, x_3, x_5, x_6);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_26 = lean_ctor_get(x_5, 1);
x_27 = lean_ctor_get(x_5, 2);
x_28 = lean_ctor_get(x_5, 3);
x_29 = lean_ctor_get(x_5, 4);
x_30 = lean_ctor_get(x_5, 5);
x_31 = lean_ctor_get(x_5, 6);
x_32 = lean_ctor_get(x_5, 7);
x_33 = lean_ctor_get(x_5, 8);
x_34 = lean_ctor_get(x_5, 9);
x_35 = lean_ctor_get_uint8(x_5, sizeof(void*)*10);
x_36 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 1);
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*10 + 2);
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
lean_ctor_set(x_43, 9, x_34);
lean_ctor_set_uint8(x_43, sizeof(void*)*10, x_35);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 1, x_36);
lean_ctor_set_uint8(x_43, sizeof(void*)*10 + 2, x_37);
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
lean_object* l___private_Lean_Elab_Inductive_26__withUsed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_26__withUsed___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_26__withUsed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_Inductive_26__withUsed___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_4);
lean_inc(x_2);
x_14 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_13, x_4, x_5);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_9, 1, x_15);
x_17 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1(x_1, x_2, x_11, x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_3, 1, x_19);
lean_ctor_set(x_17, 0, x_3);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_17);
lean_ctor_set(x_3, 1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_free_object(x_3);
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
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
lean_free_object(x_9);
lean_dec(x_12);
lean_free_object(x_3);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_3, 1);
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_2);
x_34 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_33, x_4, x_5);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1(x_1, x_2, x_31, x_4, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
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
lean_ctor_set(x_3, 1, x_39);
lean_ctor_set(x_3, 0, x_37);
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_3);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_free_object(x_3);
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_45 = x_38;
} else {
 lean_dec_ref(x_38);
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
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_32);
lean_free_object(x_3);
lean_dec(x_31);
lean_dec(x_4);
lean_dec(x_2);
x_47 = lean_ctor_get(x_34, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_34, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_49 = x_34;
} else {
 lean_dec_ref(x_34);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_3, 0);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_3);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_55 = x_51;
} else {
 lean_dec_ref(x_51);
 x_55 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_2);
x_56 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_54, x_4, x_5);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
if (lean_is_scalar(x_55)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_55;
}
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1(x_1, x_2, x_52, x_4, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_61);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_68 = x_60;
} else {
 lean_dec_ref(x_60);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_4);
lean_dec(x_2);
x_70 = lean_ctor_get(x_56, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_72 = x_56;
} else {
 lean_dec_ref(x_56);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_4);
lean_inc(x_2);
x_15 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_13, x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_4);
lean_inc(x_2);
x_18 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1(x_1, x_2, x_14, x_4, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_9, 2, x_19);
lean_ctor_set(x_9, 1, x_16);
x_21 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2(x_1, x_2, x_11, x_4, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_21, 0, x_3);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_3, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_free_object(x_3);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
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
lean_dec(x_16);
lean_free_object(x_9);
lean_dec(x_12);
lean_free_object(x_3);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
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
lean_free_object(x_9);
lean_dec(x_14);
lean_dec(x_12);
lean_free_object(x_3);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_2);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
return x_15;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_15, 0);
x_37 = lean_ctor_get(x_15, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_15);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
x_42 = lean_ctor_get(x_9, 2);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_2);
x_43 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_41, x_4, x_5);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_4);
lean_inc(x_2);
x_46 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1(x_1, x_2, x_42, x_4, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_40);
lean_ctor_set(x_49, 1, x_44);
lean_ctor_set(x_49, 2, x_47);
x_50 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2(x_1, x_2, x_39, x_4, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
lean_ctor_set(x_3, 1, x_51);
lean_ctor_set(x_3, 0, x_49);
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_49);
lean_free_object(x_3);
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_50, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_57 = x_50;
} else {
 lean_dec_ref(x_50);
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
lean_dec(x_44);
lean_dec(x_40);
lean_free_object(x_3);
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_2);
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_61 = x_46;
} else {
 lean_dec_ref(x_46);
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
lean_dec(x_42);
lean_dec(x_40);
lean_free_object(x_3);
lean_dec(x_39);
lean_dec(x_4);
lean_dec(x_2);
x_63 = lean_ctor_get(x_43, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_43, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_65 = x_43;
} else {
 lean_dec_ref(x_43);
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
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_3, 0);
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_3);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 2);
lean_inc(x_71);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 lean_ctor_release(x_67, 2);
 x_72 = x_67;
} else {
 lean_dec_ref(x_67);
 x_72 = lean_box(0);
}
lean_inc(x_4);
lean_inc(x_2);
x_73 = l_Lean_Elab_Term_mkForall(x_1, x_2, x_70, x_4, x_5);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_4);
lean_inc(x_2);
x_76 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1(x_1, x_2, x_71, x_4, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
if (lean_is_scalar(x_72)) {
 x_79 = lean_alloc_ctor(0, 3, 0);
} else {
 x_79 = x_72;
}
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_77);
x_80 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2(x_1, x_2, x_68, x_4, x_78);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_81);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_79);
x_86 = lean_ctor_get(x_80, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_80, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_88 = x_80;
} else {
 lean_dec_ref(x_80);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_74);
lean_dec(x_72);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_4);
lean_dec(x_2);
x_90 = lean_ctor_get(x_76, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_76, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_92 = x_76;
} else {
 lean_dec_ref(x_76);
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
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_4);
lean_dec(x_2);
x_94 = lean_ctor_get(x_73, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_73, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_96 = x_73;
} else {
 lean_dec_ref(x_73);
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
}
}
}
lean_object* l___private_Lean_Elab_Inductive_27__updateParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l___private_Lean_Elab_Inductive_27__updateParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_Inductive_27__updateParams(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_List_foldl___main___at___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_CollectLevelParams_main___main(x_5, x_1);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_List_foldl___main___at___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Lean_CollectLevelParams_main___main(x_5, x_1);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_List_foldl___main___at___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive___spec__1(x_6, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_DepElim_getUnusedLevelParam___closed__1;
x_3 = l_List_foldl___main___at___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive___spec__2(x_2, x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_29__mkIndFVar2Const___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
x_11 = lean_nat_sub(x_4, x_5);
lean_dec(x_5);
x_12 = l_Lean_Elab_Command_InductiveView_inhabited;
x_13 = lean_array_get(x_12, x_1, x_11);
x_14 = l_Lean_Expr_Inhabited;
x_15 = lean_array_get(x_14, x_2, x_11);
lean_dec(x_11);
x_16 = lean_ctor_get(x_13, 3);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_3);
x_17 = l_Lean_mkConst(x_16, x_3);
x_18 = l_Std_HashMapImp_insert___at___private_Lean_MetavarContext_2__visit___spec__3(x_6, x_15, x_17);
x_5 = x_10;
x_6 = x_18;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_29__mkIndFVar2Const(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_List_map___main___at_Lean_Meta_addGlobalInstance___spec__1(x_3);
x_5 = lean_array_get_size(x_1);
x_6 = l_Std_HashMap_inhabited___closed__1;
lean_inc(x_5);
x_7 = l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_29__mkIndFVar2Const___spec__1(x_1, x_2, x_4, x_5, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_29__mkIndFVar2Const___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldAux___main___at___private_Lean_Elab_Inductive_29__mkIndFVar2Const___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_29__mkIndFVar2Const___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_29__mkIndFVar2Const(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_160; lean_object* x_161; size_t x_162; uint8_t x_163; 
x_6 = lean_ptr_addr(x_4);
x_7 = x_3 == 0 ? 0 : x_6 % x_3;
x_160 = lean_ctor_get(x_5, 0);
lean_inc(x_160);
x_161 = lean_array_uget(x_160, x_7);
x_162 = lean_ptr_addr(x_161);
lean_dec(x_161);
x_163 = x_162 == x_6;
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = l_Lean_Expr_isFVar(x_4);
if (x_164 == 0)
{
lean_object* x_165; 
lean_dec(x_160);
x_165 = lean_box(0);
x_8 = x_165;
goto block_159;
}
else
{
lean_object* x_166; 
x_166 = l_Std_HashMapImp_find_x3f___at___private_Lean_MetavarContext_2__visit___spec__1(x_1, x_4);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; 
lean_dec(x_160);
x_167 = lean_box(0);
x_8 = x_167;
goto block_159;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_unsigned_to_nat(0u);
x_170 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_2, x_2, x_169, x_168);
x_171 = lean_array_uset(x_160, x_7, x_4);
x_172 = lean_ctor_get(x_5, 1);
lean_inc(x_172);
lean_dec(x_5);
lean_inc(x_170);
x_173 = lean_array_uset(x_172, x_7, x_170);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_170);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_160);
lean_dec(x_4);
x_176 = lean_ctor_get(x_5, 1);
lean_inc(x_176);
x_177 = lean_array_uget(x_176, x_7);
lean_dec(x_176);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_5);
return x_178;
}
block_159:
{
lean_dec(x_8);
switch (lean_obj_tag(x_4)) {
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_9, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_10, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_inc(x_4);
x_19 = lean_array_uset(x_18, x_7, x_4);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_expr_update_app(x_4, x_12, x_16);
lean_inc(x_21);
x_22 = lean_array_uset(x_20, x_7, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_21);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_inc(x_4);
x_27 = lean_array_uset(x_26, x_7, x_4);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_expr_update_app(x_4, x_12, x_24);
lean_inc(x_29);
x_30 = lean_array_uset(x_28, x_7, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
case 6:
{
lean_object* x_33; lean_object* x_34; uint64_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_4, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_36 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_33, x_5);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_34, x_38);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_inc(x_4);
x_44 = lean_array_uset(x_43, x_7, x_4);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = (uint8_t)((x_35 << 24) >> 61);
x_47 = lean_expr_update_lambda(x_4, x_46, x_37, x_41);
lean_inc(x_47);
x_48 = lean_array_uset(x_45, x_7, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_39, 1, x_49);
lean_ctor_set(x_39, 0, x_47);
return x_39;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_39, 0);
x_51 = lean_ctor_get(x_39, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_39);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_inc(x_4);
x_53 = lean_array_uset(x_52, x_7, x_4);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = (uint8_t)((x_35 << 24) >> 61);
x_56 = lean_expr_update_lambda(x_4, x_55, x_37, x_50);
lean_inc(x_56);
x_57 = lean_array_uset(x_54, x_7, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
case 7:
{
lean_object* x_60; lean_object* x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_4, 2);
lean_inc(x_61);
x_62 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_63 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_60, x_5);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_61, x_65);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_ctor_get(x_66, 1);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_inc(x_4);
x_71 = lean_array_uset(x_70, x_7, x_4);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = (uint8_t)((x_62 << 24) >> 61);
x_74 = lean_expr_update_forall(x_4, x_73, x_64, x_68);
lean_inc(x_74);
x_75 = lean_array_uset(x_72, x_7, x_74);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_66, 1, x_76);
lean_ctor_set(x_66, 0, x_74);
return x_66;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_66, 0);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_66);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_inc(x_4);
x_80 = lean_array_uset(x_79, x_7, x_4);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = (uint8_t)((x_62 << 24) >> 61);
x_83 = lean_expr_update_forall(x_4, x_82, x_64, x_77);
lean_inc(x_83);
x_84 = lean_array_uset(x_81, x_7, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
case 8:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_87 = lean_ctor_get(x_4, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_4, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_4, 3);
lean_inc(x_89);
x_90 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_87, x_5);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_88, x_92);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_89, x_95);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_inc(x_4);
x_101 = lean_array_uset(x_100, x_7, x_4);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_expr_update_let(x_4, x_91, x_94, x_98);
lean_inc(x_103);
x_104 = lean_array_uset(x_102, x_7, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_96, 1, x_105);
lean_ctor_set(x_96, 0, x_103);
return x_96;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = lean_ctor_get(x_96, 0);
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_96);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_inc(x_4);
x_109 = lean_array_uset(x_108, x_7, x_4);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_expr_update_let(x_4, x_91, x_94, x_106);
lean_inc(x_111);
x_112 = lean_array_uset(x_110, x_7, x_111);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_109);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
case 10:
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_115 = lean_ctor_get(x_4, 1);
lean_inc(x_115);
x_116 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_115, x_5);
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_ctor_get(x_116, 1);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_inc(x_4);
x_121 = lean_array_uset(x_120, x_7, x_4);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = lean_expr_update_mdata(x_4, x_118);
lean_inc(x_123);
x_124 = lean_array_uset(x_122, x_7, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
lean_ctor_set(x_116, 1, x_125);
lean_ctor_set(x_116, 0, x_123);
return x_116;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_126 = lean_ctor_get(x_116, 0);
x_127 = lean_ctor_get(x_116, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_116);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_inc(x_4);
x_129 = lean_array_uset(x_128, x_7, x_4);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_expr_update_mdata(x_4, x_126);
lean_inc(x_131);
x_132 = lean_array_uset(x_130, x_7, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
case 11:
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_4, 2);
lean_inc(x_135);
x_136 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_135, x_5);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_inc(x_4);
x_141 = lean_array_uset(x_140, x_7, x_4);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_expr_update_proj(x_4, x_138);
lean_inc(x_143);
x_144 = lean_array_uset(x_142, x_7, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_136, 1, x_145);
lean_ctor_set(x_136, 0, x_143);
return x_136;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_146 = lean_ctor_get(x_136, 0);
x_147 = lean_ctor_get(x_136, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_136);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_inc(x_4);
x_149 = lean_array_uset(x_148, x_7, x_4);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_dec(x_147);
x_151 = lean_expr_update_proj(x_4, x_146);
lean_inc(x_151);
x_152 = lean_array_uset(x_150, x_7, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
case 12:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_4);
x_155 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___closed__1;
x_156 = l_unreachable_x21___rarg(x_155);
x_157 = lean_apply_1(x_156, x_5);
return x_157;
}
default: 
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_4);
lean_ctor_set(x_158, 1, x_5);
return x_158;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_10 = 8192;
x_11 = l_Lean_Expr_ReplaceImpl_initCache;
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_10, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_mkForall(x_2, x_13, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_4, x_5);
lean_inc(x_6);
x_16 = l_Lean_Meta_getFVarLocalDecl(x_15, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_type(x_17);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_19);
x_20 = l_Lean_Meta_isClassQuick___main(x_19, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_15);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_5, x_23);
lean_dec(x_5);
x_5 = x_24;
x_7 = x_22;
goto _start;
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_27 = x_20;
} else {
 lean_dec_ref(x_20);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_26, 2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_90; uint8_t x_91; 
x_34 = lean_ctor_get(x_32, 2);
x_90 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_32, 2, x_90);
x_91 = !lean_is_exclusive(x_6);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_6, 2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_28);
lean_ctor_set(x_93, 1, x_15);
x_94 = lean_array_push(x_92, x_93);
lean_ctor_set(x_6, 2, x_94);
x_95 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_2, x_3, x_4, x_30, x_6, x_26);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_96);
x_35 = x_98;
x_36 = x_97;
goto block_89;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_dec(x_95);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_99);
x_35 = x_101;
x_36 = x_100;
goto block_89;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_6, 0);
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
x_105 = lean_ctor_get(x_6, 3);
x_106 = lean_ctor_get(x_6, 4);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_6);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_28);
lean_ctor_set(x_107, 1, x_15);
x_108 = lean_array_push(x_104, x_107);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_105);
lean_ctor_set(x_109, 4, x_106);
x_110 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_2, x_3, x_4, x_30, x_109, x_26);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_111);
x_35 = x_113;
x_36 = x_112;
goto block_89;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_114);
x_35 = x_116;
x_36 = x_115;
goto block_89;
}
}
block_89:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 2);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 2);
lean_dec(x_42);
lean_ctor_set(x_37, 2, x_34);
if (lean_is_scalar(x_27)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_27;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
x_46 = lean_ctor_get(x_37, 3);
x_47 = lean_ctor_get(x_37, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_34);
lean_ctor_set(x_48, 3, x_46);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set(x_36, 2, x_48);
if (lean_is_scalar(x_27)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_27;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_36);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
x_52 = lean_ctor_get(x_36, 3);
x_53 = lean_ctor_get(x_36, 4);
x_54 = lean_ctor_get(x_36, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_55 = lean_ctor_get(x_37, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_37, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_37, 4);
lean_inc(x_58);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 x_59 = x_37;
} else {
 lean_dec_ref(x_37);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_34);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_58);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_52);
lean_ctor_set(x_61, 4, x_53);
lean_ctor_set(x_61, 5, x_54);
if (lean_is_scalar(x_27)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_27;
 lean_ctor_set_tag(x_62, 1);
}
lean_ctor_set(x_62, 0, x_38);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_36, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = !lean_is_exclusive(x_36);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_36, 2);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_63, 2);
lean_dec(x_68);
lean_ctor_set(x_63, 2, x_34);
if (lean_is_scalar(x_27)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_27;
}
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_36);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_63, 0);
x_71 = lean_ctor_get(x_63, 1);
x_72 = lean_ctor_get(x_63, 3);
x_73 = lean_ctor_get(x_63, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_63);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_74, 2, x_34);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
lean_ctor_set(x_36, 2, x_74);
if (lean_is_scalar(x_27)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_27;
}
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_36);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_36, 0);
x_77 = lean_ctor_get(x_36, 1);
x_78 = lean_ctor_get(x_36, 3);
x_79 = lean_ctor_get(x_36, 4);
x_80 = lean_ctor_get(x_36, 5);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_36);
x_81 = lean_ctor_get(x_63, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_63, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_63, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_63, 4);
lean_inc(x_84);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 x_85 = x_63;
} else {
 lean_dec_ref(x_63);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 5, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_34);
lean_ctor_set(x_86, 3, x_83);
lean_ctor_set(x_86, 4, x_84);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_77);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_78);
lean_ctor_set(x_87, 4, x_79);
lean_ctor_set(x_87, 5, x_80);
if (lean_is_scalar(x_27)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_27;
}
lean_ctor_set(x_88, 0, x_64);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_117 = lean_ctor_get(x_32, 0);
x_118 = lean_ctor_get(x_32, 1);
x_119 = lean_ctor_get(x_32, 2);
x_120 = lean_ctor_get(x_32, 3);
x_121 = lean_ctor_get(x_32, 4);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_32);
x_157 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_158 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_158, 0, x_117);
lean_ctor_set(x_158, 1, x_118);
lean_ctor_set(x_158, 2, x_157);
lean_ctor_set(x_158, 3, x_120);
lean_ctor_set(x_158, 4, x_121);
lean_ctor_set(x_26, 2, x_158);
x_159 = lean_ctor_get(x_6, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_6, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_6, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_6, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_6, 4);
lean_inc(x_163);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_164 = x_6;
} else {
 lean_dec_ref(x_6);
 x_164 = lean_box(0);
}
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_28);
lean_ctor_set(x_165, 1, x_15);
x_166 = lean_array_push(x_161, x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_166);
lean_ctor_set(x_167, 3, x_162);
lean_ctor_set(x_167, 4, x_163);
x_168 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_2, x_3, x_4, x_30, x_167, x_26);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_169);
x_122 = x_171;
x_123 = x_170;
goto block_156;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
lean_dec(x_168);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_172);
x_122 = x_174;
x_123 = x_173;
goto block_156;
}
block_156:
{
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_124 = lean_ctor_get(x_123, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 4);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 5);
lean_inc(x_130);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 x_131 = x_123;
} else {
 lean_dec_ref(x_123);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_124, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_124, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_124, 4);
lean_inc(x_135);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 x_136 = x_124;
} else {
 lean_dec_ref(x_124);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set(x_137, 2, x_119);
lean_ctor_set(x_137, 3, x_134);
lean_ctor_set(x_137, 4, x_135);
if (lean_is_scalar(x_131)) {
 x_138 = lean_alloc_ctor(0, 6, 0);
} else {
 x_138 = x_131;
}
lean_ctor_set(x_138, 0, x_126);
lean_ctor_set(x_138, 1, x_127);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_138, 3, x_128);
lean_ctor_set(x_138, 4, x_129);
lean_ctor_set(x_138, 5, x_130);
if (lean_is_scalar(x_27)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_27;
 lean_ctor_set_tag(x_139, 1);
}
lean_ctor_set(x_139, 0, x_125);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_140 = lean_ctor_get(x_123, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_122, 0);
lean_inc(x_141);
lean_dec(x_122);
x_142 = lean_ctor_get(x_123, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_123, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_123, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_123, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 x_147 = x_123;
} else {
 lean_dec_ref(x_123);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_140, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_140, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_140, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_140, 4);
lean_inc(x_151);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 lean_ctor_release(x_140, 2);
 lean_ctor_release(x_140, 3);
 lean_ctor_release(x_140, 4);
 x_152 = x_140;
} else {
 lean_dec_ref(x_140);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 5, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_149);
lean_ctor_set(x_153, 2, x_119);
lean_ctor_set(x_153, 3, x_150);
lean_ctor_set(x_153, 4, x_151);
if (lean_is_scalar(x_147)) {
 x_154 = lean_alloc_ctor(0, 6, 0);
} else {
 x_154 = x_147;
}
lean_ctor_set(x_154, 0, x_142);
lean_ctor_set(x_154, 1, x_143);
lean_ctor_set(x_154, 2, x_153);
lean_ctor_set(x_154, 3, x_144);
lean_ctor_set(x_154, 4, x_145);
lean_ctor_set(x_154, 5, x_146);
if (lean_is_scalar(x_27)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_27;
}
lean_ctor_set(x_155, 0, x_141);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_175 = lean_ctor_get(x_26, 2);
x_176 = lean_ctor_get(x_26, 0);
x_177 = lean_ctor_get(x_26, 1);
x_178 = lean_ctor_get(x_26, 3);
x_179 = lean_ctor_get(x_26, 4);
x_180 = lean_ctor_get(x_26, 5);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_175);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_26);
x_181 = lean_ctor_get(x_175, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_175, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_175, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_175, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_175, 4);
lean_inc(x_185);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 lean_ctor_release(x_175, 2);
 lean_ctor_release(x_175, 3);
 lean_ctor_release(x_175, 4);
 x_186 = x_175;
} else {
 lean_dec_ref(x_175);
 x_186 = lean_box(0);
}
x_222 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_186)) {
 x_223 = lean_alloc_ctor(0, 5, 0);
} else {
 x_223 = x_186;
}
lean_ctor_set(x_223, 0, x_181);
lean_ctor_set(x_223, 1, x_182);
lean_ctor_set(x_223, 2, x_222);
lean_ctor_set(x_223, 3, x_184);
lean_ctor_set(x_223, 4, x_185);
x_224 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_224, 0, x_176);
lean_ctor_set(x_224, 1, x_177);
lean_ctor_set(x_224, 2, x_223);
lean_ctor_set(x_224, 3, x_178);
lean_ctor_set(x_224, 4, x_179);
lean_ctor_set(x_224, 5, x_180);
x_225 = lean_ctor_get(x_6, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_6, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_6, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_6, 3);
lean_inc(x_228);
x_229 = lean_ctor_get(x_6, 4);
lean_inc(x_229);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_230 = x_6;
} else {
 lean_dec_ref(x_6);
 x_230 = lean_box(0);
}
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_28);
lean_ctor_set(x_231, 1, x_15);
x_232 = lean_array_push(x_227, x_231);
if (lean_is_scalar(x_230)) {
 x_233 = lean_alloc_ctor(0, 5, 0);
} else {
 x_233 = x_230;
}
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_226);
lean_ctor_set(x_233, 2, x_232);
lean_ctor_set(x_233, 3, x_228);
lean_ctor_set(x_233, 4, x_229);
x_234 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_2, x_3, x_4, x_30, x_233, x_224);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_235);
x_187 = x_237;
x_188 = x_236;
goto block_221;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_234, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_dec(x_234);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_238);
x_187 = x_240;
x_188 = x_239;
goto block_221;
}
block_221:
{
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_189 = lean_ctor_get(x_188, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 5);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_189, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_189, 4);
lean_inc(x_200);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 x_201 = x_189;
} else {
 lean_dec_ref(x_189);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 5, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set(x_202, 1, x_198);
lean_ctor_set(x_202, 2, x_183);
lean_ctor_set(x_202, 3, x_199);
lean_ctor_set(x_202, 4, x_200);
if (lean_is_scalar(x_196)) {
 x_203 = lean_alloc_ctor(0, 6, 0);
} else {
 x_203 = x_196;
}
lean_ctor_set(x_203, 0, x_191);
lean_ctor_set(x_203, 1, x_192);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_193);
lean_ctor_set(x_203, 4, x_194);
lean_ctor_set(x_203, 5, x_195);
if (lean_is_scalar(x_27)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_27;
 lean_ctor_set_tag(x_204, 1);
}
lean_ctor_set(x_204, 0, x_190);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_205 = lean_ctor_get(x_188, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_187, 0);
lean_inc(x_206);
lean_dec(x_187);
x_207 = lean_ctor_get(x_188, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_188, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_188, 3);
lean_inc(x_209);
x_210 = lean_ctor_get(x_188, 4);
lean_inc(x_210);
x_211 = lean_ctor_get(x_188, 5);
lean_inc(x_211);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_212 = x_188;
} else {
 lean_dec_ref(x_188);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_205, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_205, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_205, 3);
lean_inc(x_215);
x_216 = lean_ctor_get(x_205, 4);
lean_inc(x_216);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 lean_ctor_release(x_205, 4);
 x_217 = x_205;
} else {
 lean_dec_ref(x_205);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(0, 5, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_213);
lean_ctor_set(x_218, 1, x_214);
lean_ctor_set(x_218, 2, x_183);
lean_ctor_set(x_218, 3, x_215);
lean_ctor_set(x_218, 4, x_216);
if (lean_is_scalar(x_212)) {
 x_219 = lean_alloc_ctor(0, 6, 0);
} else {
 x_219 = x_212;
}
lean_ctor_set(x_219, 0, x_207);
lean_ctor_set(x_219, 1, x_208);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_209);
lean_ctor_set(x_219, 4, x_210);
lean_ctor_set(x_219, 5, x_211);
if (lean_is_scalar(x_27)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_27;
}
lean_ctor_set(x_220, 0, x_206);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
default: 
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_20, 1);
lean_inc(x_241);
lean_dec(x_20);
lean_inc(x_6);
x_242 = l_Lean_Meta_isClassExpensive___main(x_19, x_6, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_15);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_unsigned_to_nat(1u);
x_246 = lean_nat_add(x_5, x_245);
lean_dec(x_5);
x_5 = x_246;
x_7 = x_244;
goto _start;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_249 = x_242;
} else {
 lean_dec_ref(x_242);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_243, 0);
lean_inc(x_250);
lean_dec(x_243);
x_251 = lean_unsigned_to_nat(1u);
x_252 = lean_nat_add(x_5, x_251);
lean_dec(x_5);
x_253 = !lean_is_exclusive(x_248);
if (x_253 == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_248, 2);
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_312; uint8_t x_313; 
x_256 = lean_ctor_get(x_254, 2);
x_312 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_254, 2, x_312);
x_313 = !lean_is_exclusive(x_6);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_314 = lean_ctor_get(x_6, 2);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_250);
lean_ctor_set(x_315, 1, x_15);
x_316 = lean_array_push(x_314, x_315);
lean_ctor_set(x_6, 2, x_316);
x_317 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_2, x_3, x_4, x_252, x_6, x_248);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_318);
x_257 = x_320;
x_258 = x_319;
goto block_311;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_317, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
lean_dec(x_317);
x_323 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_323, 0, x_321);
x_257 = x_323;
x_258 = x_322;
goto block_311;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_324 = lean_ctor_get(x_6, 0);
x_325 = lean_ctor_get(x_6, 1);
x_326 = lean_ctor_get(x_6, 2);
x_327 = lean_ctor_get(x_6, 3);
x_328 = lean_ctor_get(x_6, 4);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_6);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_250);
lean_ctor_set(x_329, 1, x_15);
x_330 = lean_array_push(x_326, x_329);
x_331 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_331, 0, x_324);
lean_ctor_set(x_331, 1, x_325);
lean_ctor_set(x_331, 2, x_330);
lean_ctor_set(x_331, 3, x_327);
lean_ctor_set(x_331, 4, x_328);
x_332 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_2, x_3, x_4, x_252, x_331, x_248);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_333);
x_257 = x_335;
x_258 = x_334;
goto block_311;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_332, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_332, 1);
lean_inc(x_337);
lean_dec(x_332);
x_338 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_338, 0, x_336);
x_257 = x_338;
x_258 = x_337;
goto block_311;
}
}
block_311:
{
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_258, 2);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 0);
lean_inc(x_260);
lean_dec(x_257);
x_261 = !lean_is_exclusive(x_258);
if (x_261 == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_258, 2);
lean_dec(x_262);
x_263 = !lean_is_exclusive(x_259);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_259, 2);
lean_dec(x_264);
lean_ctor_set(x_259, 2, x_256);
if (lean_is_scalar(x_249)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_249;
 lean_ctor_set_tag(x_265, 1);
}
lean_ctor_set(x_265, 0, x_260);
lean_ctor_set(x_265, 1, x_258);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_259, 0);
x_267 = lean_ctor_get(x_259, 1);
x_268 = lean_ctor_get(x_259, 3);
x_269 = lean_ctor_get(x_259, 4);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_259);
x_270 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_267);
lean_ctor_set(x_270, 2, x_256);
lean_ctor_set(x_270, 3, x_268);
lean_ctor_set(x_270, 4, x_269);
lean_ctor_set(x_258, 2, x_270);
if (lean_is_scalar(x_249)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_249;
 lean_ctor_set_tag(x_271, 1);
}
lean_ctor_set(x_271, 0, x_260);
lean_ctor_set(x_271, 1, x_258);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_272 = lean_ctor_get(x_258, 0);
x_273 = lean_ctor_get(x_258, 1);
x_274 = lean_ctor_get(x_258, 3);
x_275 = lean_ctor_get(x_258, 4);
x_276 = lean_ctor_get(x_258, 5);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_258);
x_277 = lean_ctor_get(x_259, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_259, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_259, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_259, 4);
lean_inc(x_280);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 lean_ctor_release(x_259, 3);
 lean_ctor_release(x_259, 4);
 x_281 = x_259;
} else {
 lean_dec_ref(x_259);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 5, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_277);
lean_ctor_set(x_282, 1, x_278);
lean_ctor_set(x_282, 2, x_256);
lean_ctor_set(x_282, 3, x_279);
lean_ctor_set(x_282, 4, x_280);
x_283 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_283, 0, x_272);
lean_ctor_set(x_283, 1, x_273);
lean_ctor_set(x_283, 2, x_282);
lean_ctor_set(x_283, 3, x_274);
lean_ctor_set(x_283, 4, x_275);
lean_ctor_set(x_283, 5, x_276);
if (lean_is_scalar(x_249)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_249;
 lean_ctor_set_tag(x_284, 1);
}
lean_ctor_set(x_284, 0, x_260);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_258, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_257, 0);
lean_inc(x_286);
lean_dec(x_257);
x_287 = !lean_is_exclusive(x_258);
if (x_287 == 0)
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_ctor_get(x_258, 2);
lean_dec(x_288);
x_289 = !lean_is_exclusive(x_285);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_285, 2);
lean_dec(x_290);
lean_ctor_set(x_285, 2, x_256);
if (lean_is_scalar(x_249)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_249;
}
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_258);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_292 = lean_ctor_get(x_285, 0);
x_293 = lean_ctor_get(x_285, 1);
x_294 = lean_ctor_get(x_285, 3);
x_295 = lean_ctor_get(x_285, 4);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_285);
x_296 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_296, 0, x_292);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_256);
lean_ctor_set(x_296, 3, x_294);
lean_ctor_set(x_296, 4, x_295);
lean_ctor_set(x_258, 2, x_296);
if (lean_is_scalar(x_249)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_249;
}
lean_ctor_set(x_297, 0, x_286);
lean_ctor_set(x_297, 1, x_258);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_298 = lean_ctor_get(x_258, 0);
x_299 = lean_ctor_get(x_258, 1);
x_300 = lean_ctor_get(x_258, 3);
x_301 = lean_ctor_get(x_258, 4);
x_302 = lean_ctor_get(x_258, 5);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_258);
x_303 = lean_ctor_get(x_285, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_285, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_285, 3);
lean_inc(x_305);
x_306 = lean_ctor_get(x_285, 4);
lean_inc(x_306);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 lean_ctor_release(x_285, 4);
 x_307 = x_285;
} else {
 lean_dec_ref(x_285);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(0, 5, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_303);
lean_ctor_set(x_308, 1, x_304);
lean_ctor_set(x_308, 2, x_256);
lean_ctor_set(x_308, 3, x_305);
lean_ctor_set(x_308, 4, x_306);
x_309 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_309, 0, x_298);
lean_ctor_set(x_309, 1, x_299);
lean_ctor_set(x_309, 2, x_308);
lean_ctor_set(x_309, 3, x_300);
lean_ctor_set(x_309, 4, x_301);
lean_ctor_set(x_309, 5, x_302);
if (lean_is_scalar(x_249)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_249;
}
lean_ctor_set(x_310, 0, x_286);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_339 = lean_ctor_get(x_254, 0);
x_340 = lean_ctor_get(x_254, 1);
x_341 = lean_ctor_get(x_254, 2);
x_342 = lean_ctor_get(x_254, 3);
x_343 = lean_ctor_get(x_254, 4);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_254);
x_379 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_380 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_380, 0, x_339);
lean_ctor_set(x_380, 1, x_340);
lean_ctor_set(x_380, 2, x_379);
lean_ctor_set(x_380, 3, x_342);
lean_ctor_set(x_380, 4, x_343);
lean_ctor_set(x_248, 2, x_380);
x_381 = lean_ctor_get(x_6, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_6, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_6, 2);
lean_inc(x_383);
x_384 = lean_ctor_get(x_6, 3);
lean_inc(x_384);
x_385 = lean_ctor_get(x_6, 4);
lean_inc(x_385);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_386 = x_6;
} else {
 lean_dec_ref(x_6);
 x_386 = lean_box(0);
}
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_250);
lean_ctor_set(x_387, 1, x_15);
x_388 = lean_array_push(x_383, x_387);
if (lean_is_scalar(x_386)) {
 x_389 = lean_alloc_ctor(0, 5, 0);
} else {
 x_389 = x_386;
}
lean_ctor_set(x_389, 0, x_381);
lean_ctor_set(x_389, 1, x_382);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_389, 3, x_384);
lean_ctor_set(x_389, 4, x_385);
x_390 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_2, x_3, x_4, x_252, x_389, x_248);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_391);
x_344 = x_393;
x_345 = x_392;
goto block_378;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_390, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_390, 1);
lean_inc(x_395);
lean_dec(x_390);
x_396 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_396, 0, x_394);
x_344 = x_396;
x_345 = x_395;
goto block_378;
}
block_378:
{
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_346 = lean_ctor_get(x_345, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
lean_dec(x_344);
x_348 = lean_ctor_get(x_345, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_345, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_345, 3);
lean_inc(x_350);
x_351 = lean_ctor_get(x_345, 4);
lean_inc(x_351);
x_352 = lean_ctor_get(x_345, 5);
lean_inc(x_352);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 lean_ctor_release(x_345, 4);
 lean_ctor_release(x_345, 5);
 x_353 = x_345;
} else {
 lean_dec_ref(x_345);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_346, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_346, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_346, 3);
lean_inc(x_356);
x_357 = lean_ctor_get(x_346, 4);
lean_inc(x_357);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 lean_ctor_release(x_346, 2);
 lean_ctor_release(x_346, 3);
 lean_ctor_release(x_346, 4);
 x_358 = x_346;
} else {
 lean_dec_ref(x_346);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(0, 5, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_354);
lean_ctor_set(x_359, 1, x_355);
lean_ctor_set(x_359, 2, x_341);
lean_ctor_set(x_359, 3, x_356);
lean_ctor_set(x_359, 4, x_357);
if (lean_is_scalar(x_353)) {
 x_360 = lean_alloc_ctor(0, 6, 0);
} else {
 x_360 = x_353;
}
lean_ctor_set(x_360, 0, x_348);
lean_ctor_set(x_360, 1, x_349);
lean_ctor_set(x_360, 2, x_359);
lean_ctor_set(x_360, 3, x_350);
lean_ctor_set(x_360, 4, x_351);
lean_ctor_set(x_360, 5, x_352);
if (lean_is_scalar(x_249)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_249;
 lean_ctor_set_tag(x_361, 1);
}
lean_ctor_set(x_361, 0, x_347);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_362 = lean_ctor_get(x_345, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_344, 0);
lean_inc(x_363);
lean_dec(x_344);
x_364 = lean_ctor_get(x_345, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_345, 1);
lean_inc(x_365);
x_366 = lean_ctor_get(x_345, 3);
lean_inc(x_366);
x_367 = lean_ctor_get(x_345, 4);
lean_inc(x_367);
x_368 = lean_ctor_get(x_345, 5);
lean_inc(x_368);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 lean_ctor_release(x_345, 4);
 lean_ctor_release(x_345, 5);
 x_369 = x_345;
} else {
 lean_dec_ref(x_345);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_362, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_362, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_362, 3);
lean_inc(x_372);
x_373 = lean_ctor_get(x_362, 4);
lean_inc(x_373);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 lean_ctor_release(x_362, 2);
 lean_ctor_release(x_362, 3);
 lean_ctor_release(x_362, 4);
 x_374 = x_362;
} else {
 lean_dec_ref(x_362);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(0, 5, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_370);
lean_ctor_set(x_375, 1, x_371);
lean_ctor_set(x_375, 2, x_341);
lean_ctor_set(x_375, 3, x_372);
lean_ctor_set(x_375, 4, x_373);
if (lean_is_scalar(x_369)) {
 x_376 = lean_alloc_ctor(0, 6, 0);
} else {
 x_376 = x_369;
}
lean_ctor_set(x_376, 0, x_364);
lean_ctor_set(x_376, 1, x_365);
lean_ctor_set(x_376, 2, x_375);
lean_ctor_set(x_376, 3, x_366);
lean_ctor_set(x_376, 4, x_367);
lean_ctor_set(x_376, 5, x_368);
if (lean_is_scalar(x_249)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_249;
}
lean_ctor_set(x_377, 0, x_363);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_397 = lean_ctor_get(x_248, 2);
x_398 = lean_ctor_get(x_248, 0);
x_399 = lean_ctor_get(x_248, 1);
x_400 = lean_ctor_get(x_248, 3);
x_401 = lean_ctor_get(x_248, 4);
x_402 = lean_ctor_get(x_248, 5);
lean_inc(x_402);
lean_inc(x_401);
lean_inc(x_400);
lean_inc(x_397);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_248);
x_403 = lean_ctor_get(x_397, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_397, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_397, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_397, 3);
lean_inc(x_406);
x_407 = lean_ctor_get(x_397, 4);
lean_inc(x_407);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 lean_ctor_release(x_397, 2);
 lean_ctor_release(x_397, 3);
 lean_ctor_release(x_397, 4);
 x_408 = x_397;
} else {
 lean_dec_ref(x_397);
 x_408 = lean_box(0);
}
x_444 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_408)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_408;
}
lean_ctor_set(x_445, 0, x_403);
lean_ctor_set(x_445, 1, x_404);
lean_ctor_set(x_445, 2, x_444);
lean_ctor_set(x_445, 3, x_406);
lean_ctor_set(x_445, 4, x_407);
x_446 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_446, 0, x_398);
lean_ctor_set(x_446, 1, x_399);
lean_ctor_set(x_446, 2, x_445);
lean_ctor_set(x_446, 3, x_400);
lean_ctor_set(x_446, 4, x_401);
lean_ctor_set(x_446, 5, x_402);
x_447 = lean_ctor_get(x_6, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_6, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_6, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_6, 3);
lean_inc(x_450);
x_451 = lean_ctor_get(x_6, 4);
lean_inc(x_451);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_452 = x_6;
} else {
 lean_dec_ref(x_6);
 x_452 = lean_box(0);
}
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_250);
lean_ctor_set(x_453, 1, x_15);
x_454 = lean_array_push(x_449, x_453);
if (lean_is_scalar(x_452)) {
 x_455 = lean_alloc_ctor(0, 5, 0);
} else {
 x_455 = x_452;
}
lean_ctor_set(x_455, 0, x_447);
lean_ctor_set(x_455, 1, x_448);
lean_ctor_set(x_455, 2, x_454);
lean_ctor_set(x_455, 3, x_450);
lean_ctor_set(x_455, 4, x_451);
x_456 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_2, x_3, x_4, x_252, x_455, x_446);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_459, 0, x_457);
x_409 = x_459;
x_410 = x_458;
goto block_443;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_456, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_456, 1);
lean_inc(x_461);
lean_dec(x_456);
x_462 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_462, 0, x_460);
x_409 = x_462;
x_410 = x_461;
goto block_443;
}
block_443:
{
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_411 = lean_ctor_get(x_410, 2);
lean_inc(x_411);
x_412 = lean_ctor_get(x_409, 0);
lean_inc(x_412);
lean_dec(x_409);
x_413 = lean_ctor_get(x_410, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_410, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_410, 3);
lean_inc(x_415);
x_416 = lean_ctor_get(x_410, 4);
lean_inc(x_416);
x_417 = lean_ctor_get(x_410, 5);
lean_inc(x_417);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 lean_ctor_release(x_410, 5);
 x_418 = x_410;
} else {
 lean_dec_ref(x_410);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_411, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_411, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_411, 3);
lean_inc(x_421);
x_422 = lean_ctor_get(x_411, 4);
lean_inc(x_422);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 lean_ctor_release(x_411, 2);
 lean_ctor_release(x_411, 3);
 lean_ctor_release(x_411, 4);
 x_423 = x_411;
} else {
 lean_dec_ref(x_411);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(0, 5, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_419);
lean_ctor_set(x_424, 1, x_420);
lean_ctor_set(x_424, 2, x_405);
lean_ctor_set(x_424, 3, x_421);
lean_ctor_set(x_424, 4, x_422);
if (lean_is_scalar(x_418)) {
 x_425 = lean_alloc_ctor(0, 6, 0);
} else {
 x_425 = x_418;
}
lean_ctor_set(x_425, 0, x_413);
lean_ctor_set(x_425, 1, x_414);
lean_ctor_set(x_425, 2, x_424);
lean_ctor_set(x_425, 3, x_415);
lean_ctor_set(x_425, 4, x_416);
lean_ctor_set(x_425, 5, x_417);
if (lean_is_scalar(x_249)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_249;
 lean_ctor_set_tag(x_426, 1);
}
lean_ctor_set(x_426, 0, x_412);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_427 = lean_ctor_get(x_410, 2);
lean_inc(x_427);
x_428 = lean_ctor_get(x_409, 0);
lean_inc(x_428);
lean_dec(x_409);
x_429 = lean_ctor_get(x_410, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_410, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_410, 3);
lean_inc(x_431);
x_432 = lean_ctor_get(x_410, 4);
lean_inc(x_432);
x_433 = lean_ctor_get(x_410, 5);
lean_inc(x_433);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 lean_ctor_release(x_410, 5);
 x_434 = x_410;
} else {
 lean_dec_ref(x_410);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_427, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_427, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_427, 3);
lean_inc(x_437);
x_438 = lean_ctor_get(x_427, 4);
lean_inc(x_438);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 lean_ctor_release(x_427, 4);
 x_439 = x_427;
} else {
 lean_dec_ref(x_427);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_435);
lean_ctor_set(x_440, 1, x_436);
lean_ctor_set(x_440, 2, x_405);
lean_ctor_set(x_440, 3, x_437);
lean_ctor_set(x_440, 4, x_438);
if (lean_is_scalar(x_434)) {
 x_441 = lean_alloc_ctor(0, 6, 0);
} else {
 x_441 = x_434;
}
lean_ctor_set(x_441, 0, x_429);
lean_ctor_set(x_441, 1, x_430);
lean_ctor_set(x_441, 2, x_440);
lean_ctor_set(x_441, 3, x_431);
lean_ctor_set(x_441, 4, x_432);
lean_ctor_set(x_441, 5, x_433);
if (lean_is_scalar(x_249)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_249;
}
lean_ctor_set(x_442, 0, x_428);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
}
}
else
{
uint8_t x_463; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_463 = !lean_is_exclusive(x_242);
if (x_463 == 0)
{
return x_242;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_242, 0);
x_465 = lean_ctor_get(x_242, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_242);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
}
}
else
{
uint8_t x_467; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_467 = !lean_is_exclusive(x_20);
if (x_467 == 0)
{
return x_20;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_20, 0);
x_469 = lean_ctor_get(x_20, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_20);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
}
}
else
{
uint8_t x_471; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_471 = !lean_is_exclusive(x_16);
if (x_471 == 0)
{
return x_16;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_16, 0);
x_473 = lean_ctor_get(x_16, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_16);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isForall(x_8);
if (x_11 == 0)
{
size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_12 = 8192;
x_13 = l_Lean_Expr_ReplaceImpl_initCache;
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_12, x_3, x_13);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_mkForall(x_2, x_15, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__3(x_1, x_4, x_5, x_6, x_2, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_inc(x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_whnf), 3, 1);
lean_closure_set(x_14, 0, x_9);
x_15 = lean_box(x_2);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5___lambda__1___boxed), 10, 7);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_5);
lean_closure_set(x_16, 2, x_9);
lean_closure_set(x_16, 3, x_15);
lean_closure_set(x_16, 4, x_3);
lean_closure_set(x_16, 5, x_4);
lean_closure_set(x_16, 6, x_8);
x_17 = lean_array_get_size(x_10);
x_18 = lean_nat_dec_lt(x_11, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(x_14, x_16, x_12, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_16);
lean_dec(x_14);
x_20 = lean_array_fget(x_10, x_11);
lean_inc(x_12);
x_21 = l_Lean_Meta_getFVarLocalDecl(x_20, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_LocalDecl_type(x_22);
lean_dec(x_22);
lean_inc(x_12);
lean_inc(x_24);
x_25 = l_Lean_Meta_isClassQuick___main(x_24, x_12, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_20);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_11, x_28);
lean_dec(x_11);
x_11 = x_29;
x_13 = x_27;
goto _start;
}
case 1:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_24);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_32 = x_25;
} else {
 lean_dec_ref(x_25);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_11, x_34);
lean_dec(x_11);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_31, 2);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_95; uint8_t x_96; 
x_39 = lean_ctor_get(x_37, 2);
x_95 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_37, 2, x_95);
x_96 = !lean_is_exclusive(x_12);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_12, 2);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_33);
lean_ctor_set(x_98, 1, x_20);
x_99 = lean_array_push(x_97, x_98);
lean_ctor_set(x_12, 2, x_99);
x_100 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35, x_12, x_31);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_101);
x_40 = x_103;
x_41 = x_102;
goto block_94;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_100, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_100, 1);
lean_inc(x_105);
lean_dec(x_100);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_104);
x_40 = x_106;
x_41 = x_105;
goto block_94;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_107 = lean_ctor_get(x_12, 0);
x_108 = lean_ctor_get(x_12, 1);
x_109 = lean_ctor_get(x_12, 2);
x_110 = lean_ctor_get(x_12, 3);
x_111 = lean_ctor_get(x_12, 4);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_12);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_33);
lean_ctor_set(x_112, 1, x_20);
x_113 = lean_array_push(x_109, x_112);
x_114 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_108);
lean_ctor_set(x_114, 2, x_113);
lean_ctor_set(x_114, 3, x_110);
lean_ctor_set(x_114, 4, x_111);
x_115 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35, x_114, x_31);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_116);
x_40 = x_118;
x_41 = x_117;
goto block_94;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_115, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_119);
x_40 = x_121;
x_41 = x_120;
goto block_94;
}
}
block_94:
{
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec(x_40);
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_41, 2);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_42, 2);
lean_dec(x_47);
lean_ctor_set(x_42, 2, x_39);
if (lean_is_scalar(x_32)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_32;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_41);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_42, 1);
x_51 = lean_ctor_get(x_42, 3);
x_52 = lean_ctor_get(x_42, 4);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_42);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_39);
lean_ctor_set(x_53, 3, x_51);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_41, 2, x_53);
if (lean_is_scalar(x_32)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_32;
 lean_ctor_set_tag(x_54, 1);
}
lean_ctor_set(x_54, 0, x_43);
lean_ctor_set(x_54, 1, x_41);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_41, 0);
x_56 = lean_ctor_get(x_41, 1);
x_57 = lean_ctor_get(x_41, 3);
x_58 = lean_ctor_get(x_41, 4);
x_59 = lean_ctor_get(x_41, 5);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_41);
x_60 = lean_ctor_get(x_42, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_42, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_42, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_42, 4);
lean_inc(x_63);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 lean_ctor_release(x_42, 4);
 x_64 = x_42;
} else {
 lean_dec_ref(x_42);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_39);
lean_ctor_set(x_65, 3, x_62);
lean_ctor_set(x_65, 4, x_63);
x_66 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_56);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_57);
lean_ctor_set(x_66, 4, x_58);
lean_ctor_set(x_66, 5, x_59);
if (lean_is_scalar(x_32)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_32;
 lean_ctor_set_tag(x_67, 1);
}
lean_ctor_set(x_67, 0, x_43);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_68 = lean_ctor_get(x_41, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_40, 0);
lean_inc(x_69);
lean_dec(x_40);
x_70 = !lean_is_exclusive(x_41);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_41, 2);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_68, 2);
lean_dec(x_73);
lean_ctor_set(x_68, 2, x_39);
if (lean_is_scalar(x_32)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_32;
}
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_41);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_68, 0);
x_76 = lean_ctor_get(x_68, 1);
x_77 = lean_ctor_get(x_68, 3);
x_78 = lean_ctor_get(x_68, 4);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_68);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set(x_79, 2, x_39);
lean_ctor_set(x_79, 3, x_77);
lean_ctor_set(x_79, 4, x_78);
lean_ctor_set(x_41, 2, x_79);
if (lean_is_scalar(x_32)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_32;
}
lean_ctor_set(x_80, 0, x_69);
lean_ctor_set(x_80, 1, x_41);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = lean_ctor_get(x_41, 0);
x_82 = lean_ctor_get(x_41, 1);
x_83 = lean_ctor_get(x_41, 3);
x_84 = lean_ctor_get(x_41, 4);
x_85 = lean_ctor_get(x_41, 5);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_41);
x_86 = lean_ctor_get(x_68, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_68, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_68, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_68, 4);
lean_inc(x_89);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 lean_ctor_release(x_68, 2);
 lean_ctor_release(x_68, 3);
 lean_ctor_release(x_68, 4);
 x_90 = x_68;
} else {
 lean_dec_ref(x_68);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(0, 5, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_86);
lean_ctor_set(x_91, 1, x_87);
lean_ctor_set(x_91, 2, x_39);
lean_ctor_set(x_91, 3, x_88);
lean_ctor_set(x_91, 4, x_89);
x_92 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_92, 0, x_81);
lean_ctor_set(x_92, 1, x_82);
lean_ctor_set(x_92, 2, x_91);
lean_ctor_set(x_92, 3, x_83);
lean_ctor_set(x_92, 4, x_84);
lean_ctor_set(x_92, 5, x_85);
if (lean_is_scalar(x_32)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_32;
}
lean_ctor_set(x_93, 0, x_69);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_122 = lean_ctor_get(x_37, 0);
x_123 = lean_ctor_get(x_37, 1);
x_124 = lean_ctor_get(x_37, 2);
x_125 = lean_ctor_get(x_37, 3);
x_126 = lean_ctor_get(x_37, 4);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_37);
x_162 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_163 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_163, 0, x_122);
lean_ctor_set(x_163, 1, x_123);
lean_ctor_set(x_163, 2, x_162);
lean_ctor_set(x_163, 3, x_125);
lean_ctor_set(x_163, 4, x_126);
lean_ctor_set(x_31, 2, x_163);
x_164 = lean_ctor_get(x_12, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_12, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_12, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_12, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_12, 4);
lean_inc(x_168);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_169 = x_12;
} else {
 lean_dec_ref(x_12);
 x_169 = lean_box(0);
}
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_33);
lean_ctor_set(x_170, 1, x_20);
x_171 = lean_array_push(x_166, x_170);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 5, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_164);
lean_ctor_set(x_172, 1, x_165);
lean_ctor_set(x_172, 2, x_171);
lean_ctor_set(x_172, 3, x_167);
lean_ctor_set(x_172, 4, x_168);
x_173 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35, x_172, x_31);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_174);
x_127 = x_176;
x_128 = x_175;
goto block_161;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_dec(x_173);
x_179 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_179, 0, x_177);
x_127 = x_179;
x_128 = x_178;
goto block_161;
}
block_161:
{
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_129 = lean_ctor_get(x_128, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
lean_dec(x_127);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_128, 3);
lean_inc(x_133);
x_134 = lean_ctor_get(x_128, 4);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 5);
lean_inc(x_135);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 lean_ctor_release(x_128, 4);
 lean_ctor_release(x_128, 5);
 x_136 = x_128;
} else {
 lean_dec_ref(x_128);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_129, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_129, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_129, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_129, 4);
lean_inc(x_140);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 lean_ctor_release(x_129, 2);
 lean_ctor_release(x_129, 3);
 lean_ctor_release(x_129, 4);
 x_141 = x_129;
} else {
 lean_dec_ref(x_129);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 5, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_137);
lean_ctor_set(x_142, 1, x_138);
lean_ctor_set(x_142, 2, x_124);
lean_ctor_set(x_142, 3, x_139);
lean_ctor_set(x_142, 4, x_140);
if (lean_is_scalar(x_136)) {
 x_143 = lean_alloc_ctor(0, 6, 0);
} else {
 x_143 = x_136;
}
lean_ctor_set(x_143, 0, x_131);
lean_ctor_set(x_143, 1, x_132);
lean_ctor_set(x_143, 2, x_142);
lean_ctor_set(x_143, 3, x_133);
lean_ctor_set(x_143, 4, x_134);
lean_ctor_set(x_143, 5, x_135);
if (lean_is_scalar(x_32)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_32;
 lean_ctor_set_tag(x_144, 1);
}
lean_ctor_set(x_144, 0, x_130);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_145 = lean_ctor_get(x_128, 2);
lean_inc(x_145);
x_146 = lean_ctor_get(x_127, 0);
lean_inc(x_146);
lean_dec(x_127);
x_147 = lean_ctor_get(x_128, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_128, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_128, 3);
lean_inc(x_149);
x_150 = lean_ctor_get(x_128, 4);
lean_inc(x_150);
x_151 = lean_ctor_get(x_128, 5);
lean_inc(x_151);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 lean_ctor_release(x_128, 2);
 lean_ctor_release(x_128, 3);
 lean_ctor_release(x_128, 4);
 lean_ctor_release(x_128, 5);
 x_152 = x_128;
} else {
 lean_dec_ref(x_128);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_145, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_145, 1);
lean_inc(x_154);
x_155 = lean_ctor_get(x_145, 3);
lean_inc(x_155);
x_156 = lean_ctor_get(x_145, 4);
lean_inc(x_156);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 lean_ctor_release(x_145, 2);
 lean_ctor_release(x_145, 3);
 lean_ctor_release(x_145, 4);
 x_157 = x_145;
} else {
 lean_dec_ref(x_145);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 5, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_154);
lean_ctor_set(x_158, 2, x_124);
lean_ctor_set(x_158, 3, x_155);
lean_ctor_set(x_158, 4, x_156);
if (lean_is_scalar(x_152)) {
 x_159 = lean_alloc_ctor(0, 6, 0);
} else {
 x_159 = x_152;
}
lean_ctor_set(x_159, 0, x_147);
lean_ctor_set(x_159, 1, x_148);
lean_ctor_set(x_159, 2, x_158);
lean_ctor_set(x_159, 3, x_149);
lean_ctor_set(x_159, 4, x_150);
lean_ctor_set(x_159, 5, x_151);
if (lean_is_scalar(x_32)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_32;
}
lean_ctor_set(x_160, 0, x_146);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_180 = lean_ctor_get(x_31, 2);
x_181 = lean_ctor_get(x_31, 0);
x_182 = lean_ctor_get(x_31, 1);
x_183 = lean_ctor_get(x_31, 3);
x_184 = lean_ctor_get(x_31, 4);
x_185 = lean_ctor_get(x_31, 5);
lean_inc(x_185);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_180);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_31);
x_186 = lean_ctor_get(x_180, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_180, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_180, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_180, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_180, 4);
lean_inc(x_190);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 lean_ctor_release(x_180, 2);
 lean_ctor_release(x_180, 3);
 lean_ctor_release(x_180, 4);
 x_191 = x_180;
} else {
 lean_dec_ref(x_180);
 x_191 = lean_box(0);
}
x_227 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_191)) {
 x_228 = lean_alloc_ctor(0, 5, 0);
} else {
 x_228 = x_191;
}
lean_ctor_set(x_228, 0, x_186);
lean_ctor_set(x_228, 1, x_187);
lean_ctor_set(x_228, 2, x_227);
lean_ctor_set(x_228, 3, x_189);
lean_ctor_set(x_228, 4, x_190);
x_229 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_229, 0, x_181);
lean_ctor_set(x_229, 1, x_182);
lean_ctor_set(x_229, 2, x_228);
lean_ctor_set(x_229, 3, x_183);
lean_ctor_set(x_229, 4, x_184);
lean_ctor_set(x_229, 5, x_185);
x_230 = lean_ctor_get(x_12, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_12, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_12, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_12, 3);
lean_inc(x_233);
x_234 = lean_ctor_get(x_12, 4);
lean_inc(x_234);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_235 = x_12;
} else {
 lean_dec_ref(x_12);
 x_235 = lean_box(0);
}
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_33);
lean_ctor_set(x_236, 1, x_20);
x_237 = lean_array_push(x_232, x_236);
if (lean_is_scalar(x_235)) {
 x_238 = lean_alloc_ctor(0, 5, 0);
} else {
 x_238 = x_235;
}
lean_ctor_set(x_238, 0, x_230);
lean_ctor_set(x_238, 1, x_231);
lean_ctor_set(x_238, 2, x_237);
lean_ctor_set(x_238, 3, x_233);
lean_ctor_set(x_238, 4, x_234);
x_239 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_35, x_238, x_229);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_240);
x_192 = x_242;
x_193 = x_241;
goto block_226;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_239, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_239, 1);
lean_inc(x_244);
lean_dec(x_239);
x_245 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_245, 0, x_243);
x_192 = x_245;
x_193 = x_244;
goto block_226;
}
block_226:
{
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_194 = lean_ctor_get(x_193, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
lean_dec(x_192);
x_196 = lean_ctor_get(x_193, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_193, 1);
lean_inc(x_197);
x_198 = lean_ctor_get(x_193, 3);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 4);
lean_inc(x_199);
x_200 = lean_ctor_get(x_193, 5);
lean_inc(x_200);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 lean_ctor_release(x_193, 5);
 x_201 = x_193;
} else {
 lean_dec_ref(x_193);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_194, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_194, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_194, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_194, 4);
lean_inc(x_205);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 lean_ctor_release(x_194, 4);
 x_206 = x_194;
} else {
 lean_dec_ref(x_194);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(0, 5, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_202);
lean_ctor_set(x_207, 1, x_203);
lean_ctor_set(x_207, 2, x_188);
lean_ctor_set(x_207, 3, x_204);
lean_ctor_set(x_207, 4, x_205);
if (lean_is_scalar(x_201)) {
 x_208 = lean_alloc_ctor(0, 6, 0);
} else {
 x_208 = x_201;
}
lean_ctor_set(x_208, 0, x_196);
lean_ctor_set(x_208, 1, x_197);
lean_ctor_set(x_208, 2, x_207);
lean_ctor_set(x_208, 3, x_198);
lean_ctor_set(x_208, 4, x_199);
lean_ctor_set(x_208, 5, x_200);
if (lean_is_scalar(x_32)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_32;
 lean_ctor_set_tag(x_209, 1);
}
lean_ctor_set(x_209, 0, x_195);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_210 = lean_ctor_get(x_193, 2);
lean_inc(x_210);
x_211 = lean_ctor_get(x_192, 0);
lean_inc(x_211);
lean_dec(x_192);
x_212 = lean_ctor_get(x_193, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_193, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_193, 3);
lean_inc(x_214);
x_215 = lean_ctor_get(x_193, 4);
lean_inc(x_215);
x_216 = lean_ctor_get(x_193, 5);
lean_inc(x_216);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 lean_ctor_release(x_193, 5);
 x_217 = x_193;
} else {
 lean_dec_ref(x_193);
 x_217 = lean_box(0);
}
x_218 = lean_ctor_get(x_210, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_210, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_210, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_210, 4);
lean_inc(x_221);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 lean_ctor_release(x_210, 2);
 lean_ctor_release(x_210, 3);
 lean_ctor_release(x_210, 4);
 x_222 = x_210;
} else {
 lean_dec_ref(x_210);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(0, 5, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_218);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_188);
lean_ctor_set(x_223, 3, x_220);
lean_ctor_set(x_223, 4, x_221);
if (lean_is_scalar(x_217)) {
 x_224 = lean_alloc_ctor(0, 6, 0);
} else {
 x_224 = x_217;
}
lean_ctor_set(x_224, 0, x_212);
lean_ctor_set(x_224, 1, x_213);
lean_ctor_set(x_224, 2, x_223);
lean_ctor_set(x_224, 3, x_214);
lean_ctor_set(x_224, 4, x_215);
lean_ctor_set(x_224, 5, x_216);
if (lean_is_scalar(x_32)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_32;
}
lean_ctor_set(x_225, 0, x_211);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
default: 
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_25, 1);
lean_inc(x_246);
lean_dec(x_25);
lean_inc(x_12);
x_247 = l_Lean_Meta_isClassExpensive___main(x_24, x_12, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_20);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_unsigned_to_nat(1u);
x_251 = lean_nat_add(x_11, x_250);
lean_dec(x_11);
x_11 = x_251;
x_13 = x_249;
goto _start;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_253 = lean_ctor_get(x_247, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_254 = x_247;
} else {
 lean_dec_ref(x_247);
 x_254 = lean_box(0);
}
x_255 = lean_ctor_get(x_248, 0);
lean_inc(x_255);
lean_dec(x_248);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_nat_add(x_11, x_256);
lean_dec(x_11);
x_258 = !lean_is_exclusive(x_253);
if (x_258 == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_253, 2);
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_317; uint8_t x_318; 
x_261 = lean_ctor_get(x_259, 2);
x_317 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_259, 2, x_317);
x_318 = !lean_is_exclusive(x_12);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_319 = lean_ctor_get(x_12, 2);
x_320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_320, 0, x_255);
lean_ctor_set(x_320, 1, x_20);
x_321 = lean_array_push(x_319, x_320);
lean_ctor_set(x_12, 2, x_321);
x_322 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_257, x_12, x_253);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_323);
x_262 = x_325;
x_263 = x_324;
goto block_316;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_322, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_322, 1);
lean_inc(x_327);
lean_dec(x_322);
x_328 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_328, 0, x_326);
x_262 = x_328;
x_263 = x_327;
goto block_316;
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_329 = lean_ctor_get(x_12, 0);
x_330 = lean_ctor_get(x_12, 1);
x_331 = lean_ctor_get(x_12, 2);
x_332 = lean_ctor_get(x_12, 3);
x_333 = lean_ctor_get(x_12, 4);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_12);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_255);
lean_ctor_set(x_334, 1, x_20);
x_335 = lean_array_push(x_331, x_334);
x_336 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_336, 0, x_329);
lean_ctor_set(x_336, 1, x_330);
lean_ctor_set(x_336, 2, x_335);
lean_ctor_set(x_336, 3, x_332);
lean_ctor_set(x_336, 4, x_333);
x_337 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_257, x_336, x_253);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_338);
x_262 = x_340;
x_263 = x_339;
goto block_316;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_337, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_337, 1);
lean_inc(x_342);
lean_dec(x_337);
x_343 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_343, 0, x_341);
x_262 = x_343;
x_263 = x_342;
goto block_316;
}
}
block_316:
{
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_264 = lean_ctor_get(x_263, 2);
lean_inc(x_264);
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
lean_dec(x_262);
x_266 = !lean_is_exclusive(x_263);
if (x_266 == 0)
{
lean_object* x_267; uint8_t x_268; 
x_267 = lean_ctor_get(x_263, 2);
lean_dec(x_267);
x_268 = !lean_is_exclusive(x_264);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_264, 2);
lean_dec(x_269);
lean_ctor_set(x_264, 2, x_261);
if (lean_is_scalar(x_254)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_254;
 lean_ctor_set_tag(x_270, 1);
}
lean_ctor_set(x_270, 0, x_265);
lean_ctor_set(x_270, 1, x_263);
return x_270;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_271 = lean_ctor_get(x_264, 0);
x_272 = lean_ctor_get(x_264, 1);
x_273 = lean_ctor_get(x_264, 3);
x_274 = lean_ctor_get(x_264, 4);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_264);
x_275 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_275, 0, x_271);
lean_ctor_set(x_275, 1, x_272);
lean_ctor_set(x_275, 2, x_261);
lean_ctor_set(x_275, 3, x_273);
lean_ctor_set(x_275, 4, x_274);
lean_ctor_set(x_263, 2, x_275);
if (lean_is_scalar(x_254)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_254;
 lean_ctor_set_tag(x_276, 1);
}
lean_ctor_set(x_276, 0, x_265);
lean_ctor_set(x_276, 1, x_263);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_277 = lean_ctor_get(x_263, 0);
x_278 = lean_ctor_get(x_263, 1);
x_279 = lean_ctor_get(x_263, 3);
x_280 = lean_ctor_get(x_263, 4);
x_281 = lean_ctor_get(x_263, 5);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_263);
x_282 = lean_ctor_get(x_264, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_264, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_264, 3);
lean_inc(x_284);
x_285 = lean_ctor_get(x_264, 4);
lean_inc(x_285);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 lean_ctor_release(x_264, 2);
 lean_ctor_release(x_264, 3);
 lean_ctor_release(x_264, 4);
 x_286 = x_264;
} else {
 lean_dec_ref(x_264);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 5, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_282);
lean_ctor_set(x_287, 1, x_283);
lean_ctor_set(x_287, 2, x_261);
lean_ctor_set(x_287, 3, x_284);
lean_ctor_set(x_287, 4, x_285);
x_288 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_288, 0, x_277);
lean_ctor_set(x_288, 1, x_278);
lean_ctor_set(x_288, 2, x_287);
lean_ctor_set(x_288, 3, x_279);
lean_ctor_set(x_288, 4, x_280);
lean_ctor_set(x_288, 5, x_281);
if (lean_is_scalar(x_254)) {
 x_289 = lean_alloc_ctor(1, 2, 0);
} else {
 x_289 = x_254;
 lean_ctor_set_tag(x_289, 1);
}
lean_ctor_set(x_289, 0, x_265);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
}
else
{
lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_290 = lean_ctor_get(x_263, 2);
lean_inc(x_290);
x_291 = lean_ctor_get(x_262, 0);
lean_inc(x_291);
lean_dec(x_262);
x_292 = !lean_is_exclusive(x_263);
if (x_292 == 0)
{
lean_object* x_293; uint8_t x_294; 
x_293 = lean_ctor_get(x_263, 2);
lean_dec(x_293);
x_294 = !lean_is_exclusive(x_290);
if (x_294 == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_290, 2);
lean_dec(x_295);
lean_ctor_set(x_290, 2, x_261);
if (lean_is_scalar(x_254)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_254;
}
lean_ctor_set(x_296, 0, x_291);
lean_ctor_set(x_296, 1, x_263);
return x_296;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_297 = lean_ctor_get(x_290, 0);
x_298 = lean_ctor_get(x_290, 1);
x_299 = lean_ctor_get(x_290, 3);
x_300 = lean_ctor_get(x_290, 4);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_290);
x_301 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_301, 0, x_297);
lean_ctor_set(x_301, 1, x_298);
lean_ctor_set(x_301, 2, x_261);
lean_ctor_set(x_301, 3, x_299);
lean_ctor_set(x_301, 4, x_300);
lean_ctor_set(x_263, 2, x_301);
if (lean_is_scalar(x_254)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_254;
}
lean_ctor_set(x_302, 0, x_291);
lean_ctor_set(x_302, 1, x_263);
return x_302;
}
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_303 = lean_ctor_get(x_263, 0);
x_304 = lean_ctor_get(x_263, 1);
x_305 = lean_ctor_get(x_263, 3);
x_306 = lean_ctor_get(x_263, 4);
x_307 = lean_ctor_get(x_263, 5);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_263);
x_308 = lean_ctor_get(x_290, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_290, 1);
lean_inc(x_309);
x_310 = lean_ctor_get(x_290, 3);
lean_inc(x_310);
x_311 = lean_ctor_get(x_290, 4);
lean_inc(x_311);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 lean_ctor_release(x_290, 2);
 lean_ctor_release(x_290, 3);
 lean_ctor_release(x_290, 4);
 x_312 = x_290;
} else {
 lean_dec_ref(x_290);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(0, 5, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_308);
lean_ctor_set(x_313, 1, x_309);
lean_ctor_set(x_313, 2, x_261);
lean_ctor_set(x_313, 3, x_310);
lean_ctor_set(x_313, 4, x_311);
x_314 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_314, 0, x_303);
lean_ctor_set(x_314, 1, x_304);
lean_ctor_set(x_314, 2, x_313);
lean_ctor_set(x_314, 3, x_305);
lean_ctor_set(x_314, 4, x_306);
lean_ctor_set(x_314, 5, x_307);
if (lean_is_scalar(x_254)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_254;
}
lean_ctor_set(x_315, 0, x_291);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_344 = lean_ctor_get(x_259, 0);
x_345 = lean_ctor_get(x_259, 1);
x_346 = lean_ctor_get(x_259, 2);
x_347 = lean_ctor_get(x_259, 3);
x_348 = lean_ctor_get(x_259, 4);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_259);
x_384 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_344);
lean_ctor_set(x_385, 1, x_345);
lean_ctor_set(x_385, 2, x_384);
lean_ctor_set(x_385, 3, x_347);
lean_ctor_set(x_385, 4, x_348);
lean_ctor_set(x_253, 2, x_385);
x_386 = lean_ctor_get(x_12, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_12, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_12, 2);
lean_inc(x_388);
x_389 = lean_ctor_get(x_12, 3);
lean_inc(x_389);
x_390 = lean_ctor_get(x_12, 4);
lean_inc(x_390);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_391 = x_12;
} else {
 lean_dec_ref(x_12);
 x_391 = lean_box(0);
}
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_255);
lean_ctor_set(x_392, 1, x_20);
x_393 = lean_array_push(x_388, x_392);
if (lean_is_scalar(x_391)) {
 x_394 = lean_alloc_ctor(0, 5, 0);
} else {
 x_394 = x_391;
}
lean_ctor_set(x_394, 0, x_386);
lean_ctor_set(x_394, 1, x_387);
lean_ctor_set(x_394, 2, x_393);
lean_ctor_set(x_394, 3, x_389);
lean_ctor_set(x_394, 4, x_390);
x_395 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_257, x_394, x_253);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_398, 0, x_396);
x_349 = x_398;
x_350 = x_397;
goto block_383;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_395, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_395, 1);
lean_inc(x_400);
lean_dec(x_395);
x_401 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_401, 0, x_399);
x_349 = x_401;
x_350 = x_400;
goto block_383;
}
block_383:
{
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_351 = lean_ctor_get(x_350, 2);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 0);
lean_inc(x_352);
lean_dec(x_349);
x_353 = lean_ctor_get(x_350, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_350, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_350, 3);
lean_inc(x_355);
x_356 = lean_ctor_get(x_350, 4);
lean_inc(x_356);
x_357 = lean_ctor_get(x_350, 5);
lean_inc(x_357);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 lean_ctor_release(x_350, 4);
 lean_ctor_release(x_350, 5);
 x_358 = x_350;
} else {
 lean_dec_ref(x_350);
 x_358 = lean_box(0);
}
x_359 = lean_ctor_get(x_351, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_351, 1);
lean_inc(x_360);
x_361 = lean_ctor_get(x_351, 3);
lean_inc(x_361);
x_362 = lean_ctor_get(x_351, 4);
lean_inc(x_362);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 lean_ctor_release(x_351, 4);
 x_363 = x_351;
} else {
 lean_dec_ref(x_351);
 x_363 = lean_box(0);
}
if (lean_is_scalar(x_363)) {
 x_364 = lean_alloc_ctor(0, 5, 0);
} else {
 x_364 = x_363;
}
lean_ctor_set(x_364, 0, x_359);
lean_ctor_set(x_364, 1, x_360);
lean_ctor_set(x_364, 2, x_346);
lean_ctor_set(x_364, 3, x_361);
lean_ctor_set(x_364, 4, x_362);
if (lean_is_scalar(x_358)) {
 x_365 = lean_alloc_ctor(0, 6, 0);
} else {
 x_365 = x_358;
}
lean_ctor_set(x_365, 0, x_353);
lean_ctor_set(x_365, 1, x_354);
lean_ctor_set(x_365, 2, x_364);
lean_ctor_set(x_365, 3, x_355);
lean_ctor_set(x_365, 4, x_356);
lean_ctor_set(x_365, 5, x_357);
if (lean_is_scalar(x_254)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_254;
 lean_ctor_set_tag(x_366, 1);
}
lean_ctor_set(x_366, 0, x_352);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_367 = lean_ctor_get(x_350, 2);
lean_inc(x_367);
x_368 = lean_ctor_get(x_349, 0);
lean_inc(x_368);
lean_dec(x_349);
x_369 = lean_ctor_get(x_350, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_350, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_350, 3);
lean_inc(x_371);
x_372 = lean_ctor_get(x_350, 4);
lean_inc(x_372);
x_373 = lean_ctor_get(x_350, 5);
lean_inc(x_373);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 lean_ctor_release(x_350, 4);
 lean_ctor_release(x_350, 5);
 x_374 = x_350;
} else {
 lean_dec_ref(x_350);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_367, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_367, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_367, 3);
lean_inc(x_377);
x_378 = lean_ctor_get(x_367, 4);
lean_inc(x_378);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 lean_ctor_release(x_367, 2);
 lean_ctor_release(x_367, 3);
 lean_ctor_release(x_367, 4);
 x_379 = x_367;
} else {
 lean_dec_ref(x_367);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(0, 5, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_375);
lean_ctor_set(x_380, 1, x_376);
lean_ctor_set(x_380, 2, x_346);
lean_ctor_set(x_380, 3, x_377);
lean_ctor_set(x_380, 4, x_378);
if (lean_is_scalar(x_374)) {
 x_381 = lean_alloc_ctor(0, 6, 0);
} else {
 x_381 = x_374;
}
lean_ctor_set(x_381, 0, x_369);
lean_ctor_set(x_381, 1, x_370);
lean_ctor_set(x_381, 2, x_380);
lean_ctor_set(x_381, 3, x_371);
lean_ctor_set(x_381, 4, x_372);
lean_ctor_set(x_381, 5, x_373);
if (lean_is_scalar(x_254)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_254;
}
lean_ctor_set(x_382, 0, x_368);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_402 = lean_ctor_get(x_253, 2);
x_403 = lean_ctor_get(x_253, 0);
x_404 = lean_ctor_get(x_253, 1);
x_405 = lean_ctor_get(x_253, 3);
x_406 = lean_ctor_get(x_253, 4);
x_407 = lean_ctor_get(x_253, 5);
lean_inc(x_407);
lean_inc(x_406);
lean_inc(x_405);
lean_inc(x_402);
lean_inc(x_404);
lean_inc(x_403);
lean_dec(x_253);
x_408 = lean_ctor_get(x_402, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_402, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_402, 2);
lean_inc(x_410);
x_411 = lean_ctor_get(x_402, 3);
lean_inc(x_411);
x_412 = lean_ctor_get(x_402, 4);
lean_inc(x_412);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 lean_ctor_release(x_402, 2);
 lean_ctor_release(x_402, 3);
 lean_ctor_release(x_402, 4);
 x_413 = x_402;
} else {
 lean_dec_ref(x_402);
 x_413 = lean_box(0);
}
x_449 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_413)) {
 x_450 = lean_alloc_ctor(0, 5, 0);
} else {
 x_450 = x_413;
}
lean_ctor_set(x_450, 0, x_408);
lean_ctor_set(x_450, 1, x_409);
lean_ctor_set(x_450, 2, x_449);
lean_ctor_set(x_450, 3, x_411);
lean_ctor_set(x_450, 4, x_412);
x_451 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_451, 0, x_403);
lean_ctor_set(x_451, 1, x_404);
lean_ctor_set(x_451, 2, x_450);
lean_ctor_set(x_451, 3, x_405);
lean_ctor_set(x_451, 4, x_406);
lean_ctor_set(x_451, 5, x_407);
x_452 = lean_ctor_get(x_12, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_12, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_12, 2);
lean_inc(x_454);
x_455 = lean_ctor_get(x_12, 3);
lean_inc(x_455);
x_456 = lean_ctor_get(x_12, 4);
lean_inc(x_456);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 lean_ctor_release(x_12, 2);
 lean_ctor_release(x_12, 3);
 lean_ctor_release(x_12, 4);
 x_457 = x_12;
} else {
 lean_dec_ref(x_12);
 x_457 = lean_box(0);
}
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_255);
lean_ctor_set(x_458, 1, x_20);
x_459 = lean_array_push(x_454, x_458);
if (lean_is_scalar(x_457)) {
 x_460 = lean_alloc_ctor(0, 5, 0);
} else {
 x_460 = x_457;
}
lean_ctor_set(x_460, 0, x_452);
lean_ctor_set(x_460, 1, x_453);
lean_ctor_set(x_460, 2, x_459);
lean_ctor_set(x_460, 3, x_455);
lean_ctor_set(x_460, 4, x_456);
x_461 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_257, x_460, x_451);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec(x_461);
x_464 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_464, 0, x_462);
x_414 = x_464;
x_415 = x_463;
goto block_448;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_461, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_461, 1);
lean_inc(x_466);
lean_dec(x_461);
x_467 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_467, 0, x_465);
x_414 = x_467;
x_415 = x_466;
goto block_448;
}
block_448:
{
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_416 = lean_ctor_get(x_415, 2);
lean_inc(x_416);
x_417 = lean_ctor_get(x_414, 0);
lean_inc(x_417);
lean_dec(x_414);
x_418 = lean_ctor_get(x_415, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_415, 1);
lean_inc(x_419);
x_420 = lean_ctor_get(x_415, 3);
lean_inc(x_420);
x_421 = lean_ctor_get(x_415, 4);
lean_inc(x_421);
x_422 = lean_ctor_get(x_415, 5);
lean_inc(x_422);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 lean_ctor_release(x_415, 4);
 lean_ctor_release(x_415, 5);
 x_423 = x_415;
} else {
 lean_dec_ref(x_415);
 x_423 = lean_box(0);
}
x_424 = lean_ctor_get(x_416, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_416, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_416, 3);
lean_inc(x_426);
x_427 = lean_ctor_get(x_416, 4);
lean_inc(x_427);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 lean_ctor_release(x_416, 4);
 x_428 = x_416;
} else {
 lean_dec_ref(x_416);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(0, 5, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_424);
lean_ctor_set(x_429, 1, x_425);
lean_ctor_set(x_429, 2, x_410);
lean_ctor_set(x_429, 3, x_426);
lean_ctor_set(x_429, 4, x_427);
if (lean_is_scalar(x_423)) {
 x_430 = lean_alloc_ctor(0, 6, 0);
} else {
 x_430 = x_423;
}
lean_ctor_set(x_430, 0, x_418);
lean_ctor_set(x_430, 1, x_419);
lean_ctor_set(x_430, 2, x_429);
lean_ctor_set(x_430, 3, x_420);
lean_ctor_set(x_430, 4, x_421);
lean_ctor_set(x_430, 5, x_422);
if (lean_is_scalar(x_254)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_254;
 lean_ctor_set_tag(x_431, 1);
}
lean_ctor_set(x_431, 0, x_417);
lean_ctor_set(x_431, 1, x_430);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_432 = lean_ctor_get(x_415, 2);
lean_inc(x_432);
x_433 = lean_ctor_get(x_414, 0);
lean_inc(x_433);
lean_dec(x_414);
x_434 = lean_ctor_get(x_415, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_415, 1);
lean_inc(x_435);
x_436 = lean_ctor_get(x_415, 3);
lean_inc(x_436);
x_437 = lean_ctor_get(x_415, 4);
lean_inc(x_437);
x_438 = lean_ctor_get(x_415, 5);
lean_inc(x_438);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 lean_ctor_release(x_415, 4);
 lean_ctor_release(x_415, 5);
 x_439 = x_415;
} else {
 lean_dec_ref(x_415);
 x_439 = lean_box(0);
}
x_440 = lean_ctor_get(x_432, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_432, 1);
lean_inc(x_441);
x_442 = lean_ctor_get(x_432, 3);
lean_inc(x_442);
x_443 = lean_ctor_get(x_432, 4);
lean_inc(x_443);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 lean_ctor_release(x_432, 2);
 lean_ctor_release(x_432, 3);
 lean_ctor_release(x_432, 4);
 x_444 = x_432;
} else {
 lean_dec_ref(x_432);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_440);
lean_ctor_set(x_445, 1, x_441);
lean_ctor_set(x_445, 2, x_410);
lean_ctor_set(x_445, 3, x_442);
lean_ctor_set(x_445, 4, x_443);
if (lean_is_scalar(x_439)) {
 x_446 = lean_alloc_ctor(0, 6, 0);
} else {
 x_446 = x_439;
}
lean_ctor_set(x_446, 0, x_434);
lean_ctor_set(x_446, 1, x_435);
lean_ctor_set(x_446, 2, x_445);
lean_ctor_set(x_446, 3, x_436);
lean_ctor_set(x_446, 4, x_437);
lean_ctor_set(x_446, 5, x_438);
if (lean_is_scalar(x_254)) {
 x_447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_447 = x_254;
}
lean_ctor_set(x_447, 0, x_433);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
}
}
else
{
uint8_t x_468; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_468 = !lean_is_exclusive(x_247);
if (x_468 == 0)
{
return x_247;
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_469 = lean_ctor_get(x_247, 0);
x_470 = lean_ctor_get(x_247, 1);
lean_inc(x_470);
lean_inc(x_469);
lean_dec(x_247);
x_471 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
return x_471;
}
}
}
}
}
else
{
uint8_t x_472; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_472 = !lean_is_exclusive(x_25);
if (x_472 == 0)
{
return x_25;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_473 = lean_ctor_get(x_25, 0);
x_474 = lean_ctor_get(x_25, 1);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_25);
x_475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
return x_475;
}
}
}
else
{
uint8_t x_476; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_476 = !lean_is_exclusive(x_21);
if (x_476 == 0)
{
return x_21;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_21, 0);
x_478 = lean_ctor_get(x_21, 1);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_21);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
return x_479;
}
}
}
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_10 = 8192;
x_11 = l_Lean_Expr_ReplaceImpl_initCache;
x_12 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_10, x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_mkForall(x_2, x_13, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_4, x_5);
lean_inc(x_6);
x_16 = l_Lean_Meta_getFVarLocalDecl(x_15, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalDecl_type(x_17);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_19);
x_20 = l_Lean_Meta_isClassQuick___main(x_19, x_6, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 0:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_15);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_5, x_23);
lean_dec(x_5);
x_5 = x_24;
x_7 = x_22;
goto _start;
}
case 1:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_27 = x_20;
} else {
 lean_dec_ref(x_20);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
lean_dec(x_21);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_26, 2);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_90; uint8_t x_91; 
x_34 = lean_ctor_get(x_32, 2);
x_90 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_32, 2, x_90);
x_91 = !lean_is_exclusive(x_6);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_6, 2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_28);
lean_ctor_set(x_93, 1, x_15);
x_94 = lean_array_push(x_92, x_93);
lean_ctor_set(x_6, 2, x_94);
x_95 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_2, x_3, x_4, x_30, x_6, x_26);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_96);
x_35 = x_98;
x_36 = x_97;
goto block_89;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_95, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_dec(x_95);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_99);
x_35 = x_101;
x_36 = x_100;
goto block_89;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_102 = lean_ctor_get(x_6, 0);
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
x_105 = lean_ctor_get(x_6, 3);
x_106 = lean_ctor_get(x_6, 4);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_6);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_28);
lean_ctor_set(x_107, 1, x_15);
x_108 = lean_array_push(x_104, x_107);
x_109 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_103);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_105);
lean_ctor_set(x_109, 4, x_106);
x_110 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_2, x_3, x_4, x_30, x_109, x_26);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_111);
x_35 = x_113;
x_36 = x_112;
goto block_89;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 1);
lean_inc(x_115);
lean_dec(x_110);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_114);
x_35 = x_116;
x_36 = x_115;
goto block_89;
}
}
block_89:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_36, 2);
lean_dec(x_40);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_37, 2);
lean_dec(x_42);
lean_ctor_set(x_37, 2, x_34);
if (lean_is_scalar(x_27)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_27;
 lean_ctor_set_tag(x_43, 1);
}
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_36);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
x_46 = lean_ctor_get(x_37, 3);
x_47 = lean_ctor_get(x_37, 4);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_45);
lean_ctor_set(x_48, 2, x_34);
lean_ctor_set(x_48, 3, x_46);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set(x_36, 2, x_48);
if (lean_is_scalar(x_27)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_27;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_38);
lean_ctor_set(x_49, 1, x_36);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
x_52 = lean_ctor_get(x_36, 3);
x_53 = lean_ctor_get(x_36, 4);
x_54 = lean_ctor_get(x_36, 5);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_55 = lean_ctor_get(x_37, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_37, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_37, 4);
lean_inc(x_58);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 lean_ctor_release(x_37, 3);
 lean_ctor_release(x_37, 4);
 x_59 = x_37;
} else {
 lean_dec_ref(x_37);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_34);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_58);
x_61 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_51);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_52);
lean_ctor_set(x_61, 4, x_53);
lean_ctor_set(x_61, 5, x_54);
if (lean_is_scalar(x_27)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_27;
 lean_ctor_set_tag(x_62, 1);
}
lean_ctor_set(x_62, 0, x_38);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_36, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_35, 0);
lean_inc(x_64);
lean_dec(x_35);
x_65 = !lean_is_exclusive(x_36);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_36, 2);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_63, 2);
lean_dec(x_68);
lean_ctor_set(x_63, 2, x_34);
if (lean_is_scalar(x_27)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_27;
}
lean_ctor_set(x_69, 0, x_64);
lean_ctor_set(x_69, 1, x_36);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_63, 0);
x_71 = lean_ctor_get(x_63, 1);
x_72 = lean_ctor_get(x_63, 3);
x_73 = lean_ctor_get(x_63, 4);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_63);
x_74 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_74, 2, x_34);
lean_ctor_set(x_74, 3, x_72);
lean_ctor_set(x_74, 4, x_73);
lean_ctor_set(x_36, 2, x_74);
if (lean_is_scalar(x_27)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_27;
}
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_36);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_76 = lean_ctor_get(x_36, 0);
x_77 = lean_ctor_get(x_36, 1);
x_78 = lean_ctor_get(x_36, 3);
x_79 = lean_ctor_get(x_36, 4);
x_80 = lean_ctor_get(x_36, 5);
lean_inc(x_80);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_36);
x_81 = lean_ctor_get(x_63, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_63, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_63, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_63, 4);
lean_inc(x_84);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 x_85 = x_63;
} else {
 lean_dec_ref(x_63);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 5, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_81);
lean_ctor_set(x_86, 1, x_82);
lean_ctor_set(x_86, 2, x_34);
lean_ctor_set(x_86, 3, x_83);
lean_ctor_set(x_86, 4, x_84);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_77);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_78);
lean_ctor_set(x_87, 4, x_79);
lean_ctor_set(x_87, 5, x_80);
if (lean_is_scalar(x_27)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_27;
}
lean_ctor_set(x_88, 0, x_64);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_117 = lean_ctor_get(x_32, 0);
x_118 = lean_ctor_get(x_32, 1);
x_119 = lean_ctor_get(x_32, 2);
x_120 = lean_ctor_get(x_32, 3);
x_121 = lean_ctor_get(x_32, 4);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_32);
x_157 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_158 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_158, 0, x_117);
lean_ctor_set(x_158, 1, x_118);
lean_ctor_set(x_158, 2, x_157);
lean_ctor_set(x_158, 3, x_120);
lean_ctor_set(x_158, 4, x_121);
lean_ctor_set(x_26, 2, x_158);
x_159 = lean_ctor_get(x_6, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_6, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_6, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_6, 3);
lean_inc(x_162);
x_163 = lean_ctor_get(x_6, 4);
lean_inc(x_163);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_164 = x_6;
} else {
 lean_dec_ref(x_6);
 x_164 = lean_box(0);
}
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_28);
lean_ctor_set(x_165, 1, x_15);
x_166 = lean_array_push(x_161, x_165);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(0, 5, 0);
} else {
 x_167 = x_164;
}
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_166);
lean_ctor_set(x_167, 3, x_162);
lean_ctor_set(x_167, 4, x_163);
x_168 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_2, x_3, x_4, x_30, x_167, x_26);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_169);
x_122 = x_171;
x_123 = x_170;
goto block_156;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_168, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 1);
lean_inc(x_173);
lean_dec(x_168);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_172);
x_122 = x_174;
x_123 = x_173;
goto block_156;
}
block_156:
{
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_124 = lean_ctor_get(x_123, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 0);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 4);
lean_inc(x_129);
x_130 = lean_ctor_get(x_123, 5);
lean_inc(x_130);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 x_131 = x_123;
} else {
 lean_dec_ref(x_123);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_124, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_124, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_124, 3);
lean_inc(x_134);
x_135 = lean_ctor_get(x_124, 4);
lean_inc(x_135);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 x_136 = x_124;
} else {
 lean_dec_ref(x_124);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(0, 5, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_133);
lean_ctor_set(x_137, 2, x_119);
lean_ctor_set(x_137, 3, x_134);
lean_ctor_set(x_137, 4, x_135);
if (lean_is_scalar(x_131)) {
 x_138 = lean_alloc_ctor(0, 6, 0);
} else {
 x_138 = x_131;
}
lean_ctor_set(x_138, 0, x_126);
lean_ctor_set(x_138, 1, x_127);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_138, 3, x_128);
lean_ctor_set(x_138, 4, x_129);
lean_ctor_set(x_138, 5, x_130);
if (lean_is_scalar(x_27)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_27;
 lean_ctor_set_tag(x_139, 1);
}
lean_ctor_set(x_139, 0, x_125);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_140 = lean_ctor_get(x_123, 2);
lean_inc(x_140);
x_141 = lean_ctor_get(x_122, 0);
lean_inc(x_141);
lean_dec(x_122);
x_142 = lean_ctor_get(x_123, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_123, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_123, 3);
lean_inc(x_144);
x_145 = lean_ctor_get(x_123, 4);
lean_inc(x_145);
x_146 = lean_ctor_get(x_123, 5);
lean_inc(x_146);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 x_147 = x_123;
} else {
 lean_dec_ref(x_123);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_140, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_140, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_140, 3);
lean_inc(x_150);
x_151 = lean_ctor_get(x_140, 4);
lean_inc(x_151);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 lean_ctor_release(x_140, 2);
 lean_ctor_release(x_140, 3);
 lean_ctor_release(x_140, 4);
 x_152 = x_140;
} else {
 lean_dec_ref(x_140);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 5, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_148);
lean_ctor_set(x_153, 1, x_149);
lean_ctor_set(x_153, 2, x_119);
lean_ctor_set(x_153, 3, x_150);
lean_ctor_set(x_153, 4, x_151);
if (lean_is_scalar(x_147)) {
 x_154 = lean_alloc_ctor(0, 6, 0);
} else {
 x_154 = x_147;
}
lean_ctor_set(x_154, 0, x_142);
lean_ctor_set(x_154, 1, x_143);
lean_ctor_set(x_154, 2, x_153);
lean_ctor_set(x_154, 3, x_144);
lean_ctor_set(x_154, 4, x_145);
lean_ctor_set(x_154, 5, x_146);
if (lean_is_scalar(x_27)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_27;
}
lean_ctor_set(x_155, 0, x_141);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_175 = lean_ctor_get(x_26, 2);
x_176 = lean_ctor_get(x_26, 0);
x_177 = lean_ctor_get(x_26, 1);
x_178 = lean_ctor_get(x_26, 3);
x_179 = lean_ctor_get(x_26, 4);
x_180 = lean_ctor_get(x_26, 5);
lean_inc(x_180);
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_175);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_26);
x_181 = lean_ctor_get(x_175, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_175, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_175, 2);
lean_inc(x_183);
x_184 = lean_ctor_get(x_175, 3);
lean_inc(x_184);
x_185 = lean_ctor_get(x_175, 4);
lean_inc(x_185);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 lean_ctor_release(x_175, 2);
 lean_ctor_release(x_175, 3);
 lean_ctor_release(x_175, 4);
 x_186 = x_175;
} else {
 lean_dec_ref(x_175);
 x_186 = lean_box(0);
}
x_222 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_186)) {
 x_223 = lean_alloc_ctor(0, 5, 0);
} else {
 x_223 = x_186;
}
lean_ctor_set(x_223, 0, x_181);
lean_ctor_set(x_223, 1, x_182);
lean_ctor_set(x_223, 2, x_222);
lean_ctor_set(x_223, 3, x_184);
lean_ctor_set(x_223, 4, x_185);
x_224 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_224, 0, x_176);
lean_ctor_set(x_224, 1, x_177);
lean_ctor_set(x_224, 2, x_223);
lean_ctor_set(x_224, 3, x_178);
lean_ctor_set(x_224, 4, x_179);
lean_ctor_set(x_224, 5, x_180);
x_225 = lean_ctor_get(x_6, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_6, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_6, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_6, 3);
lean_inc(x_228);
x_229 = lean_ctor_get(x_6, 4);
lean_inc(x_229);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_230 = x_6;
} else {
 lean_dec_ref(x_6);
 x_230 = lean_box(0);
}
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_28);
lean_ctor_set(x_231, 1, x_15);
x_232 = lean_array_push(x_227, x_231);
if (lean_is_scalar(x_230)) {
 x_233 = lean_alloc_ctor(0, 5, 0);
} else {
 x_233 = x_230;
}
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_226);
lean_ctor_set(x_233, 2, x_232);
lean_ctor_set(x_233, 3, x_228);
lean_ctor_set(x_233, 4, x_229);
x_234 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_2, x_3, x_4, x_30, x_233, x_224);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_235);
x_187 = x_237;
x_188 = x_236;
goto block_221;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_234, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_dec(x_234);
x_240 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_240, 0, x_238);
x_187 = x_240;
x_188 = x_239;
goto block_221;
}
block_221:
{
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_189 = lean_ctor_get(x_188, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 0);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_ctor_get(x_188, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 3);
lean_inc(x_193);
x_194 = lean_ctor_get(x_188, 4);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 5);
lean_inc(x_195);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_196 = x_188;
} else {
 lean_dec_ref(x_188);
 x_196 = lean_box(0);
}
x_197 = lean_ctor_get(x_189, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_189, 3);
lean_inc(x_199);
x_200 = lean_ctor_get(x_189, 4);
lean_inc(x_200);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 lean_ctor_release(x_189, 4);
 x_201 = x_189;
} else {
 lean_dec_ref(x_189);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(0, 5, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_197);
lean_ctor_set(x_202, 1, x_198);
lean_ctor_set(x_202, 2, x_183);
lean_ctor_set(x_202, 3, x_199);
lean_ctor_set(x_202, 4, x_200);
if (lean_is_scalar(x_196)) {
 x_203 = lean_alloc_ctor(0, 6, 0);
} else {
 x_203 = x_196;
}
lean_ctor_set(x_203, 0, x_191);
lean_ctor_set(x_203, 1, x_192);
lean_ctor_set(x_203, 2, x_202);
lean_ctor_set(x_203, 3, x_193);
lean_ctor_set(x_203, 4, x_194);
lean_ctor_set(x_203, 5, x_195);
if (lean_is_scalar(x_27)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_27;
 lean_ctor_set_tag(x_204, 1);
}
lean_ctor_set(x_204, 0, x_190);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_205 = lean_ctor_get(x_188, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_187, 0);
lean_inc(x_206);
lean_dec(x_187);
x_207 = lean_ctor_get(x_188, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_188, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_188, 3);
lean_inc(x_209);
x_210 = lean_ctor_get(x_188, 4);
lean_inc(x_210);
x_211 = lean_ctor_get(x_188, 5);
lean_inc(x_211);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 lean_ctor_release(x_188, 4);
 lean_ctor_release(x_188, 5);
 x_212 = x_188;
} else {
 lean_dec_ref(x_188);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_205, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_205, 1);
lean_inc(x_214);
x_215 = lean_ctor_get(x_205, 3);
lean_inc(x_215);
x_216 = lean_ctor_get(x_205, 4);
lean_inc(x_216);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 lean_ctor_release(x_205, 2);
 lean_ctor_release(x_205, 3);
 lean_ctor_release(x_205, 4);
 x_217 = x_205;
} else {
 lean_dec_ref(x_205);
 x_217 = lean_box(0);
}
if (lean_is_scalar(x_217)) {
 x_218 = lean_alloc_ctor(0, 5, 0);
} else {
 x_218 = x_217;
}
lean_ctor_set(x_218, 0, x_213);
lean_ctor_set(x_218, 1, x_214);
lean_ctor_set(x_218, 2, x_183);
lean_ctor_set(x_218, 3, x_215);
lean_ctor_set(x_218, 4, x_216);
if (lean_is_scalar(x_212)) {
 x_219 = lean_alloc_ctor(0, 6, 0);
} else {
 x_219 = x_212;
}
lean_ctor_set(x_219, 0, x_207);
lean_ctor_set(x_219, 1, x_208);
lean_ctor_set(x_219, 2, x_218);
lean_ctor_set(x_219, 3, x_209);
lean_ctor_set(x_219, 4, x_210);
lean_ctor_set(x_219, 5, x_211);
if (lean_is_scalar(x_27)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_27;
}
lean_ctor_set(x_220, 0, x_206);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
default: 
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_20, 1);
lean_inc(x_241);
lean_dec(x_20);
lean_inc(x_6);
x_242 = l_Lean_Meta_isClassExpensive___main(x_19, x_6, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_15);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_unsigned_to_nat(1u);
x_246 = lean_nat_add(x_5, x_245);
lean_dec(x_5);
x_5 = x_246;
x_7 = x_244;
goto _start;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_248 = lean_ctor_get(x_242, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_249 = x_242;
} else {
 lean_dec_ref(x_242);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_243, 0);
lean_inc(x_250);
lean_dec(x_243);
x_251 = lean_unsigned_to_nat(1u);
x_252 = lean_nat_add(x_5, x_251);
lean_dec(x_5);
x_253 = !lean_is_exclusive(x_248);
if (x_253 == 0)
{
lean_object* x_254; uint8_t x_255; 
x_254 = lean_ctor_get(x_248, 2);
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_312; uint8_t x_313; 
x_256 = lean_ctor_get(x_254, 2);
x_312 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_254, 2, x_312);
x_313 = !lean_is_exclusive(x_6);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_314 = lean_ctor_get(x_6, 2);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_250);
lean_ctor_set(x_315, 1, x_15);
x_316 = lean_array_push(x_314, x_315);
lean_ctor_set(x_6, 2, x_316);
x_317 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_2, x_3, x_4, x_252, x_6, x_248);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_318);
x_257 = x_320;
x_258 = x_319;
goto block_311;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_317, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
lean_dec(x_317);
x_323 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_323, 0, x_321);
x_257 = x_323;
x_258 = x_322;
goto block_311;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_324 = lean_ctor_get(x_6, 0);
x_325 = lean_ctor_get(x_6, 1);
x_326 = lean_ctor_get(x_6, 2);
x_327 = lean_ctor_get(x_6, 3);
x_328 = lean_ctor_get(x_6, 4);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_6);
x_329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_329, 0, x_250);
lean_ctor_set(x_329, 1, x_15);
x_330 = lean_array_push(x_326, x_329);
x_331 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_331, 0, x_324);
lean_ctor_set(x_331, 1, x_325);
lean_ctor_set(x_331, 2, x_330);
lean_ctor_set(x_331, 3, x_327);
lean_ctor_set(x_331, 4, x_328);
x_332 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_2, x_3, x_4, x_252, x_331, x_248);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_335, 0, x_333);
x_257 = x_335;
x_258 = x_334;
goto block_311;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_332, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_332, 1);
lean_inc(x_337);
lean_dec(x_332);
x_338 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_338, 0, x_336);
x_257 = x_338;
x_258 = x_337;
goto block_311;
}
}
block_311:
{
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_259 = lean_ctor_get(x_258, 2);
lean_inc(x_259);
x_260 = lean_ctor_get(x_257, 0);
lean_inc(x_260);
lean_dec(x_257);
x_261 = !lean_is_exclusive(x_258);
if (x_261 == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_258, 2);
lean_dec(x_262);
x_263 = !lean_is_exclusive(x_259);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_259, 2);
lean_dec(x_264);
lean_ctor_set(x_259, 2, x_256);
if (lean_is_scalar(x_249)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_249;
 lean_ctor_set_tag(x_265, 1);
}
lean_ctor_set(x_265, 0, x_260);
lean_ctor_set(x_265, 1, x_258);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_259, 0);
x_267 = lean_ctor_get(x_259, 1);
x_268 = lean_ctor_get(x_259, 3);
x_269 = lean_ctor_get(x_259, 4);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_259);
x_270 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_267);
lean_ctor_set(x_270, 2, x_256);
lean_ctor_set(x_270, 3, x_268);
lean_ctor_set(x_270, 4, x_269);
lean_ctor_set(x_258, 2, x_270);
if (lean_is_scalar(x_249)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_249;
 lean_ctor_set_tag(x_271, 1);
}
lean_ctor_set(x_271, 0, x_260);
lean_ctor_set(x_271, 1, x_258);
return x_271;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_272 = lean_ctor_get(x_258, 0);
x_273 = lean_ctor_get(x_258, 1);
x_274 = lean_ctor_get(x_258, 3);
x_275 = lean_ctor_get(x_258, 4);
x_276 = lean_ctor_get(x_258, 5);
lean_inc(x_276);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_258);
x_277 = lean_ctor_get(x_259, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_259, 1);
lean_inc(x_278);
x_279 = lean_ctor_get(x_259, 3);
lean_inc(x_279);
x_280 = lean_ctor_get(x_259, 4);
lean_inc(x_280);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 lean_ctor_release(x_259, 2);
 lean_ctor_release(x_259, 3);
 lean_ctor_release(x_259, 4);
 x_281 = x_259;
} else {
 lean_dec_ref(x_259);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(0, 5, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_277);
lean_ctor_set(x_282, 1, x_278);
lean_ctor_set(x_282, 2, x_256);
lean_ctor_set(x_282, 3, x_279);
lean_ctor_set(x_282, 4, x_280);
x_283 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_283, 0, x_272);
lean_ctor_set(x_283, 1, x_273);
lean_ctor_set(x_283, 2, x_282);
lean_ctor_set(x_283, 3, x_274);
lean_ctor_set(x_283, 4, x_275);
lean_ctor_set(x_283, 5, x_276);
if (lean_is_scalar(x_249)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_249;
 lean_ctor_set_tag(x_284, 1);
}
lean_ctor_set(x_284, 0, x_260);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
else
{
lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_285 = lean_ctor_get(x_258, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_257, 0);
lean_inc(x_286);
lean_dec(x_257);
x_287 = !lean_is_exclusive(x_258);
if (x_287 == 0)
{
lean_object* x_288; uint8_t x_289; 
x_288 = lean_ctor_get(x_258, 2);
lean_dec(x_288);
x_289 = !lean_is_exclusive(x_285);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_285, 2);
lean_dec(x_290);
lean_ctor_set(x_285, 2, x_256);
if (lean_is_scalar(x_249)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_249;
}
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_258);
return x_291;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_292 = lean_ctor_get(x_285, 0);
x_293 = lean_ctor_get(x_285, 1);
x_294 = lean_ctor_get(x_285, 3);
x_295 = lean_ctor_get(x_285, 4);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_285);
x_296 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_296, 0, x_292);
lean_ctor_set(x_296, 1, x_293);
lean_ctor_set(x_296, 2, x_256);
lean_ctor_set(x_296, 3, x_294);
lean_ctor_set(x_296, 4, x_295);
lean_ctor_set(x_258, 2, x_296);
if (lean_is_scalar(x_249)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_249;
}
lean_ctor_set(x_297, 0, x_286);
lean_ctor_set(x_297, 1, x_258);
return x_297;
}
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_298 = lean_ctor_get(x_258, 0);
x_299 = lean_ctor_get(x_258, 1);
x_300 = lean_ctor_get(x_258, 3);
x_301 = lean_ctor_get(x_258, 4);
x_302 = lean_ctor_get(x_258, 5);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_258);
x_303 = lean_ctor_get(x_285, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_285, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_285, 3);
lean_inc(x_305);
x_306 = lean_ctor_get(x_285, 4);
lean_inc(x_306);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 lean_ctor_release(x_285, 2);
 lean_ctor_release(x_285, 3);
 lean_ctor_release(x_285, 4);
 x_307 = x_285;
} else {
 lean_dec_ref(x_285);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(0, 5, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_303);
lean_ctor_set(x_308, 1, x_304);
lean_ctor_set(x_308, 2, x_256);
lean_ctor_set(x_308, 3, x_305);
lean_ctor_set(x_308, 4, x_306);
x_309 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_309, 0, x_298);
lean_ctor_set(x_309, 1, x_299);
lean_ctor_set(x_309, 2, x_308);
lean_ctor_set(x_309, 3, x_300);
lean_ctor_set(x_309, 4, x_301);
lean_ctor_set(x_309, 5, x_302);
if (lean_is_scalar(x_249)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_249;
}
lean_ctor_set(x_310, 0, x_286);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_339 = lean_ctor_get(x_254, 0);
x_340 = lean_ctor_get(x_254, 1);
x_341 = lean_ctor_get(x_254, 2);
x_342 = lean_ctor_get(x_254, 3);
x_343 = lean_ctor_get(x_254, 4);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_254);
x_379 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_380 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_380, 0, x_339);
lean_ctor_set(x_380, 1, x_340);
lean_ctor_set(x_380, 2, x_379);
lean_ctor_set(x_380, 3, x_342);
lean_ctor_set(x_380, 4, x_343);
lean_ctor_set(x_248, 2, x_380);
x_381 = lean_ctor_get(x_6, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_6, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_6, 2);
lean_inc(x_383);
x_384 = lean_ctor_get(x_6, 3);
lean_inc(x_384);
x_385 = lean_ctor_get(x_6, 4);
lean_inc(x_385);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_386 = x_6;
} else {
 lean_dec_ref(x_6);
 x_386 = lean_box(0);
}
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_250);
lean_ctor_set(x_387, 1, x_15);
x_388 = lean_array_push(x_383, x_387);
if (lean_is_scalar(x_386)) {
 x_389 = lean_alloc_ctor(0, 5, 0);
} else {
 x_389 = x_386;
}
lean_ctor_set(x_389, 0, x_381);
lean_ctor_set(x_389, 1, x_382);
lean_ctor_set(x_389, 2, x_388);
lean_ctor_set(x_389, 3, x_384);
lean_ctor_set(x_389, 4, x_385);
x_390 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_2, x_3, x_4, x_252, x_389, x_248);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_393, 0, x_391);
x_344 = x_393;
x_345 = x_392;
goto block_378;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_390, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_390, 1);
lean_inc(x_395);
lean_dec(x_390);
x_396 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_396, 0, x_394);
x_344 = x_396;
x_345 = x_395;
goto block_378;
}
block_378:
{
if (lean_obj_tag(x_344) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_346 = lean_ctor_get(x_345, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_344, 0);
lean_inc(x_347);
lean_dec(x_344);
x_348 = lean_ctor_get(x_345, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_345, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_345, 3);
lean_inc(x_350);
x_351 = lean_ctor_get(x_345, 4);
lean_inc(x_351);
x_352 = lean_ctor_get(x_345, 5);
lean_inc(x_352);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 lean_ctor_release(x_345, 4);
 lean_ctor_release(x_345, 5);
 x_353 = x_345;
} else {
 lean_dec_ref(x_345);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_346, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_346, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_346, 3);
lean_inc(x_356);
x_357 = lean_ctor_get(x_346, 4);
lean_inc(x_357);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 lean_ctor_release(x_346, 2);
 lean_ctor_release(x_346, 3);
 lean_ctor_release(x_346, 4);
 x_358 = x_346;
} else {
 lean_dec_ref(x_346);
 x_358 = lean_box(0);
}
if (lean_is_scalar(x_358)) {
 x_359 = lean_alloc_ctor(0, 5, 0);
} else {
 x_359 = x_358;
}
lean_ctor_set(x_359, 0, x_354);
lean_ctor_set(x_359, 1, x_355);
lean_ctor_set(x_359, 2, x_341);
lean_ctor_set(x_359, 3, x_356);
lean_ctor_set(x_359, 4, x_357);
if (lean_is_scalar(x_353)) {
 x_360 = lean_alloc_ctor(0, 6, 0);
} else {
 x_360 = x_353;
}
lean_ctor_set(x_360, 0, x_348);
lean_ctor_set(x_360, 1, x_349);
lean_ctor_set(x_360, 2, x_359);
lean_ctor_set(x_360, 3, x_350);
lean_ctor_set(x_360, 4, x_351);
lean_ctor_set(x_360, 5, x_352);
if (lean_is_scalar(x_249)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_249;
 lean_ctor_set_tag(x_361, 1);
}
lean_ctor_set(x_361, 0, x_347);
lean_ctor_set(x_361, 1, x_360);
return x_361;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_362 = lean_ctor_get(x_345, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_344, 0);
lean_inc(x_363);
lean_dec(x_344);
x_364 = lean_ctor_get(x_345, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_345, 1);
lean_inc(x_365);
x_366 = lean_ctor_get(x_345, 3);
lean_inc(x_366);
x_367 = lean_ctor_get(x_345, 4);
lean_inc(x_367);
x_368 = lean_ctor_get(x_345, 5);
lean_inc(x_368);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 lean_ctor_release(x_345, 3);
 lean_ctor_release(x_345, 4);
 lean_ctor_release(x_345, 5);
 x_369 = x_345;
} else {
 lean_dec_ref(x_345);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_362, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_362, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_362, 3);
lean_inc(x_372);
x_373 = lean_ctor_get(x_362, 4);
lean_inc(x_373);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 lean_ctor_release(x_362, 2);
 lean_ctor_release(x_362, 3);
 lean_ctor_release(x_362, 4);
 x_374 = x_362;
} else {
 lean_dec_ref(x_362);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(0, 5, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_370);
lean_ctor_set(x_375, 1, x_371);
lean_ctor_set(x_375, 2, x_341);
lean_ctor_set(x_375, 3, x_372);
lean_ctor_set(x_375, 4, x_373);
if (lean_is_scalar(x_369)) {
 x_376 = lean_alloc_ctor(0, 6, 0);
} else {
 x_376 = x_369;
}
lean_ctor_set(x_376, 0, x_364);
lean_ctor_set(x_376, 1, x_365);
lean_ctor_set(x_376, 2, x_375);
lean_ctor_set(x_376, 3, x_366);
lean_ctor_set(x_376, 4, x_367);
lean_ctor_set(x_376, 5, x_368);
if (lean_is_scalar(x_249)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_249;
}
lean_ctor_set(x_377, 0, x_363);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_397 = lean_ctor_get(x_248, 2);
x_398 = lean_ctor_get(x_248, 0);
x_399 = lean_ctor_get(x_248, 1);
x_400 = lean_ctor_get(x_248, 3);
x_401 = lean_ctor_get(x_248, 4);
x_402 = lean_ctor_get(x_248, 5);
lean_inc(x_402);
lean_inc(x_401);
lean_inc(x_400);
lean_inc(x_397);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_248);
x_403 = lean_ctor_get(x_397, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_397, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_397, 2);
lean_inc(x_405);
x_406 = lean_ctor_get(x_397, 3);
lean_inc(x_406);
x_407 = lean_ctor_get(x_397, 4);
lean_inc(x_407);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 lean_ctor_release(x_397, 2);
 lean_ctor_release(x_397, 3);
 lean_ctor_release(x_397, 4);
 x_408 = x_397;
} else {
 lean_dec_ref(x_397);
 x_408 = lean_box(0);
}
x_444 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_408)) {
 x_445 = lean_alloc_ctor(0, 5, 0);
} else {
 x_445 = x_408;
}
lean_ctor_set(x_445, 0, x_403);
lean_ctor_set(x_445, 1, x_404);
lean_ctor_set(x_445, 2, x_444);
lean_ctor_set(x_445, 3, x_406);
lean_ctor_set(x_445, 4, x_407);
x_446 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_446, 0, x_398);
lean_ctor_set(x_446, 1, x_399);
lean_ctor_set(x_446, 2, x_445);
lean_ctor_set(x_446, 3, x_400);
lean_ctor_set(x_446, 4, x_401);
lean_ctor_set(x_446, 5, x_402);
x_447 = lean_ctor_get(x_6, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_6, 1);
lean_inc(x_448);
x_449 = lean_ctor_get(x_6, 2);
lean_inc(x_449);
x_450 = lean_ctor_get(x_6, 3);
lean_inc(x_450);
x_451 = lean_ctor_get(x_6, 4);
lean_inc(x_451);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 x_452 = x_6;
} else {
 lean_dec_ref(x_6);
 x_452 = lean_box(0);
}
x_453 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_453, 0, x_250);
lean_ctor_set(x_453, 1, x_15);
x_454 = lean_array_push(x_449, x_453);
if (lean_is_scalar(x_452)) {
 x_455 = lean_alloc_ctor(0, 5, 0);
} else {
 x_455 = x_452;
}
lean_ctor_set(x_455, 0, x_447);
lean_ctor_set(x_455, 1, x_448);
lean_ctor_set(x_455, 2, x_454);
lean_ctor_set(x_455, 3, x_450);
lean_ctor_set(x_455, 4, x_451);
x_456 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_2, x_3, x_4, x_252, x_455, x_446);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
x_459 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_459, 0, x_457);
x_409 = x_459;
x_410 = x_458;
goto block_443;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_456, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_456, 1);
lean_inc(x_461);
lean_dec(x_456);
x_462 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_462, 0, x_460);
x_409 = x_462;
x_410 = x_461;
goto block_443;
}
block_443:
{
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_411 = lean_ctor_get(x_410, 2);
lean_inc(x_411);
x_412 = lean_ctor_get(x_409, 0);
lean_inc(x_412);
lean_dec(x_409);
x_413 = lean_ctor_get(x_410, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_410, 1);
lean_inc(x_414);
x_415 = lean_ctor_get(x_410, 3);
lean_inc(x_415);
x_416 = lean_ctor_get(x_410, 4);
lean_inc(x_416);
x_417 = lean_ctor_get(x_410, 5);
lean_inc(x_417);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 lean_ctor_release(x_410, 5);
 x_418 = x_410;
} else {
 lean_dec_ref(x_410);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_411, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_411, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_411, 3);
lean_inc(x_421);
x_422 = lean_ctor_get(x_411, 4);
lean_inc(x_422);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 lean_ctor_release(x_411, 2);
 lean_ctor_release(x_411, 3);
 lean_ctor_release(x_411, 4);
 x_423 = x_411;
} else {
 lean_dec_ref(x_411);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(0, 5, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_419);
lean_ctor_set(x_424, 1, x_420);
lean_ctor_set(x_424, 2, x_405);
lean_ctor_set(x_424, 3, x_421);
lean_ctor_set(x_424, 4, x_422);
if (lean_is_scalar(x_418)) {
 x_425 = lean_alloc_ctor(0, 6, 0);
} else {
 x_425 = x_418;
}
lean_ctor_set(x_425, 0, x_413);
lean_ctor_set(x_425, 1, x_414);
lean_ctor_set(x_425, 2, x_424);
lean_ctor_set(x_425, 3, x_415);
lean_ctor_set(x_425, 4, x_416);
lean_ctor_set(x_425, 5, x_417);
if (lean_is_scalar(x_249)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_249;
 lean_ctor_set_tag(x_426, 1);
}
lean_ctor_set(x_426, 0, x_412);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_427 = lean_ctor_get(x_410, 2);
lean_inc(x_427);
x_428 = lean_ctor_get(x_409, 0);
lean_inc(x_428);
lean_dec(x_409);
x_429 = lean_ctor_get(x_410, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_410, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_410, 3);
lean_inc(x_431);
x_432 = lean_ctor_get(x_410, 4);
lean_inc(x_432);
x_433 = lean_ctor_get(x_410, 5);
lean_inc(x_433);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 lean_ctor_release(x_410, 2);
 lean_ctor_release(x_410, 3);
 lean_ctor_release(x_410, 4);
 lean_ctor_release(x_410, 5);
 x_434 = x_410;
} else {
 lean_dec_ref(x_410);
 x_434 = lean_box(0);
}
x_435 = lean_ctor_get(x_427, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_427, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_427, 3);
lean_inc(x_437);
x_438 = lean_ctor_get(x_427, 4);
lean_inc(x_438);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 lean_ctor_release(x_427, 4);
 x_439 = x_427;
} else {
 lean_dec_ref(x_427);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(0, 5, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_435);
lean_ctor_set(x_440, 1, x_436);
lean_ctor_set(x_440, 2, x_405);
lean_ctor_set(x_440, 3, x_437);
lean_ctor_set(x_440, 4, x_438);
if (lean_is_scalar(x_434)) {
 x_441 = lean_alloc_ctor(0, 6, 0);
} else {
 x_441 = x_434;
}
lean_ctor_set(x_441, 0, x_429);
lean_ctor_set(x_441, 1, x_430);
lean_ctor_set(x_441, 2, x_440);
lean_ctor_set(x_441, 3, x_431);
lean_ctor_set(x_441, 4, x_432);
lean_ctor_set(x_441, 5, x_433);
if (lean_is_scalar(x_249)) {
 x_442 = lean_alloc_ctor(0, 2, 0);
} else {
 x_442 = x_249;
}
lean_ctor_set(x_442, 0, x_428);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
}
}
else
{
uint8_t x_463; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_463 = !lean_is_exclusive(x_242);
if (x_463 == 0)
{
return x_242;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_242, 0);
x_465 = lean_ctor_get(x_242, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_242);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
}
}
else
{
uint8_t x_467; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_467 = !lean_is_exclusive(x_20);
if (x_467 == 0)
{
return x_20;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_20, 0);
x_469 = lean_ctor_get(x_20, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_20);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
}
}
else
{
uint8_t x_471; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_471 = !lean_is_exclusive(x_16);
if (x_471 == 0)
{
return x_16;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_16, 0);
x_473 = lean_ctor_get(x_16, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_16);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (lean_obj_tag(x_7) == 7)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_7, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_29 = lean_array_get_size(x_5);
x_30 = lean_expr_instantiate_rev_range(x_26, x_6, x_29, x_5);
lean_dec(x_29);
lean_dec(x_26);
x_31 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = (uint8_t)((x_28 << 24) >> 61);
lean_inc(x_32);
x_35 = lean_local_ctx_mk_local_decl(x_4, x_32, x_25, x_30, x_34);
x_36 = l_Lean_mkFVar(x_32);
x_37 = lean_array_push(x_5, x_36);
x_4 = x_35;
x_5 = x_37;
x_7 = x_27;
x_9 = x_33;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint64_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_7, 2);
lean_inc(x_41);
x_42 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
x_43 = lean_ctor_get(x_3, 0);
lean_inc(x_43);
x_44 = lean_array_get_size(x_5);
x_45 = lean_nat_dec_lt(x_44, x_43);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_3);
x_46 = lean_expr_instantiate_rev_range(x_7, x_6, x_44, x_5);
lean_dec(x_44);
lean_dec(x_7);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_8, 1);
lean_dec(x_48);
lean_ctor_set(x_8, 1, x_4);
lean_inc(x_5);
x_49 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_5, x_46, x_5, x_6, x_8, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 2);
x_52 = lean_ctor_get(x_8, 3);
x_53 = lean_ctor_get(x_8, 4);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_4);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_52);
lean_ctor_set(x_54, 4, x_53);
lean_inc(x_5);
x_55 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_5, x_46, x_5, x_6, x_54, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_7);
x_56 = lean_expr_instantiate_rev_range(x_40, x_6, x_44, x_5);
lean_dec(x_44);
lean_dec(x_40);
x_57 = l_Lean_Meta_mkFreshId___rarg(x_9);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = (uint8_t)((x_42 << 24) >> 61);
lean_inc(x_58);
x_61 = lean_local_ctx_mk_local_decl(x_4, x_58, x_39, x_56, x_60);
x_62 = l_Lean_mkFVar(x_58);
x_63 = lean_array_push(x_5, x_62);
x_4 = x_61;
x_5 = x_63;
x_7 = x_41;
x_9 = x_59;
goto _start;
}
}
}
else
{
lean_object* x_65; 
x_65 = lean_box(0);
x_10 = x_65;
goto block_24;
}
block_24:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_dec(x_10);
x_11 = lean_array_get_size(x_5);
x_12 = lean_expr_instantiate_rev_range(x_7, x_6, x_11, x_5);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_4);
if (x_2 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_5);
x_15 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_5, x_12, x_5, x_6, x_8, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
else
{
lean_object* x_16; 
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_5, x_6, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 2);
x_19 = lean_ctor_get(x_8, 3);
x_20 = lean_ctor_get(x_8, 4);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
if (x_2 == 0)
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_5);
x_22 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_5, x_12, x_5, x_6, x_21, x_9);
lean_dec(x_5);
lean_dec(x_1);
return x_22;
}
else
{
lean_object* x_23; 
lean_inc(x_6);
lean_inc(x_5);
x_23 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_11, x_12, x_5, x_6, x_21, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
}
}
}
}
lean_object* l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
lean_inc(x_2);
x_6 = l_Lean_Meta_whnf(x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Expr_isForall(x_7);
if (x_9 == 0)
{
size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_3);
x_10 = 8192;
x_11 = l_Array_empty___closed__1;
x_12 = l_Lean_Expr_ReplaceImpl_initCache;
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_11, x_10, x_2, x_12);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_mkForall(x_11, x_14, x_4, x_8);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = 1;
x_18 = l_Array_empty___closed__1;
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__3(x_1, x_17, x_3, x_16, x_18, x_19, x_7, x_4, x_8);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 4);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = l_Lean_TraceState_Inhabited___closed__1;
lean_ctor_set(x_16, 4, x_20);
lean_inc(x_3);
x_21 = l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__2(x_3, x_14, x_15, x_19, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_5);
x_24 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_5, x_6, x_23, x_18);
lean_ctor_set(x_10, 1, x_22);
x_25 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(x_1, x_2, x_3, x_12, x_5, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_4, 1, x_27);
lean_ctor_set(x_25, 0, x_4);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_4, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_free_object(x_4);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
return x_25;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_25, 0);
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_25);
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
lean_free_object(x_10);
lean_dec(x_13);
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_5);
x_38 = l___private_Lean_Elab_Term_2__fromMetaException(x_5, x_2, x_36);
x_39 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_5, x_6, x_37, x_18);
lean_ctor_set(x_21, 1, x_39);
lean_ctor_set(x_21, 0, x_38);
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
lean_inc(x_5);
x_42 = l___private_Lean_Elab_Term_2__fromMetaException(x_5, x_2, x_40);
x_43 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_5, x_6, x_41, x_18);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
x_47 = lean_ctor_get(x_16, 2);
x_48 = lean_ctor_get(x_16, 3);
x_49 = lean_ctor_get(x_16, 4);
x_50 = lean_ctor_get(x_16, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_51 = lean_ctor_get(x_5, 0);
lean_inc(x_51);
x_52 = l_Lean_TraceState_Inhabited___closed__1;
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set(x_53, 2, x_47);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_50);
lean_inc(x_3);
x_54 = l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__2(x_3, x_14, x_15, x_51, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_5);
x_57 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_5, x_6, x_56, x_49);
lean_ctor_set(x_10, 1, x_55);
x_58 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(x_1, x_2, x_3, x_12, x_5, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
lean_ctor_set(x_4, 1, x_59);
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_4);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
lean_free_object(x_4);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_65 = x_58;
} else {
 lean_dec_ref(x_58);
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
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_free_object(x_10);
lean_dec(x_13);
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_1);
x_67 = lean_ctor_get(x_54, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_69 = x_54;
} else {
 lean_dec_ref(x_54);
 x_69 = lean_box(0);
}
lean_inc(x_5);
x_70 = l___private_Lean_Elab_Term_2__fromMetaException(x_5, x_2, x_67);
x_71 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_5, x_6, x_68, x_49);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_73 = lean_ctor_get(x_4, 1);
x_74 = lean_ctor_get(x_10, 0);
x_75 = lean_ctor_get(x_10, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_10);
lean_inc(x_1);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_1);
x_77 = lean_ctor_get(x_6, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 3);
lean_inc(x_81);
x_82 = lean_ctor_get(x_77, 4);
lean_inc(x_82);
x_83 = lean_ctor_get(x_77, 5);
lean_inc(x_83);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 lean_ctor_release(x_77, 2);
 lean_ctor_release(x_77, 3);
 lean_ctor_release(x_77, 4);
 lean_ctor_release(x_77, 5);
 x_84 = x_77;
} else {
 lean_dec_ref(x_77);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_5, 0);
lean_inc(x_85);
x_86 = l_Lean_TraceState_Inhabited___closed__1;
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 6, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_79);
lean_ctor_set(x_87, 2, x_80);
lean_ctor_set(x_87, 3, x_81);
lean_ctor_set(x_87, 4, x_86);
lean_ctor_set(x_87, 5, x_83);
lean_inc(x_3);
x_88 = l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__2(x_3, x_75, x_76, x_85, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_5);
x_91 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_5, x_6, x_90, x_82);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_74);
lean_ctor_set(x_92, 1, x_89);
x_93 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(x_1, x_2, x_3, x_73, x_5, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_96 = x_93;
} else {
 lean_dec_ref(x_93);
 x_96 = lean_box(0);
}
lean_ctor_set(x_4, 1, x_94);
lean_ctor_set(x_4, 0, x_92);
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_4);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_92);
lean_free_object(x_4);
x_98 = lean_ctor_get(x_93, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_93, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_100 = x_93;
} else {
 lean_dec_ref(x_93);
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
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_74);
lean_free_object(x_4);
lean_dec(x_73);
lean_dec(x_3);
lean_dec(x_1);
x_102 = lean_ctor_get(x_88, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_88, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_104 = x_88;
} else {
 lean_dec_ref(x_88);
 x_104 = lean_box(0);
}
lean_inc(x_5);
x_105 = l___private_Lean_Elab_Term_2__fromMetaException(x_5, x_2, x_102);
x_106 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_5, x_6, x_103, x_82);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_108 = lean_ctor_get(x_4, 0);
x_109 = lean_ctor_get(x_4, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_4);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_112 = x_108;
} else {
 lean_dec_ref(x_108);
 x_112 = lean_box(0);
}
lean_inc(x_1);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_1);
x_114 = lean_ctor_get(x_6, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 2);
lean_inc(x_117);
x_118 = lean_ctor_get(x_114, 3);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 4);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 5);
lean_inc(x_120);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 lean_ctor_release(x_114, 2);
 lean_ctor_release(x_114, 3);
 lean_ctor_release(x_114, 4);
 lean_ctor_release(x_114, 5);
 x_121 = x_114;
} else {
 lean_dec_ref(x_114);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_5, 0);
lean_inc(x_122);
x_123 = l_Lean_TraceState_Inhabited___closed__1;
if (lean_is_scalar(x_121)) {
 x_124 = lean_alloc_ctor(0, 6, 0);
} else {
 x_124 = x_121;
}
lean_ctor_set(x_124, 0, x_115);
lean_ctor_set(x_124, 1, x_116);
lean_ctor_set(x_124, 2, x_117);
lean_ctor_set(x_124, 3, x_118);
lean_ctor_set(x_124, 4, x_123);
lean_ctor_set(x_124, 5, x_120);
lean_inc(x_3);
x_125 = l___private_Lean_Meta_Basic_6__forallTelescopeReducingAux___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__2(x_3, x_111, x_113, x_122, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_5);
x_128 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_5, x_6, x_127, x_119);
if (lean_is_scalar(x_112)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_112;
}
lean_ctor_set(x_129, 0, x_110);
lean_ctor_set(x_129, 1, x_126);
x_130 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(x_1, x_2, x_3, x_109, x_5, x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_131);
if (lean_is_scalar(x_133)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_133;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_132);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_129);
x_136 = lean_ctor_get(x_130, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_130, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_138 = x_130;
} else {
 lean_dec_ref(x_130);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_112);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_3);
lean_dec(x_1);
x_140 = lean_ctor_get(x_125, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_125, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_142 = x_125;
} else {
 lean_dec_ref(x_125);
 x_142 = lean_box(0);
}
lean_inc(x_5);
x_143 = l___private_Lean_Elab_Term_2__fromMetaException(x_5, x_2, x_140);
x_144 = l___private_Lean_Elab_Term_3__fromMetaState(x_2, x_5, x_6, x_141, x_119);
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_142;
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_10, 0);
x_14 = lean_ctor_get(x_10, 1);
x_15 = lean_ctor_get(x_10, 2);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_16 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(x_1, x_2, x_3, x_15, x_5, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_10, 2, x_17);
x_19 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__8(x_1, x_2, x_3, x_12, x_5, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_4, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_free_object(x_4);
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
lean_free_object(x_10);
lean_dec(x_14);
lean_dec(x_13);
lean_free_object(x_4);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_3);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_4, 1);
x_34 = lean_ctor_get(x_10, 0);
x_35 = lean_ctor_get(x_10, 1);
x_36 = lean_ctor_get(x_10, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_10);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_37 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(x_1, x_2, x_3, x_36, x_5, x_6);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_38);
x_41 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__8(x_1, x_2, x_3, x_33, x_5, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
lean_ctor_set(x_4, 1, x_42);
lean_ctor_set(x_4, 0, x_40);
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_40);
lean_free_object(x_4);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_48 = x_41;
} else {
 lean_dec_ref(x_41);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_35);
lean_dec(x_34);
lean_free_object(x_4);
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_50 = lean_ctor_get(x_37, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_52 = x_37;
} else {
 lean_dec_ref(x_37);
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
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_4, 0);
x_55 = lean_ctor_get(x_4, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_4);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_54, 2);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 lean_ctor_release(x_54, 2);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
x_60 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(x_1, x_2, x_3, x_58, x_5, x_6);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 3, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_57);
lean_ctor_set(x_63, 2, x_61);
x_64 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__8(x_1, x_2, x_3, x_55, x_5, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_67 = x_64;
} else {
 lean_dec_ref(x_64);
 x_67 = lean_box(0);
}
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_65);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_63);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_64, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_74 = lean_ctor_get(x_60, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_76 = x_60;
} else {
 lean_dec_ref(x_60);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Elab_Command_InductiveView_inhabited;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get(x_8, x_1, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l___private_Lean_Elab_Inductive_29__mkIndFVar2Const(x_1, x_2, x_3);
x_13 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__8(x_4, x_11, x_12, x_5, x_6, x_7);
lean_dec(x_11);
return x_13;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5___lambda__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__5(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
return x_15;
}
}
lean_object* l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withNewLocalInstances___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Basic_5__forallTelescopeReducingAuxAux___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__3(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__7(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM___main___at___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___spec__8(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_7, sizeof(void*)*5);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_12 = l_Std_HashMapImp_insert___at_Lean_ClassState_addEntry___spec__6(x_4, x_8, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 7);
lean_inc(x_8);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__1(x_7, x_8, x_9, x_4);
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
x_4 = x_10;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_31__mkCtor2InferMod(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Std_HashMap_inhabited___closed__1;
x_4 = l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__2(x_1, x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at___private_Lean_Elab_Inductive_31__mkCtor2InferMod___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_31__mkCtor2InferMod___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Inductive_31__mkCtor2InferMod(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Std_HashMap_find_x21___rarg___closed__1;
x_2 = lean_unsigned_to_nat(162u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_Std_PersistentHashMap_find_x21___rarg___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1(x_1, x_2, x_8);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(x_2, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_Bool_Inhabited;
x_14 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___closed__1;
x_15 = lean_box(x_13);
x_16 = lean_panic_fn(x_15, x_14);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = l_Lean_Expr_inferImplicit___main(x_10, x_1, x_18);
lean_ctor_set(x_6, 1, x_19);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = l_Lean_Expr_inferImplicit___main(x_10, x_1, x_20);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_12, 0);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; 
x_24 = 1;
x_25 = l_Lean_Expr_inferImplicit___main(x_10, x_1, x_24);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_26; lean_object* x_27; 
x_26 = 0;
x_27 = l_Lean_Expr_inferImplicit___main(x_10, x_1, x_26);
lean_ctor_set(x_6, 1, x_27);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_31 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1(x_1, x_2, x_28);
x_32 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(x_2, x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = l_Bool_Inhabited;
x_34 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___closed__1;
x_35 = lean_box(x_33);
x_36 = lean_panic_fn(x_35, x_34);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 1;
x_39 = l_Lean_Expr_inferImplicit___main(x_30, x_1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_40);
return x_3;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_41 = 0;
x_42 = l_Lean_Expr_inferImplicit___main(x_30, x_1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_29);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_43);
return x_3;
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
lean_dec(x_32);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
uint8_t x_46; lean_object* x_47; lean_object* x_48; 
x_46 = 1;
x_47 = l_Lean_Expr_inferImplicit___main(x_30, x_1, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_29);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_48);
return x_3;
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_49 = 0;
x_50 = l_Lean_Expr_inferImplicit___main(x_30, x_1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_29);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_3, 1, x_31);
lean_ctor_set(x_3, 0, x_51);
return x_3;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_3, 0);
x_53 = lean_ctor_get(x_3, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_3);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_56 = x_52;
} else {
 lean_dec_ref(x_52);
 x_56 = lean_box(0);
}
x_57 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1(x_1, x_2, x_53);
x_58 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(x_2, x_54);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = l_Bool_Inhabited;
x_60 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___closed__1;
x_61 = lean_box(x_59);
x_62 = lean_panic_fn(x_61, x_60);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = 1;
x_65 = l_Lean_Expr_inferImplicit___main(x_55, x_1, x_64);
if (lean_is_scalar(x_56)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_56;
}
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_57);
return x_67;
}
else
{
uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = 0;
x_69 = l_Lean_Expr_inferImplicit___main(x_55, x_1, x_68);
if (lean_is_scalar(x_56)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_56;
}
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_57);
return x_71;
}
}
else
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_58, 0);
lean_inc(x_72);
lean_dec(x_58);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = 1;
x_75 = l_Lean_Expr_inferImplicit___main(x_55, x_1, x_74);
if (lean_is_scalar(x_56)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_56;
}
lean_ctor_set(x_76, 0, x_54);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_57);
return x_77;
}
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = 0;
x_79 = l_Lean_Expr_inferImplicit___main(x_55, x_1, x_78);
if (lean_is_scalar(x_56)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_56;
}
lean_ctor_set(x_80, 0, x_54);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_57);
return x_81;
}
}
}
}
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_6, 2);
x_10 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1(x_1, x_2, x_9);
lean_ctor_set(x_6, 2, x_10);
x_11 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__2(x_1, x_2, x_8);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
x_16 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1(x_1, x_2, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__2(x_1, x_2, x_12);
lean_ctor_set(x_3, 1, x_18);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_3, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_3);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 2);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 lean_ctor_release(x_19, 2);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1(x_1, x_2, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 3, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__2(x_1, x_2, x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_32__applyInferMod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_Inductive_31__mkCtor2InferMod(x_1);
x_5 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__2(x_2, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Inductive_32__applyInferMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_32__applyInferMod(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_33__mkInductiveDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_6, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_6, x_12);
lean_dec(x_6);
x_14 = lean_nat_sub(x_5, x_13);
x_15 = lean_nat_sub(x_14, x_12);
lean_dec(x_14);
x_16 = l_Lean_Expr_Inhabited;
x_17 = lean_array_get(x_16, x_4, x_15);
x_18 = l_Lean_Elab_Command_ElabHeaderResult_inhabited;
x_19 = lean_array_get(x_18, x_2, x_15);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
lean_inc(x_8);
lean_inc(x_3);
x_21 = l_Lean_Elab_Term_mkForall(x_1, x_3, x_20, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_8);
lean_inc(x_3);
x_24 = l___private_Lean_Elab_Inductive_16__elabCtors(x_17, x_3, x_19, x_8, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_7);
x_6 = x_13;
x_7 = x_30;
x_9 = x_26;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
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
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_get_size(x_10);
x_14 = lean_nat_add(x_13, x_1);
lean_dec(x_13);
lean_inc(x_11);
x_15 = l_List_mapM___main___at___private_Lean_Elab_Inductive_27__updateParams___spec__2(x_2, x_10, x_3, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_11);
x_18 = l___private_Lean_Elab_Inductive_18__levelMVarToParam___rarg(x_16, x_11, x_17);
if (x_4 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
x_21 = l___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive(x_19);
x_22 = l_Lean_Elab_Command_sortDeclLevelParams(x_5, x_6, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
lean_dec(x_14);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Elab_Term_throwError___rarg(x_2, x_25, x_11, x_20);
lean_dec(x_2);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_22, 0);
lean_inc(x_27);
lean_dec(x_22);
lean_inc(x_14);
lean_inc(x_27);
x_28 = l___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts(x_7, x_8, x_27, x_14, x_19, x_11, x_20);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = l___private_Lean_Elab_Inductive_32__applyInferMod(x_7, x_14, x_30);
x_32 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_14);
lean_ctor_set(x_32, 2, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*3, x_9);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = l___private_Lean_Elab_Inductive_32__applyInferMod(x_7, x_14, x_33);
x_36 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_14);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*3, x_9);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_27);
lean_dec(x_14);
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
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_18, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 1);
lean_inc(x_43);
lean_dec(x_18);
lean_inc(x_11);
lean_inc(x_2);
x_44 = l___private_Lean_Elab_Inductive_23__updateResultingUniverse(x_2, x_14, x_42, x_11, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_45);
x_47 = l___private_Lean_Elab_Inductive_28__collectLevelParamsInInductive(x_45);
x_48 = l_Lean_Elab_Command_sortDeclLevelParams(x_5, x_6, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
lean_dec(x_14);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_Elab_Term_throwError___rarg(x_2, x_51, x_11, x_46);
lean_dec(x_2);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_2);
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
lean_dec(x_48);
lean_inc(x_14);
lean_inc(x_53);
x_54 = l___private_Lean_Elab_Inductive_30__replaceIndFVarsWithConsts(x_7, x_8, x_53, x_14, x_45, x_11, x_46);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l___private_Lean_Elab_Inductive_32__applyInferMod(x_7, x_14, x_56);
x_58 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_14);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_9);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_54, 0);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_54);
x_61 = l___private_Lean_Elab_Inductive_32__applyInferMod(x_7, x_14, x_59);
x_62 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_62, 0, x_53);
lean_ctor_set(x_62, 1, x_14);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_9);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
uint8_t x_64; 
lean_dec(x_53);
lean_dec(x_14);
x_64 = !lean_is_exclusive(x_54);
if (x_64 == 0)
{
return x_54;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_54, 0);
x_66 = lean_ctor_get(x_54, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_54);
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
uint8_t x_68; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_44);
if (x_68 == 0)
{
return x_44;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_44, 0);
x_70 = lean_ctor_get(x_44, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_44);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_15);
if (x_72 == 0)
{
return x_15;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_15, 0);
x_74 = lean_ctor_get(x_15, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_15);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_get_size(x_8);
x_13 = lean_box(0);
x_14 = lean_array_get_size(x_1);
lean_inc(x_10);
lean_inc(x_14);
x_15 = l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_33__mkInductiveDecl___spec__1(x_2, x_3, x_8, x_9, x_14, x_14, x_13, x_10, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_List_reverse___rarg(x_16);
x_19 = 0;
x_20 = lean_box(0);
lean_inc(x_10);
x_21 = l___private_Lean_Elab_SyntheticMVars_11__synthesizeSyntheticMVarsAux___main(x_19, x_20, x_10, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_inc(x_10);
lean_inc(x_18);
x_23 = l___private_Lean_Elab_Inductive_19__getResultingUniverse(x_2, x_18, x_10, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_10);
x_26 = l_Lean_Elab_Command_shouldInferResultUniverse(x_2, x_24, x_10, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(x_6);
lean_inc(x_18);
lean_inc(x_2);
x_30 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__1___boxed), 12, 9);
lean_closure_set(x_30, 0, x_12);
lean_closure_set(x_30, 1, x_2);
lean_closure_set(x_30, 2, x_18);
lean_closure_set(x_30, 3, x_27);
lean_closure_set(x_30, 4, x_4);
lean_closure_set(x_30, 5, x_5);
lean_closure_set(x_30, 6, x_1);
lean_closure_set(x_30, 7, x_9);
lean_closure_set(x_30, 8, x_29);
x_31 = l___private_Lean_Elab_Inductive_26__withUsed___rarg(x_2, x_7, x_18, x_30, x_10, x_28);
lean_dec(x_2);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_36; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
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
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_21);
if (x_40 == 0)
{
return x_21;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_21, 0);
x_42 = lean_ctor_get(x_21, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_21);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_5 = l_Lean_Elab_Command_InductiveView_inhabited;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_2, x_6);
x_8 = l_Lean_Elab_Term_getLevelNames(x_3, x_4);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_7, 4);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*2 + 3);
lean_dec(x_12);
x_14 = lean_ctor_get(x_7, 0);
lean_inc(x_14);
lean_dec(x_7);
lean_inc(x_3);
x_15 = l___private_Lean_Elab_Inductive_4__checkLevelNames(x_2, x_3, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_3, 6);
lean_dec(x_18);
lean_inc(x_11);
lean_ctor_set(x_3, 6, x_11);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l___private_Lean_Elab_Inductive_12__elabHeader(x_2, x_3, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(x_13);
lean_inc(x_20);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__2___boxed), 11, 7);
lean_closure_set(x_23, 0, x_2);
lean_closure_set(x_23, 1, x_14);
lean_closure_set(x_23, 2, x_20);
lean_closure_set(x_23, 3, x_9);
lean_closure_set(x_23, 4, x_11);
lean_closure_set(x_23, 5, x_22);
lean_closure_set(x_23, 6, x_1);
x_24 = l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg(x_20, x_23, x_3, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_3);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_9);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_ctor_get(x_3, 1);
x_31 = lean_ctor_get(x_3, 2);
x_32 = lean_ctor_get(x_3, 3);
x_33 = lean_ctor_get(x_3, 4);
x_34 = lean_ctor_get(x_3, 5);
x_35 = lean_ctor_get(x_3, 7);
x_36 = lean_ctor_get(x_3, 8);
x_37 = lean_ctor_get(x_3, 9);
x_38 = lean_ctor_get_uint8(x_3, sizeof(void*)*10);
x_39 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 1);
x_40 = lean_ctor_get_uint8(x_3, sizeof(void*)*10 + 2);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_3);
lean_inc(x_11);
x_41 = lean_alloc_ctor(0, 10, 3);
lean_ctor_set(x_41, 0, x_29);
lean_ctor_set(x_41, 1, x_30);
lean_ctor_set(x_41, 2, x_31);
lean_ctor_set(x_41, 3, x_32);
lean_ctor_set(x_41, 4, x_33);
lean_ctor_set(x_41, 5, x_34);
lean_ctor_set(x_41, 6, x_11);
lean_ctor_set(x_41, 7, x_35);
lean_ctor_set(x_41, 8, x_36);
lean_ctor_set(x_41, 9, x_37);
lean_ctor_set_uint8(x_41, sizeof(void*)*10, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*10 + 1, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*10 + 2, x_40);
lean_inc(x_41);
lean_inc(x_2);
x_42 = l___private_Lean_Elab_Inductive_12__elabHeader(x_2, x_41, x_16);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_box(x_13);
lean_inc(x_43);
x_46 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__2___boxed), 11, 7);
lean_closure_set(x_46, 0, x_2);
lean_closure_set(x_46, 1, x_14);
lean_closure_set(x_46, 2, x_43);
lean_closure_set(x_46, 3, x_9);
lean_closure_set(x_46, 4, x_11);
lean_closure_set(x_46, 5, x_45);
lean_closure_set(x_46, 6, x_1);
x_47 = l___private_Lean_Elab_Inductive_14__withInductiveLocalDecls___rarg(x_43, x_46, x_41, x_44);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_50 = x_42;
} else {
 lean_dec_ref(x_42);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_15);
if (x_52 == 0)
{
return x_15;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_15, 0);
x_54 = lean_ctor_get(x_15, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_15);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_33__mkInductiveDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Nat_foldMAux___main___at___private_Lean_Elab_Inductive_33__mkInductiveDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_9);
lean_dec(x_9);
x_15 = l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__1(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_14, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l___private_Lean_Elab_Inductive_33__mkInductiveDecl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_6, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_array_fget(x_5, x_6);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_13, 3);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_7);
x_17 = l___private_Lean_Elab_Command_2__getState(x_7, x_8);
if (x_3 == 0)
{
uint8_t x_217; 
x_217 = 0;
x_18 = x_217;
goto block_216;
}
else
{
uint8_t x_218; 
x_218 = 1;
x_18 = x_218;
goto block_216;
}
block_216:
{
uint8_t x_19; 
if (x_3 == 0)
{
uint8_t x_214; 
x_214 = 0;
x_19 = x_214;
goto block_213;
}
else
{
if (x_1 == 0)
{
uint8_t x_215; 
x_215 = 0;
x_19 = x_215;
goto block_213;
}
else
{
x_19 = x_2;
goto block_213;
}
}
block_213:
{
uint8_t x_20; 
if (x_19 == 0)
{
uint8_t x_211; 
x_211 = 0;
x_20 = x_211;
goto block_210;
}
else
{
uint8_t x_212; 
x_212 = 1;
x_20 = x_212;
goto block_210;
}
block_210:
{
uint8_t x_21; 
if (x_3 == 0)
{
uint8_t x_209; 
x_209 = 0;
x_21 = x_209;
goto block_208;
}
else
{
x_21 = x_4;
goto block_208;
}
block_208:
{
uint8_t x_22; 
if (x_21 == 0)
{
uint8_t x_206; 
x_206 = 0;
x_22 = x_206;
goto block_205;
}
else
{
uint8_t x_207; 
x_207 = 1;
x_22 = x_207;
goto block_205;
}
block_205:
{
lean_object* x_23; lean_object* x_58; lean_object* x_90; 
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_17, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_17, 1);
lean_inc(x_123);
lean_dec(x_17);
x_124 = !lean_is_exclusive(x_122);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_122, 0);
x_126 = lean_mk_rec_on(x_125, x_16);
lean_ctor_set(x_122, 0, x_126);
lean_inc(x_7);
x_127 = l___private_Lean_Elab_Command_3__setState(x_122, x_7, x_123);
if (lean_obj_tag(x_127) == 0)
{
if (x_18 == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_90 = x_128;
goto block_121;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_7);
x_130 = l___private_Lean_Elab_Command_2__getState(x_7, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = !lean_is_exclusive(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_131, 0);
x_135 = lean_mk_cases_on(x_134, x_16);
lean_ctor_set(x_131, 0, x_135);
lean_inc(x_7);
x_136 = l___private_Lean_Elab_Command_3__setState(x_131, x_7, x_132);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_90 = x_137;
goto block_121;
}
else
{
uint8_t x_138; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_138 = !lean_is_exclusive(x_136);
if (x_138 == 0)
{
return x_136;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_136, 0);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_136);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_142 = lean_ctor_get(x_131, 0);
x_143 = lean_ctor_get(x_131, 1);
x_144 = lean_ctor_get(x_131, 2);
x_145 = lean_ctor_get(x_131, 3);
x_146 = lean_ctor_get(x_131, 4);
x_147 = lean_ctor_get(x_131, 5);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_131);
x_148 = lean_mk_cases_on(x_142, x_16);
x_149 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_143);
lean_ctor_set(x_149, 2, x_144);
lean_ctor_set(x_149, 3, x_145);
lean_ctor_set(x_149, 4, x_146);
lean_ctor_set(x_149, 5, x_147);
lean_inc(x_7);
x_150 = l___private_Lean_Elab_Command_3__setState(x_149, x_7, x_132);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_90 = x_151;
goto block_121;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_156 = !lean_is_exclusive(x_130);
if (x_156 == 0)
{
return x_130;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_130, 0);
x_158 = lean_ctor_get(x_130, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_130);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
}
else
{
uint8_t x_160; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_160 = !lean_is_exclusive(x_127);
if (x_160 == 0)
{
return x_127;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_127, 0);
x_162 = lean_ctor_get(x_127, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_127);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_164 = lean_ctor_get(x_122, 0);
x_165 = lean_ctor_get(x_122, 1);
x_166 = lean_ctor_get(x_122, 2);
x_167 = lean_ctor_get(x_122, 3);
x_168 = lean_ctor_get(x_122, 4);
x_169 = lean_ctor_get(x_122, 5);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_122);
x_170 = lean_mk_rec_on(x_164, x_16);
x_171 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_165);
lean_ctor_set(x_171, 2, x_166);
lean_ctor_set(x_171, 3, x_167);
lean_ctor_set(x_171, 4, x_168);
lean_ctor_set(x_171, 5, x_169);
lean_inc(x_7);
x_172 = l___private_Lean_Elab_Command_3__setState(x_171, x_7, x_123);
if (lean_obj_tag(x_172) == 0)
{
if (x_18 == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec(x_172);
x_90 = x_173;
goto block_121;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
lean_inc(x_7);
x_175 = l___private_Lean_Elab_Command_2__getState(x_7, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_176, 2);
lean_inc(x_180);
x_181 = lean_ctor_get(x_176, 3);
lean_inc(x_181);
x_182 = lean_ctor_get(x_176, 4);
lean_inc(x_182);
x_183 = lean_ctor_get(x_176, 5);
lean_inc(x_183);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 lean_ctor_release(x_176, 2);
 lean_ctor_release(x_176, 3);
 lean_ctor_release(x_176, 4);
 lean_ctor_release(x_176, 5);
 x_184 = x_176;
} else {
 lean_dec_ref(x_176);
 x_184 = lean_box(0);
}
x_185 = lean_mk_cases_on(x_178, x_16);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 6, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_179);
lean_ctor_set(x_186, 2, x_180);
lean_ctor_set(x_186, 3, x_181);
lean_ctor_set(x_186, 4, x_182);
lean_ctor_set(x_186, 5, x_183);
lean_inc(x_7);
x_187 = l___private_Lean_Elab_Command_3__setState(x_186, x_7, x_177);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_90 = x_188;
goto block_121;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_191 = x_187;
} else {
 lean_dec_ref(x_187);
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
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_193 = lean_ctor_get(x_175, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_175, 1);
lean_inc(x_194);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_195 = x_175;
} else {
 lean_dec_ref(x_175);
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
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_197 = lean_ctor_get(x_172, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_172, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_199 = x_172;
} else {
 lean_dec_ref(x_172);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_201 = !lean_is_exclusive(x_17);
if (x_201 == 0)
{
return x_17;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_17, 0);
x_203 = lean_ctor_get(x_17, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_17);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
block_57:
{
if (x_22 == 0)
{
lean_dec(x_16);
x_6 = x_15;
x_8 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_inc(x_7);
x_25 = l___private_Lean_Elab_Command_2__getState(x_7, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_mk_ibelow(x_29, x_16);
lean_dec(x_16);
lean_ctor_set(x_26, 0, x_30);
lean_inc(x_7);
x_31 = l___private_Lean_Elab_Command_3__setState(x_26, x_7, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_6 = x_15;
x_8 = x_32;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_15);
lean_dec(x_7);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 0);
x_36 = lean_ctor_get(x_31, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_31);
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
x_38 = lean_ctor_get(x_26, 0);
x_39 = lean_ctor_get(x_26, 1);
x_40 = lean_ctor_get(x_26, 2);
x_41 = lean_ctor_get(x_26, 3);
x_42 = lean_ctor_get(x_26, 4);
x_43 = lean_ctor_get(x_26, 5);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_26);
x_44 = lean_mk_ibelow(x_38, x_16);
lean_dec(x_16);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
lean_ctor_set(x_45, 2, x_40);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_42);
lean_ctor_set(x_45, 5, x_43);
lean_inc(x_7);
x_46 = l___private_Lean_Elab_Command_3__setState(x_45, x_7, x_27);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_6 = x_15;
x_8 = x_47;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_15);
lean_dec(x_7);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
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
else
{
uint8_t x_53; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_25, 0);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
block_89:
{
if (x_22 == 0)
{
x_23 = x_58;
goto block_57;
}
else
{
lean_object* x_59; 
lean_inc(x_7);
x_59 = l___private_Lean_Elab_Command_2__getState(x_7, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_mk_below(x_63, x_16);
lean_ctor_set(x_60, 0, x_64);
lean_inc(x_7);
x_65 = l___private_Lean_Elab_Command_3__setState(x_60, x_7, x_61);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_23 = x_66;
goto block_57;
}
else
{
uint8_t x_67; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_65, 0);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_65);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_60, 0);
x_72 = lean_ctor_get(x_60, 1);
x_73 = lean_ctor_get(x_60, 2);
x_74 = lean_ctor_get(x_60, 3);
x_75 = lean_ctor_get(x_60, 4);
x_76 = lean_ctor_get(x_60, 5);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_60);
x_77 = lean_mk_below(x_71, x_16);
x_78 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_74);
lean_ctor_set(x_78, 4, x_75);
lean_ctor_set(x_78, 5, x_76);
lean_inc(x_7);
x_79 = l___private_Lean_Elab_Command_3__setState(x_78, x_7, x_61);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_23 = x_80;
goto block_57;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_85 = !lean_is_exclusive(x_59);
if (x_85 == 0)
{
return x_59;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_59, 0);
x_87 = lean_ctor_get(x_59, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_59);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
block_121:
{
if (x_20 == 0)
{
x_58 = x_90;
goto block_89;
}
else
{
lean_object* x_91; 
lean_inc(x_7);
x_91 = l___private_Lean_Elab_Command_2__getState(x_7, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = !lean_is_exclusive(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_92, 0);
x_96 = lean_mk_no_confusion(x_95, x_16);
lean_ctor_set(x_92, 0, x_96);
lean_inc(x_7);
x_97 = l___private_Lean_Elab_Command_3__setState(x_92, x_7, x_93);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_58 = x_98;
goto block_89;
}
else
{
uint8_t x_99; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_99 = !lean_is_exclusive(x_97);
if (x_99 == 0)
{
return x_97;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_97, 0);
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_97);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_103 = lean_ctor_get(x_92, 0);
x_104 = lean_ctor_get(x_92, 1);
x_105 = lean_ctor_get(x_92, 2);
x_106 = lean_ctor_get(x_92, 3);
x_107 = lean_ctor_get(x_92, 4);
x_108 = lean_ctor_get(x_92, 5);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_92);
x_109 = lean_mk_no_confusion(x_103, x_16);
x_110 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_104);
lean_ctor_set(x_110, 2, x_105);
lean_ctor_set(x_110, 3, x_106);
lean_ctor_set(x_110, 4, x_107);
lean_ctor_set(x_110, 5, x_108);
lean_inc(x_7);
x_111 = l___private_Lean_Elab_Command_3__setState(x_110, x_7, x_93);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_58 = x_112;
goto block_89;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_115 = x_111;
} else {
 lean_dec_ref(x_111);
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
}
else
{
uint8_t x_117; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_7);
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
}
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_14 = lean_ctor_get(x_11, 3);
lean_inc(x_14);
lean_dec(x_11);
if (x_1 == 0)
{
uint8_t x_86; 
x_86 = 0;
x_15 = x_86;
goto block_85;
}
else
{
x_15 = x_2;
goto block_85;
}
block_85:
{
uint8_t x_16; 
if (x_15 == 0)
{
uint8_t x_83; 
x_83 = 0;
x_16 = x_83;
goto block_82;
}
else
{
uint8_t x_84; 
x_84 = 1;
x_16 = x_84;
goto block_82;
}
block_82:
{
lean_object* x_17; 
if (x_16 == 0)
{
x_17 = x_6;
goto block_51;
}
else
{
lean_object* x_52; 
lean_inc(x_5);
x_52 = l___private_Lean_Elab_Command_2__getState(x_5, x_6);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
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
x_57 = lean_mk_brec_on(x_56, x_14);
lean_ctor_set(x_53, 0, x_57);
lean_inc(x_5);
x_58 = l___private_Lean_Elab_Command_3__setState(x_53, x_5, x_54);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_17 = x_59;
goto block_51;
}
else
{
uint8_t x_60; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_ctor_get(x_58, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_58);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_ctor_get(x_53, 0);
x_65 = lean_ctor_get(x_53, 1);
x_66 = lean_ctor_get(x_53, 2);
x_67 = lean_ctor_get(x_53, 3);
x_68 = lean_ctor_get(x_53, 4);
x_69 = lean_ctor_get(x_53, 5);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_53);
x_70 = lean_mk_brec_on(x_64, x_14);
x_71 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_67);
lean_ctor_set(x_71, 4, x_68);
lean_ctor_set(x_71, 5, x_69);
lean_inc(x_5);
x_72 = l___private_Lean_Elab_Command_3__setState(x_71, x_5, x_54);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_17 = x_73;
goto block_51;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_76 = x_72;
} else {
 lean_dec_ref(x_72);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_52);
if (x_78 == 0)
{
return x_52;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_52, 0);
x_80 = lean_ctor_get(x_52, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_52);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
block_51:
{
if (x_16 == 0)
{
lean_dec(x_14);
x_4 = x_13;
x_6 = x_17;
goto _start;
}
else
{
lean_object* x_19; 
lean_inc(x_5);
x_19 = l___private_Lean_Elab_Command_2__getState(x_5, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_mk_binduction_on(x_23, x_14);
lean_dec(x_14);
lean_ctor_set(x_20, 0, x_24);
lean_inc(x_5);
x_25 = l___private_Lean_Elab_Command_3__setState(x_20, x_5, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_4 = x_13;
x_6 = x_26;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_13);
lean_dec(x_5);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
x_34 = lean_ctor_get(x_20, 2);
x_35 = lean_ctor_get(x_20, 3);
x_36 = lean_ctor_get(x_20, 4);
x_37 = lean_ctor_get(x_20, 5);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_38 = lean_mk_binduction_on(x_32, x_14);
lean_dec(x_14);
x_39 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_33);
lean_ctor_set(x_39, 2, x_34);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 4, x_36);
lean_ctor_set(x_39, 5, x_37);
lean_inc(x_5);
x_40 = l___private_Lean_Elab_Command_3__setState(x_39, x_5, x_21);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_4 = x_13;
x_6 = x_41;
goto _start;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_5);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_45 = x_40;
} else {
 lean_dec_ref(x_40);
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
}
}
else
{
uint8_t x_47; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_19);
if (x_47 == 0)
{
return x_19;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_19, 0);
x_49 = lean_ctor_get(x_19, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_19);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
}
}
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUnit");
return x_1;
}
}
lean_object* _init_l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Elab_Command_getEnv(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_5);
x_8 = l_Lean_Environment_contains(x_5, x_7);
x_9 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_5);
x_10 = l_Lean_Environment_contains(x_5, x_9);
x_11 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2;
lean_inc(x_5);
x_12 = l_Lean_Environment_contains(x_5, x_11);
x_13 = l_Lean_Expr_prod_x3f___closed__2;
x_14 = l_Lean_Environment_contains(x_5, x_13);
x_15 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_16 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1(x_8, x_10, x_12, x_14, x_1, x_15, x_2, x_6);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2(x_12, x_14, x_1, x_15, x_2, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_4);
if (x_23 == 0)
{
return x_4;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_4);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__1(x_9, x_10, x_11, x_12, x_5, x_6, x_7, x_8);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Array_forMAux___main___at___private_Lean_Elab_Inductive_34__mkAuxConstructions___spec__2(x_7, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_34__mkAuxConstructions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabInductiveViews___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_18 = l_Array_forMAux___main___at_Lean_Elab_Command_applyAttributes___spec__1(x_1, x_13, x_16, x_15, x_17, x_4, x_5);
lean_dec(x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_3 = x_12;
x_5 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_12);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Inductive_33__mkInductiveDecl(x_2, x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_4 = l_Lean_Elab_Command_InductiveView_inhabited;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get(x_4, x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_34 = lean_ctor_get(x_6, 3);
lean_inc(x_34);
lean_dec(x_6);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
lean_inc(x_1);
x_36 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInductiveViews___lambda__1), 4, 1);
lean_closure_set(x_36, 0, x_1);
lean_inc(x_2);
x_37 = l___private_Lean_Elab_Command_2__getState(x_2, x_3);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_Command_8__getVarDecls(x_38);
lean_dec(x_38);
lean_inc(x_2);
x_41 = l___private_Lean_Elab_Command_2__getState(x_2, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_Command_6__mkTermContext(x_2, x_42, x_35);
x_45 = l___private_Lean_Elab_Command_7__mkTermState(x_42);
lean_dec(x_42);
x_46 = l_Lean_Elab_Term_elabBinders___rarg(x_40, x_36, x_44, x_45);
lean_dec(x_40);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
lean_inc(x_2);
x_49 = l___private_Lean_Elab_Command_2__getState(x_2, x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_50, 3);
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_ctor_get(x_48, 2);
lean_inc(x_55);
lean_dec(x_48);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_51, 5);
lean_dec(x_57);
x_58 = lean_ctor_get(x_51, 1);
lean_dec(x_58);
x_59 = lean_ctor_get(x_51, 0);
lean_dec(x_59);
lean_ctor_set(x_51, 5, x_54);
lean_ctor_set(x_51, 1, x_55);
lean_ctor_set(x_51, 0, x_53);
lean_inc(x_2);
x_60 = l___private_Lean_Elab_Command_3__setState(x_51, x_2, x_52);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_8 = x_47;
x_9 = x_61;
goto block_33;
}
else
{
uint8_t x_62; 
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_60);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_51, 2);
x_67 = lean_ctor_get(x_51, 3);
x_68 = lean_ctor_get(x_51, 4);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_51);
x_69 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_69, 0, x_53);
lean_ctor_set(x_69, 1, x_55);
lean_ctor_set(x_69, 2, x_66);
lean_ctor_set(x_69, 3, x_67);
lean_ctor_set(x_69, 4, x_68);
lean_ctor_set(x_69, 5, x_54);
lean_inc(x_2);
x_70 = l___private_Lean_Elab_Command_3__setState(x_69, x_2, x_52);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_8 = x_47;
x_9 = x_71;
goto block_33;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_74 = x_70;
} else {
 lean_dec_ref(x_70);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_49);
if (x_76 == 0)
{
return x_49;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_49, 0);
x_78 = lean_ctor_get(x_49, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_49);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_46, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_7);
lean_dec(x_1);
x_81 = lean_ctor_get(x_46, 1);
lean_inc(x_81);
lean_dec(x_46);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_2);
x_83 = l___private_Lean_Elab_Command_2__getState(x_2, x_43);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_84, 3);
lean_inc(x_88);
lean_dec(x_84);
x_89 = lean_ctor_get(x_81, 2);
lean_inc(x_89);
lean_dec(x_81);
x_90 = !lean_is_exclusive(x_85);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_85, 5);
lean_dec(x_91);
x_92 = lean_ctor_get(x_85, 1);
lean_dec(x_92);
x_93 = lean_ctor_get(x_85, 0);
lean_dec(x_93);
lean_ctor_set(x_85, 5, x_88);
lean_ctor_set(x_85, 1, x_89);
lean_ctor_set(x_85, 0, x_87);
x_94 = l___private_Lean_Elab_Command_3__setState(x_85, x_2, x_86);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 0, x_82);
return x_94;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_82);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_82);
x_99 = !lean_is_exclusive(x_94);
if (x_99 == 0)
{
return x_94;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_94, 0);
x_101 = lean_ctor_get(x_94, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_94);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_85, 2);
x_104 = lean_ctor_get(x_85, 3);
x_105 = lean_ctor_get(x_85, 4);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_85);
x_106 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_106, 0, x_87);
lean_ctor_set(x_106, 1, x_89);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set(x_106, 3, x_104);
lean_ctor_set(x_106, 4, x_105);
lean_ctor_set(x_106, 5, x_88);
x_107 = l___private_Lean_Elab_Command_3__setState(x_106, x_2, x_86);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
 lean_ctor_set_tag(x_110, 1);
}
lean_ctor_set(x_110, 0, x_82);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_82);
x_111 = lean_ctor_get(x_107, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_113 = x_107;
} else {
 lean_dec_ref(x_107);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_2);
x_115 = !lean_is_exclusive(x_83);
if (x_115 == 0)
{
return x_83;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_83, 0);
x_117 = lean_ctor_get(x_83, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_83);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_46);
x_119 = l_Lean_Elab_Command_liftTermElabM___rarg___closed__1;
x_120 = l_unreachable_x21___rarg(x_119);
lean_inc(x_2);
x_121 = lean_apply_2(x_120, x_2, x_43);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_8 = x_122;
x_9 = x_123;
goto block_33;
}
else
{
uint8_t x_124; 
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_121);
if (x_124 == 0)
{
return x_121;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_121, 0);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_121);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_41);
if (x_128 == 0)
{
return x_41;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_41, 0);
x_130 = lean_ctor_get(x_41, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_41);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_37);
if (x_132 == 0)
{
return x_37;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_37, 0);
x_134 = lean_ctor_get(x_37, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_37);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
block_33:
{
lean_object* x_10; 
lean_inc(x_2);
x_10 = l_Lean_Elab_Command_addDecl(x_7, x_8, x_2, x_9);
lean_dec(x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_2);
x_12 = l___private_Lean_Elab_Inductive_34__mkAuxConstructions(x_1, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Array_forMAux___main___at_Lean_Elab_Command_elabInductiveViews___spec__1(x_7, x_1, x_5, x_2, x_13);
lean_dec(x_1);
lean_dec(x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
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
else
{
uint8_t x_25; 
lean_dec(x_7);
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
lean_dec(x_7);
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
}
lean_object* l_Array_forMAux___main___at_Lean_Elab_Command_elabInductiveViews___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_Elab_Command_elabInductiveViews___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_ReplaceLevel(lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Util_Constructions(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_CollectFVars(lean_object*);
lean_object* initialize_Lean_Elab_Definition(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Inductive(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceLevel(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_ReplaceExpr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Constructions(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Definition(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__3 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__3);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__4 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__4);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__5 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__5);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__6 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__6);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__7 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__7);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__8 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__8);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__9 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__9);
l_Lean_Elab_Command_checkValidCtorModifier___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___closed__3 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__3);
l_Lean_Elab_Command_checkValidCtorModifier___closed__4 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__4);
l_Lean_Elab_Command_checkValidCtorModifier___closed__5 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__5);
l_Lean_Elab_Command_checkValidCtorModifier___closed__6 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__6);
l_Lean_Elab_Command_checkValidCtorModifier___closed__7 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__7();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__7);
l_Lean_Elab_Command_checkValidCtorModifier___closed__8 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__8();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__8);
l_Lean_Elab_Command_checkValidCtorModifier___closed__9 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__9();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__9);
l_Lean_Elab_Command_checkValidCtorModifier___closed__10 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__10();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__10);
l_Lean_Elab_Command_checkValidCtorModifier___closed__11 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__11();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__11);
l_Lean_Elab_Command_checkValidCtorModifier___closed__12 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__12();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__12);
l_Lean_Elab_Command_CtorView_inhabited___closed__1 = _init_l_Lean_Elab_Command_CtorView_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_CtorView_inhabited___closed__1);
l_Lean_Elab_Command_CtorView_inhabited___closed__2 = _init_l_Lean_Elab_Command_CtorView_inhabited___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_CtorView_inhabited___closed__2);
l_Lean_Elab_Command_CtorView_inhabited = _init_l_Lean_Elab_Command_CtorView_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_CtorView_inhabited);
l_Lean_Elab_Command_InductiveView_inhabited___closed__1 = _init_l_Lean_Elab_Command_InductiveView_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_InductiveView_inhabited___closed__1);
l_Lean_Elab_Command_InductiveView_inhabited = _init_l_Lean_Elab_Command_InductiveView_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_InductiveView_inhabited);
l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1 = _init_l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_ElabHeaderResult_inhabited___closed__1);
l_Lean_Elab_Command_ElabHeaderResult_inhabited = _init_l_Lean_Elab_Command_ElabHeaderResult_inhabited();
lean_mark_persistent(l_Lean_Elab_Command_ElabHeaderResult_inhabited);
l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1 = _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__1);
l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2 = _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__2);
l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3 = _init_l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_1__elabHeaderAux___main___lambda__1___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_2__checkNumParams___spec__1___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_3__checkUnsafe___spec__1___closed__3);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__1);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__2);
l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3 = _init_l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3();
lean_mark_persistent(l_Array_forMAux___main___at___private_Lean_Elab_Inductive_4__checkLevelNames___spec__1___closed__3);
l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1 = _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__1);
l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2 = _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__2);
l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3 = _init_l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_6__throwUnexpectedInductiveType___rarg___closed__3);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__1 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__1);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__2 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__2);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__3 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__3);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__4 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__4);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__5 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__5);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__6 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__6);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__7 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__7();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__7);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__8 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__8();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__8);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__9 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__9();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__9);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__10 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__10();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__10);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__11 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__11();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__11);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__12 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__12();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__12);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__13 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__13();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__13);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__14 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__14();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__14);
l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__15 = _init_l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__15();
lean_mark_persistent(l___private_Lean_Elab_Inductive_9__checkParamsAndResultType___main___closed__15);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__1);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__2);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__3);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__4);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__5);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__6);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__7);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__8);
l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9 = _init_l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9();
lean_mark_persistent(l_List_mapM___main___at___private_Lean_Elab_Inductive_16__elabCtors___spec__1___lambda__1___closed__9);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__1);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__2);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__3);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__4);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__5);
l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6 = _init_l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Inductive_19__getResultingUniverse___closed__6);
l_Lean_Elab_Command_tmpIndParam___closed__1 = _init_l_Lean_Elab_Command_tmpIndParam___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam___closed__1);
l_Lean_Elab_Command_tmpIndParam___closed__2 = _init_l_Lean_Elab_Command_tmpIndParam___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam___closed__2);
l_Lean_Elab_Command_tmpIndParam___closed__3 = _init_l_Lean_Elab_Command_tmpIndParam___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam___closed__3);
l_Lean_Elab_Command_tmpIndParam = _init_l_Lean_Elab_Command_tmpIndParam();
lean_mark_persistent(l_Lean_Elab_Command_tmpIndParam);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__1 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__1);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__2 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__2);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__3 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__3);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__4 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__4();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__4);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__5 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__5();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__5);
l_Lean_Elab_Command_shouldInferResultUniverse___closed__6 = _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__6();
lean_mark_persistent(l_Lean_Elab_Command_shouldInferResultUniverse___closed__6);
l_Lean_Elab_Command_accLevelAtCtor___main___closed__1 = _init_l_Lean_Elab_Command_accLevelAtCtor___main___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_accLevelAtCtor___main___closed__1);
l_Lean_Elab_Command_accLevelAtCtor___main___closed__2 = _init_l_Lean_Elab_Command_accLevelAtCtor___main___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_accLevelAtCtor___main___closed__2);
l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___closed__1 = _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___at___private_Lean_Elab_Inductive_23__updateResultingUniverse___spec__1___closed__1);
l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__1);
l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_23__updateResultingUniverse___closed__2);
l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1___closed__1 = _init_l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1___closed__1();
lean_mark_persistent(l_List_forM___main___at___private_Lean_Elab_Inductive_24__traceIndTypes___spec__1___closed__1);
l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___closed__1 = _init_l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___closed__1();
lean_mark_persistent(l_List_map___main___at___private_Lean_Elab_Inductive_32__applyInferMod___spec__1___closed__1);
l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1 = _init_l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__1);
l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2 = _init_l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_34__mkAuxConstructions___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
