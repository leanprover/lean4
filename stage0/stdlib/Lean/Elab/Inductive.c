// Lean compiler output
// Module: Lean.Elab.Inductive
// Imports: Init Lean.Util.ReplaceLevel Lean.Util.ReplaceExpr Lean.Util.CollectLevelParams Lean.Util.Constructions Lean.Elab.Command Lean.Elab.CollectFVars Lean.Elab.DefView Lean.Elab.DeclUtil
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
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLevelNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeFormerTypeImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__1;
extern lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__4;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1;
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_brec_on(lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2;
size_t l_USize_add(size_t, size_t);
uint8_t l_Lean_Level_isNeverZero(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___boxed(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Elab_Command_checkResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__3(lean_object*);
lean_object* l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__4;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
extern lean_object* l_Lean_initFn____x40_Lean_Class___hyg_784____closed__2;
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__1;
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkResultUniverse(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__6;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux_match__1(lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__3;
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__2;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1(lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNoConfusion___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkResultingUniverses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__1(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEqAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_ensureNoUnassignedMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1;
lean_object* l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor___closed__1;
lean_object* l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Elab_Term_applyAttributesAt(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffsetAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1;
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__2;
lean_object* l_Lean_Elab_Term_withLevelNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Lean_Elab_Attributes___instance__2;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2;
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkResultingUniverse___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__5;
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_Std_Data_HashMap___instance__1___closed__1;
lean_object* l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__1;
lean_object* l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVarsImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2;
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1;
lean_object* l_Lean_Elab_Command_checkResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6(uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkResultingUniverse___closed__2;
lean_object* lean_mk_ibelow(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__3(uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_mkResultUniverse___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_CollectFVars_Lean_Util_CollectFVars___instance__1___closed__1;
extern lean_object* l_Lean_Meta_isExprDefEq___rarg___closed__2;
extern lean_object* l_Lean_Meta_isLevelDefEqAux___closed__6;
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Level_isParam(lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4;
lean_object* l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern uint8_t l_Init_Core___instance__31;
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls(lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__2;
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__3;
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__2(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_KVMap_getBool(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__3;
extern lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_Lean_LocalContext___instance__2___closed__1;
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__2;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___lambda__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused_match__1(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__2;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__1;
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed(lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_assignLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getCheckResultingUniverseOption___boxed(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__5;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2;
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__3;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__4;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop_match__1(lean_object*);
lean_object* l_Lean_Elab_Command_accLevelAtCtor_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Init_LeanInit___instance__19___rarg___closed__2;
lean_object* l_Lean_Meta_getLocalInstances___at_Lean_Elab_Term_removeUnused___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_no_confusion(lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__2(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__2(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__3;
lean_object* l_Lean_Elab_sortDeclLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2;
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__3;
lean_object* l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__2;
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__1(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__2;
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__3;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__2;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2;
lean_object* l_Lean_Elab_Command_accLevelAtCtor___closed__2;
lean_object* l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__4;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3;
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__1;
lean_object* l_Lean_Elab_Term_levelMVarToParam_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__3;
lean_object* l_Lean_Elab_Term_resetMessageLog(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__1;
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1;
lean_object* l_List_foldl___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__1;
lean_object* l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* lean_mk_below(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Elab_Term_declareTacticSyntax___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__6;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__2___boxed(lean_object**);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__1;
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2;
lean_object* l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_initFn____x40_Lean_Data_Options___hyg_479____closed__3;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Meta_addGlobalInstanceImp___spec__1(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___boxed(lean_object**);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts_match__1(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__3;
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494_(lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4_(lean_object*);
lean_object* l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam___closed__3;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mkNaryMax(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2;
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
extern lean_object* l_Std_HashMap_find_x21___rarg___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__3;
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_find_x21___rarg___closed__2;
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__4;
lean_object* l_ReaderT_bind___at_Lean_Elab_Term_Lean_Elab_Term___instance__8___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__2;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__3;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__2;
extern lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__2(lean_object*, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__2;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeCompatibleAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux_match__1(lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_Command_getCheckResultingUniverseOption(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNoConfusion___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__6;
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_Elab_Term_elabBinders___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___closed__3;
lean_object* l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Lean_Expr___instance__11___closed__1;
lean_object* l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl_match__1(lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__4;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__3;
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__3;
lean_object* l_Lean_Elab_Command_accLevelAtCtor_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_CollectLevelParams_Lean_Util_CollectLevelParams___instance__1___closed__1;
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
lean_object* lean_mk_rec_on(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Nat_foldM_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2(lean_object*, lean_object*, size_t, size_t);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__2___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse_match__1(lean_object*);
uint8_t l_List_beq___at_Lean_OpenDecl_Lean_Data_OpenDecl___instance__2___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_Lean_Elab_Term___instance__8___closed__5;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___closed__1;
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_tmpIndParam;
lean_object* l_Lean_Elab_Command_elabInductiveViews___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_ClassState_addEntry___spec__6(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_binduction_on(lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__5;
lean_object* l_Nat_foldAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__2;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__5;
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__3;
lean_object* l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop_match__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeImp___at_Lean_Meta_isType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__2(lean_object*);
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__1;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_ReplaceImpl_initCache;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__3;
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_834____closed__1;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in inductive declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_eq(x_7, x_10);
lean_dec(x_7);
if (x_11 == 0)
{
if (x_9 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__3;
x_13 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_12, x_3, x_4, x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
else
{
if (x_9 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = l_Lean_Elab_Lean_Elab_Attributes___instance__2;
x_17 = lean_array_get(x_16, x_6, x_8);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_initFn____x40_Lean_Class___hyg_784____closed__2;
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__3;
x_22 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_21, x_3, x_4, x_5);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_5);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_3);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_5);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in inductive declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__3;
x_10 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_9, x_3, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in inductive declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2(x_1, x_6, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Elab_Command_checkValidInductiveModifier___closed__3;
x_9 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_8, x_2, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_checkValidInductiveModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidInductiveModifier(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of attributes in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__3;
x_11 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_10, x_3, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'unsafe' in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__1(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__3;
x_10 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_9, x_3, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'partial' in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__2(x_1, x_7, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__3;
x_10 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_9, x_3, x_4, x_5);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid use of 'noncomputable' in constructor declaration");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkValidCtorModifier___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__3(x_1, x_6, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Elab_Command_checkValidCtorModifier___closed__3;
x_9 = l_Lean_throwError___at_Lean_Elab_Command_elabCommand___spec__7___rarg(x_8, x_2, x_3, x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Command_checkValidCtorModifier___lambda__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Elab_Command_checkValidCtorModifier___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_checkValidCtorModifier(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__1() {
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
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__1;
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
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__1;
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
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2___closed__1;
x_2 = l_Lean_LocalContext_Lean_LocalContext___instance__2___closed__1;
x_3 = l_Array_empty___closed__1;
x_4 = l_Lean_Expr_Lean_Expr___instance__11___closed__1;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3___closed__1;
return x_1;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeFormerTypeImp(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_1, x_17);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_5);
lean_ctor_set(x_19, 4, x_6);
x_20 = lean_array_push(x_7, x_19);
x_21 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux(x_8, x_18, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
return x_21;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, resultant type is not a sort");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
x_14 = l_Lean_Meta_getLocalInstances___at_Lean_Elab_Term_removeUnused___spec__1___rarg(x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_1, 6);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_Meta_mkFreshLevelMVar___at_Lean_Elab_Term_ensureType___spec__2___rarg(x_9, x_10, x_11, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_mkSort(x_19);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_2, x_22);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_5);
lean_ctor_set(x_24, 4, x_21);
x_25 = lean_array_push(x_3, x_24);
x_26 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux(x_4, x_23, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_ctor_get(x_15, 0);
lean_inc(x_29);
lean_dec(x_15);
x_30 = lean_box(0);
x_31 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
x_32 = l_Lean_Elab_Term_elabTerm(x_29, x_30, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_33);
x_35 = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeFormerTypeImp(x_33, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_33);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__3;
x_40 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_29, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_38);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_29);
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
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_29);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_box(0);
x_47 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1(x_2, x_1, x_13, x_27, x_5, x_33, x_3, x_4, x_46, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_32, 0);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_32);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_2, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_fget(x_1, x_2);
x_15 = lean_ctor_get(x_14, 5);
lean_inc(x_15);
x_16 = l_Lean_Syntax_getArgs(x_15);
lean_dec(x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___boxed), 12, 4);
lean_closure_set(x_17, 0, x_14);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_3);
lean_closure_set(x_17, 3, x_1);
x_18 = l_Lean_Elab_Term_elabBinders___rarg(x_16, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
}
lean_object* l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isTypeFormerType___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_1);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, number of parameters mismatch in mutually inductive datatypes");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_4 < x_3;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 3);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
lean_dec(x_16);
x_18 = lean_nat_dec_eq(x_17, x_1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__3;
x_22 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_20, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
lean_dec(x_15);
x_27 = 1;
x_28 = x_4 + x_27;
x_29 = lean_box(0);
x_4 = x_28;
x_5 = x_29;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_1, x_10);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_12);
lean_dec(x_12);
x_14 = lean_array_get_size(x_1);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = lean_box(0);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1(x_13, x_1, x_15, x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_13);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, cannot mix unsafe and safe declarations in a mutually inductive datatypes");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_10, 1);
x_21 = lean_ctor_get_uint8(x_20, sizeof(void*)*2 + 3);
if (x_21 == 0)
{
if (x_2 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_3);
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_box(0);
x_11 = x_24;
goto block_19;
}
}
else
{
if (x_2 == 0)
{
lean_object* x_25; 
x_25 = lean_box(0);
x_11 = x_25;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec(x_3);
x_26 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_11);
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__3;
x_14 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__2(lean_object* x_1, size_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_9(x_20, lean_box(0), x_18, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = 1;
x_24 = x_2 + x_23;
x_25 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1(x_3, x_4, x_5, x_6, x_7, x_1, x_8, x_9, x_24, x_22, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_25;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = x_9 < x_8;
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_9(x_20, lean_box(0), x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
x_22 = lean_array_uget(x_7, x_9);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
x_24 = lean_box(x_1);
x_25 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___boxed), 9, 2);
lean_closure_set(x_25, 0, x_22);
lean_closure_set(x_25, 1, x_24);
x_26 = lean_box_usize(x_9);
x_27 = lean_box(x_1);
x_28 = lean_box_usize(x_8);
x_29 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__2___boxed), 17, 9);
lean_closure_set(x_29, 0, x_6);
lean_closure_set(x_29, 1, x_26);
lean_closure_set(x_29, 2, x_27);
lean_closure_set(x_29, 3, x_2);
lean_closure_set(x_29, 4, x_3);
lean_closure_set(x_29, 5, x_4);
lean_closure_set(x_29, 6, x_5);
lean_closure_set(x_29, 7, x_7);
lean_closure_set(x_29, 8, x_28);
x_30 = lean_apply_11(x_23, lean_box(0), lean_box(0), x_25, x_29, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_30;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*2 + 3);
lean_dec(x_13);
x_15 = lean_array_get_size(x_1);
x_16 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_17 = 0;
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__1;
x_19 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__2;
x_20 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewLocalInstancesImp___rarg___closed__3;
x_21 = l_Lean_Meta_CheckAssignment_checkFVar___closed__1;
x_22 = l_Lean_Meta_CheckAssignment_checkFVar___closed__2;
x_23 = lean_box(0);
x_24 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1(x_14, x_18, x_19, x_20, x_21, x_22, x_1, x_16, x_17, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
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
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__2___boxed(lean_object** _args) {
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
_start:
{
size_t x_18; uint8_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_19 = lean_unbox(x_3);
lean_dec(x_3);
x_20 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__2(x_1, x_18, x_19, x_4, x_5, x_6, x_7, x_8, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_1);
lean_dec(x_1);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_19, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_21;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid inductive type, universe parameters mismatch in mutually inductive datatypes");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = x_4 < x_3;
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_5);
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
x_17 = l_List_beq___at_Lean_OpenDecl_Lean_Data_OpenDecl___instance__2___spec__1(x_16, x_1);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__3;
x_20 = l_Lean_throwErrorAt___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabTermAux___spec__1___rarg(x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_18);
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
size_t x_25; size_t x_26; lean_object* x_27; 
lean_dec(x_15);
x_25 = 1;
x_26 = x_4 + x_25;
x_27 = lean_box(0);
x_4 = x_26;
x_5 = x_27;
goto _start;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_1, x_15);
x_17 = lean_ctor_get(x_16, 4);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_19 = 0;
x_20 = lean_box(0);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1(x_17, x_1, x_18, x_19, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
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
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 4);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2___boxed), 9, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_9, x_10, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected inductive resulting type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__3;
x_9 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___spec__1___rarg), 9, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___lambda__1___boxed), 9, 0);
return x_1;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___closed__1;
x_10 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___spec__1___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Meta_isExprDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_42, 0, x_58);
return x_42;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_dec(x_42);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_dec(x_42);
x_20 = x_63;
x_21 = x_64;
goto block_27;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_dec(x_28);
x_20 = x_65;
x_21 = x_66;
goto block_27;
}
block_27:
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_28; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_getResetPostponed(x_4, x_5, x_6, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_28 = l_Lean_Meta_isExprDefEqAux(x_1, x_2, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_dec(x_32);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_28, 1);
lean_inc(x_41);
lean_dec(x_28);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_42 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed(x_3, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = 0;
x_50 = lean_box(x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_42, 0);
lean_dec(x_56);
x_57 = 1;
x_58 = lean_box(x_57);
lean_ctor_set(x_42, 0, x_58);
return x_42;
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_42, 1);
lean_inc(x_59);
lean_dec(x_42);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_42, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_42, 1);
lean_inc(x_64);
lean_dec(x_42);
x_20 = x_63;
x_21 = x_64;
goto block_27;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_28, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_dec(x_28);
x_20 = x_65;
x_21 = x_66;
goto block_27;
}
block_27:
{
lean_object* x_22; uint8_t x_23; 
x_22 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_restore(x_12, x_16, x_18, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_17; lean_object* x_18; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_422 = lean_st_ref_get(x_6, x_7);
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_423, 3);
lean_inc(x_424);
lean_dec(x_423);
x_425 = lean_ctor_get_uint8(x_424, sizeof(void*)*1);
lean_dec(x_424);
if (x_425 == 0)
{
lean_object* x_426; uint8_t x_427; 
x_426 = lean_ctor_get(x_422, 1);
lean_inc(x_426);
lean_dec(x_422);
x_427 = 0;
x_17 = x_427;
x_18 = x_426;
goto block_421;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; 
x_428 = lean_ctor_get(x_422, 1);
lean_inc(x_428);
lean_dec(x_422);
x_429 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_430 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_429, x_3, x_4, x_5, x_6, x_428);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = lean_unbox(x_431);
lean_dec(x_431);
x_17 = x_433;
x_18 = x_432;
goto block_421;
}
block_16:
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
block_421:
{
if (x_17 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_19 = lean_st_ref_get(x_6, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_6, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 3);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_83; lean_object* x_84; 
x_31 = 0;
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_31);
x_32 = lean_st_ref_set(x_6, x_25, x_27);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_83 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_84 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__2(x_1, x_2, x_83, x_3, x_4, x_5, x_6, x_33);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_115 = lean_st_ref_get(x_6, x_86);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 3);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_ctor_get_uint8(x_117, sizeof(void*)*1);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_115, 1);
lean_inc(x_119);
lean_dec(x_115);
x_87 = x_31;
x_88 = x_119;
goto block_114;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_dec(x_115);
x_121 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_122 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_121, x_3, x_4, x_5, x_6, x_120);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_unbox(x_123);
lean_dec(x_123);
x_87 = x_125;
x_88 = x_124;
goto block_114;
}
block_114:
{
if (x_87 == 0)
{
uint8_t x_89; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_unbox(x_85);
lean_dec(x_85);
x_34 = x_89;
x_35 = x_88;
goto block_82;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_90 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_90, 0, x_1);
x_91 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_92 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_94 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_95, 0, x_2);
x_96 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_unbox(x_85);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_100 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_91);
x_103 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_104 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_103, x_102, x_3, x_4, x_5, x_6, x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_unbox(x_85);
lean_dec(x_85);
x_34 = x_106;
x_35 = x_105;
goto block_82;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_107 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
x_108 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_108, 0, x_98);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_91);
x_110 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_111 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_110, x_109, x_3, x_4, x_5, x_6, x_88);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_unbox(x_85);
lean_dec(x_85);
x_34 = x_113;
x_35 = x_112;
goto block_82;
}
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_ctor_get(x_84, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_84, 1);
lean_inc(x_127);
lean_dec(x_84);
x_128 = lean_st_ref_get(x_6, x_127);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_6, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 3);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = !lean_is_exclusive(x_131);
if (x_134 == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_131, 3);
lean_dec(x_135);
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_23);
x_137 = lean_st_ref_set(x_6, x_131, x_133);
lean_dec(x_6);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_137, 0);
lean_dec(x_139);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 0, x_126);
return x_137;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_126);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_132, 0);
lean_inc(x_142);
lean_dec(x_132);
x_143 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set_uint8(x_143, sizeof(void*)*1, x_23);
lean_ctor_set(x_131, 3, x_143);
x_144 = lean_st_ref_set(x_6, x_131, x_133);
lean_dec(x_6);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
 lean_ctor_set_tag(x_147, 1);
}
lean_ctor_set(x_147, 0, x_126);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_148 = lean_ctor_get(x_131, 0);
x_149 = lean_ctor_get(x_131, 1);
x_150 = lean_ctor_get(x_131, 2);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_131);
x_151 = lean_ctor_get(x_132, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_152 = x_132;
} else {
 lean_dec_ref(x_132);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(0, 1, 1);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_23);
x_154 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_149);
lean_ctor_set(x_154, 2, x_150);
lean_ctor_set(x_154, 3, x_153);
x_155 = lean_st_ref_set(x_6, x_154, x_133);
lean_dec(x_6);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_126);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
block_82:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_36 = lean_st_ref_get(x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_37, 3);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*1);
lean_dec(x_39);
x_41 = lean_st_ref_take(x_6, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_42, 3);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_23);
x_48 = lean_st_ref_set(x_6, x_42, x_44);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(x_34);
x_52 = lean_box(x_40);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_48, 0, x_53);
x_8 = x_48;
goto block_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_box(x_34);
x_56 = lean_box(x_40);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
x_8 = x_58;
goto block_16;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_59 = lean_ctor_get(x_43, 0);
lean_inc(x_59);
lean_dec(x_43);
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_23);
lean_ctor_set(x_42, 3, x_60);
x_61 = lean_st_ref_set(x_6, x_42, x_44);
lean_dec(x_6);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_63 = x_61;
} else {
 lean_dec_ref(x_61);
 x_63 = lean_box(0);
}
x_64 = lean_box(x_34);
x_65 = lean_box(x_40);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
if (lean_is_scalar(x_63)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_63;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
x_8 = x_67;
goto block_16;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_68 = lean_ctor_get(x_42, 0);
x_69 = lean_ctor_get(x_42, 1);
x_70 = lean_ctor_get(x_42, 2);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_42);
x_71 = lean_ctor_get(x_43, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_72 = x_43;
} else {
 lean_dec_ref(x_43);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 1, 1);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_23);
x_74 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_70);
lean_ctor_set(x_74, 3, x_73);
x_75 = lean_st_ref_set(x_6, x_74, x_44);
lean_dec(x_6);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_box(x_34);
x_79 = lean_box(x_40);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_76);
x_8 = x_81;
goto block_16;
}
}
}
else
{
lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; uint8_t x_191; lean_object* x_192; 
x_159 = lean_ctor_get(x_26, 0);
lean_inc(x_159);
lean_dec(x_26);
x_160 = 0;
x_161 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set_uint8(x_161, sizeof(void*)*1, x_160);
lean_ctor_set(x_25, 3, x_161);
x_162 = lean_st_ref_set(x_6, x_25, x_27);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_191 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_192 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__2(x_1, x_2, x_191, x_3, x_4, x_5, x_6, x_163);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_223 = lean_st_ref_get(x_6, x_194);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_224, 3);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_ctor_get_uint8(x_225, sizeof(void*)*1);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; 
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_dec(x_223);
x_195 = x_160;
x_196 = x_227;
goto block_222;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_228 = lean_ctor_get(x_223, 1);
lean_inc(x_228);
lean_dec(x_223);
x_229 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_230 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_229, x_3, x_4, x_5, x_6, x_228);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_unbox(x_231);
lean_dec(x_231);
x_195 = x_233;
x_196 = x_232;
goto block_222;
}
block_222:
{
if (x_195 == 0)
{
uint8_t x_197; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_unbox(x_193);
lean_dec(x_193);
x_164 = x_197;
x_165 = x_196;
goto block_190;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_198 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_198, 0, x_1);
x_199 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_200 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
x_201 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_202 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_203, 0, x_2);
x_204 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
x_206 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_unbox(x_193);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_208 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
x_209 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_199);
x_211 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_212 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_211, x_210, x_3, x_4, x_5, x_6, x_196);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_unbox(x_193);
lean_dec(x_193);
x_164 = x_214;
x_165 = x_213;
goto block_190;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_215 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
x_216 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_216, 0, x_206);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_199);
x_218 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_219 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_218, x_217, x_3, x_4, x_5, x_6, x_196);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = lean_unbox(x_193);
lean_dec(x_193);
x_164 = x_221;
x_165 = x_220;
goto block_190;
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_234 = lean_ctor_get(x_192, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_192, 1);
lean_inc(x_235);
lean_dec(x_192);
x_236 = lean_st_ref_get(x_6, x_235);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_st_ref_take(x_6, x_237);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_239, 3);
lean_inc(x_240);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
lean_dec(x_238);
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_239, 2);
lean_inc(x_244);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 lean_ctor_release(x_239, 2);
 lean_ctor_release(x_239, 3);
 x_245 = x_239;
} else {
 lean_dec_ref(x_239);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_240, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 x_247 = x_240;
} else {
 lean_dec_ref(x_240);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(0, 1, 1);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set_uint8(x_248, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_245)) {
 x_249 = lean_alloc_ctor(0, 4, 0);
} else {
 x_249 = x_245;
}
lean_ctor_set(x_249, 0, x_242);
lean_ctor_set(x_249, 1, x_243);
lean_ctor_set(x_249, 2, x_244);
lean_ctor_set(x_249, 3, x_248);
x_250 = lean_st_ref_set(x_6, x_249, x_241);
lean_dec(x_6);
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
 lean_ctor_set_tag(x_253, 1);
}
lean_ctor_set(x_253, 0, x_234);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
block_190:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_166 = lean_st_ref_get(x_6, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_ctor_get(x_167, 3);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get_uint8(x_169, sizeof(void*)*1);
lean_dec(x_169);
x_171 = lean_st_ref_take(x_6, x_168);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_172, 3);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 1);
lean_inc(x_174);
lean_dec(x_171);
x_175 = lean_ctor_get(x_172, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 2);
lean_inc(x_177);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 lean_ctor_release(x_172, 2);
 lean_ctor_release(x_172, 3);
 x_178 = x_172;
} else {
 lean_dec_ref(x_172);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_173, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_180 = x_173;
} else {
 lean_dec_ref(x_173);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(0, 1, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_178)) {
 x_182 = lean_alloc_ctor(0, 4, 0);
} else {
 x_182 = x_178;
}
lean_ctor_set(x_182, 0, x_175);
lean_ctor_set(x_182, 1, x_176);
lean_ctor_set(x_182, 2, x_177);
lean_ctor_set(x_182, 3, x_181);
x_183 = lean_st_ref_set(x_6, x_182, x_174);
lean_dec(x_6);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_185 = x_183;
} else {
 lean_dec_ref(x_183);
 x_185 = lean_box(0);
}
x_186 = lean_box(x_164);
x_187 = lean_box(x_170);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
if (lean_is_scalar(x_185)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_185;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_184);
x_8 = x_189;
goto block_16;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; uint8_t x_291; lean_object* x_292; 
x_254 = lean_ctor_get(x_25, 0);
x_255 = lean_ctor_get(x_25, 1);
x_256 = lean_ctor_get(x_25, 2);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_25);
x_257 = lean_ctor_get(x_26, 0);
lean_inc(x_257);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_258 = x_26;
} else {
 lean_dec_ref(x_26);
 x_258 = lean_box(0);
}
x_259 = 0;
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(0, 1, 1);
} else {
 x_260 = x_258;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set_uint8(x_260, sizeof(void*)*1, x_259);
x_261 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_261, 0, x_254);
lean_ctor_set(x_261, 1, x_255);
lean_ctor_set(x_261, 2, x_256);
lean_ctor_set(x_261, 3, x_260);
x_262 = lean_st_ref_set(x_6, x_261, x_27);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_291 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_292 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__2(x_1, x_2, x_291, x_3, x_4, x_5, x_6, x_263);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; lean_object* x_296; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_323 = lean_st_ref_get(x_6, x_294);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_324, 3);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_ctor_get_uint8(x_325, sizeof(void*)*1);
lean_dec(x_325);
if (x_326 == 0)
{
lean_object* x_327; 
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_295 = x_259;
x_296 = x_327;
goto block_322;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; 
x_328 = lean_ctor_get(x_323, 1);
lean_inc(x_328);
lean_dec(x_323);
x_329 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_330 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_329, x_3, x_4, x_5, x_6, x_328);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
lean_dec(x_330);
x_333 = lean_unbox(x_331);
lean_dec(x_331);
x_295 = x_333;
x_296 = x_332;
goto block_322;
}
block_322:
{
if (x_295 == 0)
{
uint8_t x_297; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_297 = lean_unbox(x_293);
lean_dec(x_293);
x_264 = x_297;
x_265 = x_296;
goto block_290;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_298 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_298, 0, x_1);
x_299 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_300 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_300, 0, x_299);
lean_ctor_set(x_300, 1, x_298);
x_301 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_302 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_303, 0, x_2);
x_304 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
x_306 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_unbox(x_293);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_308 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
x_309 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_299);
x_311 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_312 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_311, x_310, x_3, x_4, x_5, x_6, x_296);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_314 = lean_unbox(x_293);
lean_dec(x_293);
x_264 = x_314;
x_265 = x_313;
goto block_290;
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; 
x_315 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
x_316 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_316, 0, x_306);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_299);
x_318 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_319 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_318, x_317, x_3, x_4, x_5, x_6, x_296);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_320 = lean_ctor_get(x_319, 1);
lean_inc(x_320);
lean_dec(x_319);
x_321 = lean_unbox(x_293);
lean_dec(x_293);
x_264 = x_321;
x_265 = x_320;
goto block_290;
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_334 = lean_ctor_get(x_292, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_292, 1);
lean_inc(x_335);
lean_dec(x_292);
x_336 = lean_st_ref_get(x_6, x_335);
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
lean_dec(x_336);
x_338 = lean_st_ref_take(x_6, x_337);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_339, 3);
lean_inc(x_340);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_dec(x_338);
x_342 = lean_ctor_get(x_339, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_339, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_339, 2);
lean_inc(x_344);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 lean_ctor_release(x_339, 3);
 x_345 = x_339;
} else {
 lean_dec_ref(x_339);
 x_345 = lean_box(0);
}
x_346 = lean_ctor_get(x_340, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 x_347 = x_340;
} else {
 lean_dec_ref(x_340);
 x_347 = lean_box(0);
}
if (lean_is_scalar(x_347)) {
 x_348 = lean_alloc_ctor(0, 1, 1);
} else {
 x_348 = x_347;
}
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set_uint8(x_348, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_345)) {
 x_349 = lean_alloc_ctor(0, 4, 0);
} else {
 x_349 = x_345;
}
lean_ctor_set(x_349, 0, x_342);
lean_ctor_set(x_349, 1, x_343);
lean_ctor_set(x_349, 2, x_344);
lean_ctor_set(x_349, 3, x_348);
x_350 = lean_st_ref_set(x_6, x_349, x_341);
lean_dec(x_6);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 2, 0);
} else {
 x_353 = x_352;
 lean_ctor_set_tag(x_353, 1);
}
lean_ctor_set(x_353, 0, x_334);
lean_ctor_set(x_353, 1, x_351);
return x_353;
}
block_290:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_266 = lean_st_ref_get(x_6, x_265);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = lean_ctor_get(x_267, 3);
lean_inc(x_269);
lean_dec(x_267);
x_270 = lean_ctor_get_uint8(x_269, sizeof(void*)*1);
lean_dec(x_269);
x_271 = lean_st_ref_take(x_6, x_268);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_272, 3);
lean_inc(x_273);
x_274 = lean_ctor_get(x_271, 1);
lean_inc(x_274);
lean_dec(x_271);
x_275 = lean_ctor_get(x_272, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_272, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_272, 2);
lean_inc(x_277);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_278 = x_272;
} else {
 lean_dec_ref(x_272);
 x_278 = lean_box(0);
}
x_279 = lean_ctor_get(x_273, 0);
lean_inc(x_279);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_280 = x_273;
} else {
 lean_dec_ref(x_273);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(0, 1, 1);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set_uint8(x_281, sizeof(void*)*1, x_23);
if (lean_is_scalar(x_278)) {
 x_282 = lean_alloc_ctor(0, 4, 0);
} else {
 x_282 = x_278;
}
lean_ctor_set(x_282, 0, x_275);
lean_ctor_set(x_282, 1, x_276);
lean_ctor_set(x_282, 2, x_277);
lean_ctor_set(x_282, 3, x_281);
x_283 = lean_st_ref_set(x_6, x_282, x_274);
lean_dec(x_6);
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_283)) {
 lean_ctor_release(x_283, 0);
 lean_ctor_release(x_283, 1);
 x_285 = x_283;
} else {
 lean_dec_ref(x_283);
 x_285 = lean_box(0);
}
x_286 = lean_box(x_264);
x_287 = lean_box(x_270);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
if (lean_is_scalar(x_285)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_285;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_284);
x_8 = x_289;
goto block_16;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; uint8_t x_369; lean_object* x_370; 
x_354 = lean_ctor_get(x_5, 3);
lean_inc(x_354);
x_355 = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__1___rarg(x_6, x_18);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_369 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_370 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__3(x_1, x_2, x_369, x_3, x_4, x_5, x_6, x_357);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_401 = lean_st_ref_get(x_6, x_372);
x_402 = lean_ctor_get(x_401, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_402, 3);
lean_inc(x_403);
lean_dec(x_402);
x_404 = lean_ctor_get_uint8(x_403, sizeof(void*)*1);
lean_dec(x_403);
if (x_404 == 0)
{
lean_object* x_405; uint8_t x_406; 
x_405 = lean_ctor_get(x_401, 1);
lean_inc(x_405);
lean_dec(x_401);
x_406 = 0;
x_373 = x_406;
x_374 = x_405;
goto block_400;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; 
x_407 = lean_ctor_get(x_401, 1);
lean_inc(x_407);
lean_dec(x_401);
x_408 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_409 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_408, x_3, x_4, x_5, x_6, x_407);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
x_412 = lean_unbox(x_410);
lean_dec(x_410);
x_373 = x_412;
x_374 = x_411;
goto block_400;
}
block_400:
{
if (x_373 == 0)
{
uint8_t x_375; 
lean_dec(x_2);
lean_dec(x_1);
x_375 = lean_unbox(x_371);
lean_dec(x_371);
x_358 = x_375;
x_359 = x_374;
goto block_368;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
x_376 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_376, 0, x_1);
x_377 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_378 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
x_379 = l_Lean_Meta_isLevelDefEqAux___closed__6;
x_380 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_381, 0, x_2);
x_382 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
x_383 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__2;
x_384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_unbox(x_371);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_386 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__4;
x_387 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_377);
x_389 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_390 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_389, x_388, x_3, x_4, x_5, x_6, x_374);
x_391 = lean_ctor_get(x_390, 1);
lean_inc(x_391);
lean_dec(x_390);
x_392 = lean_unbox(x_371);
lean_dec(x_371);
x_358 = x_392;
x_359 = x_391;
goto block_368;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_393 = l_Lean_Meta_isLevelDefEq___rarg___lambda__2___closed__6;
x_394 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_394, 0, x_384);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_377);
x_396 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_397 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_396, x_395, x_3, x_4, x_5, x_6, x_374);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_399 = lean_unbox(x_371);
lean_dec(x_371);
x_358 = x_399;
x_359 = x_398;
goto block_368;
}
}
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
lean_dec(x_2);
lean_dec(x_1);
x_413 = lean_ctor_get(x_370, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_370, 1);
lean_inc(x_414);
lean_dec(x_370);
x_415 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_416 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__2(x_356, x_415, x_354, x_3, x_4, x_5, x_6, x_414);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_417 = !lean_is_exclusive(x_416);
if (x_417 == 0)
{
lean_object* x_418; 
x_418 = lean_ctor_get(x_416, 0);
lean_dec(x_418);
lean_ctor_set_tag(x_416, 1);
lean_ctor_set(x_416, 0, x_413);
return x_416;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_416, 1);
lean_inc(x_419);
lean_dec(x_416);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_413);
lean_ctor_set(x_420, 1, x_419);
return x_420;
}
}
block_368:
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_360 = l_Lean_Meta_isExprDefEq___rarg___closed__2;
x_361 = l___private_Lean_Util_Trace_0__Lean_addNode___at___private_Lean_Meta_LevelDefEq_0__Lean_Meta_processPostponed___spec__2(x_356, x_360, x_354, x_3, x_4, x_5, x_6, x_359);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_362 = !lean_is_exclusive(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = lean_ctor_get(x_361, 0);
lean_dec(x_363);
x_364 = lean_box(x_358);
lean_ctor_set(x_361, 0, x_364);
return x_361;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_361, 1);
lean_inc(x_365);
lean_dec(x_361);
x_366 = lean_box(x_358);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_365);
return x_367;
}
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isExprDefEq___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__1(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1___boxed), 8, 1);
lean_closure_set(x_8, 0, x_2);
x_9 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_preprocess___spec__1___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_commitWhen___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___spec__3(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_eqvFirstTypeResult___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_apply_1(x_3, x_1);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg___lambda__1), 10, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
lean_object* l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg), 9, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("resulting universe mismatch, given");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_3);
x_11 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_3, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_indentExpr(x_1);
x_16 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg___lambda__4___closed__4;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_indentExpr(x_3);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_11, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_11, 0, x_27);
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 1);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
return x_11;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_11, 0);
x_33 = lean_ctor_get(x_11, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_11);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_3);
lean_dec(x_1);
x_35 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__3;
x_36 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_35, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_36;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___boxed), 10, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(x_1, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__2___boxed), 10, 1);
lean_closure_set(x_11, 0, x_5);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(x_4, x_11, x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid mutually inductive types, ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__3___boxed), 10, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = l_Array_empty___closed__1;
x_13 = l_Lean_Meta_forallTelescopeCompatibleAux___rarg(x_11, x_3, x_1, x_2, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_18, 1, x_26);
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_13, 0, x_33);
return x_13;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_18, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_37 = x_18;
} else {
 lean_dec_ref(x_18);
 x_37 = lean_box(0);
}
x_38 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
if (lean_is_scalar(x_37)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_37;
}
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_34);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_13);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_13, 0);
lean_dec(x_45);
return x_13;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_13, 1);
lean_inc(x_46);
lean_dec(x_13);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_18);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_8, 3);
x_23 = l_Lean_replaceRef(x_20, x_22);
lean_dec(x_22);
lean_dec(x_20);
lean_ctor_set(x_8, 3, x_23);
lean_inc(x_18);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType(x_16, x_18, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_18);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
x_35 = lean_ctor_get(x_8, 2);
x_36 = lean_ctor_get(x_8, 3);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_37 = l_Lean_replaceRef(x_20, x_36);
lean_dec(x_36);
lean_dec(x_20);
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_38, 2, x_35);
lean_ctor_set(x_38, 3, x_37);
lean_inc(x_18);
x_39 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType(x_16, x_18, x_2, x_4, x_5, x_6, x_7, x_38, x_9, x_17);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_18);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_18);
x_43 = lean_ctor_get(x_39, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_45 = x_39;
} else {
 lean_dec_ref(x_39);
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
}
else
{
uint8_t x_47; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_11);
if (x_47 == 0)
{
return x_11;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_11, 0);
x_49 = lean_ctor_get(x_11, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_11);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_get_size(x_1);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3;
x_17 = lean_array_get(x_16, x_1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeader(x_17, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_19);
x_3 = x_22;
x_4 = x_23;
x_11 = x_20;
goto _start;
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
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux(x_1, x_9, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_array_get_size(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_dec_lt(x_16, x_15);
lean_dec(x_15);
if (x_17 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_18; 
lean_free_object(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_6);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(x_13, x_21, x_9, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_21);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_13);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
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
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
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
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_array_get_size(x_41);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_dec_lt(x_44, x_43);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_41);
x_47 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_inc(x_6);
lean_inc(x_2);
x_49 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(0);
x_53 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkHeaders(x_41, x_50, x_9, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_51);
lean_dec(x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_41);
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_59 = x_53;
} else {
 lean_dec_ref(x_53);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_61 = lean_ctor_get(x_49, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_63 = x_49;
} else {
 lean_dec_ref(x_49);
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
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_65 = lean_ctor_get(x_47, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_47, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_67 = x_47;
} else {
 lean_dec_ref(x_47);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
return x_11;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_11, 0);
x_71 = lean_ctor_get(x_11, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_11);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_1, x_14);
x_16 = lean_array_push(x_2, x_6);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(x_3, x_4, x_5, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_4, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_apply_9(x_1, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_2, x_4);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg___lambda__1___boxed), 13, 5);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_5);
lean_closure_set(x_19, 2, x_1);
lean_closure_set(x_19, 3, x_2);
lean_closure_set(x_19, 4, x_3);
x_20 = 0;
x_21 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_17, x_20, x_18, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_21;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg), 12, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_2 < x_1;
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = x_3;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = x_14;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_17);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkTypeFor(x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = 1;
x_25 = x_2 + x_24;
x_26 = x_23;
x_27 = lean_array_uset(x_16, x_2, x_26);
x_2 = x_25;
x_3 = x_27;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_18);
if (x_29 == 0)
{
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_replaceRef(x_1, x_6);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 3);
lean_dec(x_16);
lean_ctor_set(x_11, 3, x_14);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(x_2, x_3, x_4, x_17, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
x_21 = lean_ctor_get(x_11, 2);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
lean_ctor_set(x_22, 3, x_14);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls_loop___rarg(x_2, x_3, x_4, x_23, x_5, x_7, x_8, x_9, x_10, x_22, x_12, x_13);
return x_24;
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_usize_of_nat(x_10);
lean_dec(x_10);
lean_inc(x_1);
x_12 = x_1;
x_13 = lean_box_usize(x_11);
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1;
x_15 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1___boxed), 10, 3);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
lean_closure_set(x_15, 2, x_12);
x_16 = x_15;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_7(x_16, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_1, x_21);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Array_empty___closed__1;
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1___boxed), 13, 5);
lean_closure_set(x_29, 0, x_27);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_18);
lean_closure_set(x_29, 3, x_23);
lean_closure_set(x_29, 4, x_28);
x_30 = l_Lean_Elab_Term_Lean_Elab_Term___instance__8___closed__5;
x_31 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_Lean_Elab_Term___instance__8___spec__2___rarg), 9, 2);
lean_closure_set(x_31, 0, x_30);
lean_closure_set(x_31, 1, x_29);
x_32 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_24, x_25, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg), 9, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_lt(x_1, x_11);
lean_dec(x_11);
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_inferType___at___private_Lean_Elab_Term_0__Lean_Elab_Term_tryLiftAndCoe___spec__2(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1___boxed), 10, 1);
lean_closure_set(x_13, 0, x_1);
x_14 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___spec__1___rarg(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductive datatype parameter mismatch");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nexpected");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_nat_dec_le(x_14, x_5);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_4, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_4, x_18);
lean_dec(x_4);
x_20 = l_Lean_Expr_Lean_Expr___instance__11;
x_21 = lean_array_get(x_20, x_1, x_5);
x_22 = lean_array_get(x_20, x_2, x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
lean_inc(x_21);
x_23 = l_Lean_Meta_isExprDefEq___at_Lean_Elab_Term_synthesizeInstMVarCore___spec__3(x_21, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_19);
lean_dec(x_5);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l_Lean_indentExpr(x_22);
x_28 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__2;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__4;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_indentExpr(x_21);
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_35, x_7, x_8, x_9, x_10, x_11, x_12, x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_22);
lean_dec(x_21);
x_41 = lean_ctor_get(x_23, 1);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_ctor_get(x_3, 2);
x_43 = lean_nat_add(x_5, x_42);
lean_dec(x_5);
x_44 = lean_box(0);
x_4 = x_19;
x_5 = x_43;
x_6 = x_44;
x_13 = x_41;
goto _start;
}
}
else
{
uint8_t x_46; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_23);
if (x_46 == 0)
{
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_23, 0);
x_48 = lean_ctor_get(x_23, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_23);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_13);
return x_50;
}
}
else
{
lean_object* x_51; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_6);
lean_ctor_set(x_51, 1, x_13);
return x_51;
}
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_7);
x_12 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_ctor_get(x_3, 2);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
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
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_mkAppN(x_1, x_2);
x_13 = lean_apply_8(x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_getAppNumArgsAux(x_1, x_14);
x_16 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_17, x_19);
lean_inc(x_2);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_2);
lean_ctor_set(x_21, 2, x_18);
x_22 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_23 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(x_3, x_20, x_21, x_2, x_14, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_21);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_apply_8(x_4, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor resulting type, type expected");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
x_14 = l___private_Lean_Meta_InferType_0__Lean_Meta_isTypeImp___at_Lean_Meta_isType___spec__1(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lean_indentExpr(x_1);
x_19 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_box(0);
x_30 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_14, 0);
x_33 = lean_ctor_get(x_14, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constructor resulting type must be specified in inductive family declaration");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected constructor resulting type");
return x_1;
}
}
static lean_object* _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_inc(x_1);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__1___boxed), 11, 3);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_1);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_11, 3);
x_19 = l_Lean_replaceRef(x_14, x_18);
lean_dec(x_18);
lean_dec(x_14);
lean_ctor_set(x_11, 3, x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
x_21 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__2(x_3, x_2, x_15, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__3;
x_23 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_box(0);
x_30 = 1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Elab_Term_elabTerm(x_28, x_29, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___closed__1;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_32);
x_35 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___spec__1___rarg(x_32, x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_getAppFn(x_36);
x_39 = lean_expr_eqv(x_38, x_3);
lean_dec(x_3);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_32);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
x_40 = l_Lean_indentExpr(x_36);
x_41 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__5;
x_42 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_44 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_44, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4(x_36, x_5, x_2, x_15, x_32, x_50, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
lean_dec(x_2);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_32);
lean_dec(x_11);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_35);
if (x_52 == 0)
{
return x_35;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_35, 0);
x_54 = lean_ctor_get(x_35, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_35);
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
lean_dec(x_11);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_31, 0);
x_58 = lean_ctor_get(x_31, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_31);
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
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_11, 0);
x_61 = lean_ctor_get(x_11, 1);
x_62 = lean_ctor_get(x_11, 2);
x_63 = lean_ctor_get(x_11, 3);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_11);
x_64 = l_Lean_replaceRef(x_14, x_63);
lean_dec(x_63);
lean_dec(x_14);
x_65 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_62);
lean_ctor_set(x_65, 3, x_64);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_5);
if (x_4 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__2(x_3, x_2, x_15, x_66, x_7, x_8, x_9, x_10, x_65, x_12, x_13);
lean_dec(x_2);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_68 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__3;
x_69 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_68, x_7, x_8, x_9, x_10, x_65, x_12, x_13);
lean_dec(x_12);
lean_dec(x_65);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_16, 0);
lean_inc(x_74);
lean_dec(x_16);
x_75 = lean_box(0);
x_76 = 1;
lean_inc(x_12);
lean_inc(x_65);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_77 = l_Lean_Elab_Term_elabTerm(x_74, x_75, x_76, x_7, x_8, x_9, x_10, x_65, x_12, x_13);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___closed__1;
lean_inc(x_12);
lean_inc(x_65);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_78);
x_81 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___spec__1___rarg(x_78, x_80, x_7, x_8, x_9, x_10, x_65, x_12, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Expr_getAppFn(x_82);
x_85 = lean_expr_eqv(x_84, x_3);
lean_dec(x_3);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_78);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
x_86 = l_Lean_indentExpr(x_82);
x_87 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__5;
x_88 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_86);
x_89 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_90 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_90, x_7, x_8, x_9, x_10, x_65, x_12, x_83);
lean_dec(x_12);
lean_dec(x_65);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_box(0);
x_97 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4(x_82, x_5, x_2, x_15, x_78, x_96, x_7, x_8, x_9, x_10, x_65, x_12, x_83);
lean_dec(x_2);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_78);
lean_dec(x_65);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_ctor_get(x_81, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_81, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_100 = x_81;
} else {
 lean_dec_ref(x_81);
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
lean_dec(x_65);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_102 = lean_ctor_get(x_77, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_77, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_104 = x_77;
} else {
 lean_dec_ref(x_77);
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
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_ctor_get(x_16, 3);
lean_inc(x_18);
x_19 = l_Lean_Syntax_getArgs(x_18);
lean_dec(x_18);
x_20 = lean_box(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___boxed), 13, 5);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_1);
lean_closure_set(x_21, 3, x_20);
lean_closure_set(x_21, 4, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Elab_Term_elabBinders___rarg(x_19, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_23);
lean_ctor_set(x_25, 0, x_5);
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
lean_ctor_set(x_5, 1, x_28);
lean_ctor_set(x_5, 0, x_23);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_23);
lean_free_object(x_5);
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
lean_free_object(x_5);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
x_41 = lean_ctor_get(x_39, 3);
lean_inc(x_41);
x_42 = l_Lean_Syntax_getArgs(x_41);
lean_dec(x_41);
x_43 = lean_box(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_44 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___boxed), 13, 5);
lean_closure_set(x_44, 0, x_39);
lean_closure_set(x_44, 1, x_2);
lean_closure_set(x_44, 2, x_1);
lean_closure_set(x_44, 3, x_43);
lean_closure_set(x_44, 4, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l_Lean_Elab_Term_elabBinders___rarg(x_42, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2(x_1, x_2, x_3, x_4, x_40, x_6, x_7, x_8, x_9, x_10, x_11, x_47);
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
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_49);
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
lean_dec(x_46);
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
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_40);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_45, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_45, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_60 = x_45;
} else {
 lean_dec_ref(x_45);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_array_get_size(x_2);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 3);
x_16 = l_Lean_replaceRef(x_12, x_15);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_13);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily(x_13, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_11, 7);
x_21 = l_Array_toList___rarg(x_20);
x_22 = lean_unbox(x_18);
lean_dec(x_18);
x_23 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2(x_1, x_2, x_13, x_22, x_21, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
x_30 = lean_ctor_get(x_8, 2);
x_31 = lean_ctor_get(x_8, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_32 = l_Lean_replaceRef(x_12, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_29);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_32);
lean_inc(x_9);
lean_inc(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_13);
x_34 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_isInductiveFamily(x_13, x_1, x_4, x_5, x_6, x_7, x_33, x_9, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_11, 7);
x_38 = l_Array_toList___rarg(x_37);
x_39 = lean_unbox(x_35);
lean_dec(x_35);
x_40 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2(x_1, x_2, x_13, x_39, x_38, x_4, x_5, x_6, x_7, x_33, x_9, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_33);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_34, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_43 = x_34;
} else {
 lean_dec_ref(x_34);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_3);
x_17 = l_Lean_Elab_Term_levelMVarToParam_x27(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_ctor_set(x_13, 1, x_18);
x_20 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_1, 1, x_22);
lean_ctor_set(x_20, 0, x_1);
return x_20;
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
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_ctor_get(x_1, 1);
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
lean_inc(x_3);
x_29 = l_Lean_Elab_Term_levelMVarToParam_x27(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_30);
x_33 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_32);
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
lean_inc(x_3);
x_43 = l_Lean_Elab_Term_levelMVarToParam_x27(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
x_47 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_46);
lean_ctor_set(x_51, 1, x_48);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_13, 2);
lean_inc(x_3);
x_18 = l_Lean_Elab_Term_levelMVarToParam_x27(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
x_21 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_13, 2, x_22);
lean_ctor_set(x_13, 1, x_19);
x_24 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_24, 0, x_1);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_1, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
x_33 = lean_ctor_get(x_13, 2);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
lean_inc(x_3);
x_34 = l_Lean_Elab_Term_levelMVarToParam_x27(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_3);
x_37 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_38);
x_41 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_30, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
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
lean_ctor_set(x_1, 1, x_42);
lean_ctor_set(x_1, 0, x_40);
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_46 = lean_ctor_get(x_1, 0);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_1);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 2);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 lean_ctor_release(x_46, 2);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
lean_inc(x_3);
x_52 = l_Lean_Elab_Term_levelMVarToParam_x27(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_3);
x_55 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
if (lean_is_scalar(x_51)) {
 x_58 = lean_alloc_ctor(0, 3, 0);
} else {
 x_58 = x_51;
}
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_53);
lean_ctor_set(x_58, 2, x_56);
x_59 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_60);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParamAux___spec__2(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_11, x_15);
lean_dec(x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_14);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse_match__2___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected empty inductive declaration");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unexpected inductive type resulting type");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3;
x_10 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___closed__1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_Meta_forallTelescopeReducing___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___spec__1___rarg(x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 3)
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_15);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__6;
x_24 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 0);
x_27 = lean_ctor_get(x_14, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_14);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_tmp_ind_univ_param");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_tmpIndParam___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_tmpIndParam___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_tmpIndParam___closed__2;
x_2 = l_Lean_mkLevelParam(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_tmpIndParam() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Command_tmpIndParam___closed__3;
return x_1;
}
}
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_shouldInferResultUniverse_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVarsImp___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("cannot infer resulting universe level of inductive datatype, given level contains metavariables ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", provide universe explicitly");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_shouldInferResultUniverse___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVarsImp___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Level_hasMVar(x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_2);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
return x_9;
}
else
{
lean_object* x_16; 
lean_free_object(x_9);
x_16 = l_Lean_Level_getLevelOffset(x_11);
if (lean_obj_tag(x_16) == 5)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Elab_Command_tmpIndParam;
x_19 = l_Lean_Elab_Term_assignLevelMVar(x_17, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = 1;
x_23 = lean_box(x_22);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_16);
x_28 = l_Lean_mkSort(x_11);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_37 = l_Lean_Level_hasMVar(x_35);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_35);
lean_dec(x_2);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; 
x_41 = l_Lean_Level_getLevelOffset(x_35);
if (lean_obj_tag(x_41) == 5)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Elab_Command_tmpIndParam;
x_44 = l_Lean_Elab_Term_assignLevelMVar(x_42, x_43, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
lean_dec(x_2);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = 1;
x_48 = lean_box(x_47);
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
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
x_50 = l_Lean_mkSort(x_35);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__2;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = l_Lean_Elab_Command_shouldInferResultUniverse___closed__4;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_36);
return x_56;
}
}
}
}
}
lean_object* l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_instantiateLevelMVars___at_Lean_Elab_Command_shouldInferResultUniverse___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_shouldInferResultUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_shouldInferResultUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_ctor_get_uint64(x_1, 0);
lean_dec(x_1);
x_11 = lean_box_uint64(x_10);
x_12 = lean_apply_4(x_7, x_11, x_2, x_3, x_4);
return x_12;
}
case 1:
{
lean_object* x_13; uint64_t x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_3, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_1);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_3, x_17);
lean_dec(x_3);
x_19 = lean_box_uint64(x_14);
x_20 = lean_apply_5(x_8, x_13, x_19, x_2, x_18, x_4);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_3);
x_21 = lean_apply_4(x_9, x_1, x_2, x_15, x_4);
return x_21;
}
}
case 2:
{
lean_object* x_22; lean_object* x_23; uint64_t x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_25 = lean_box_uint64(x_24);
x_26 = lean_apply_6(x_5, x_22, x_23, x_25, x_2, x_3, x_4);
return x_26;
}
case 3:
{
lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_30 = lean_box_uint64(x_29);
x_31 = lean_apply_6(x_6, x_27, x_28, x_30, x_2, x_3, x_4);
return x_31;
}
default: 
{
lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = lean_apply_4(x_9, x_1, x_2, x_3, x_4);
return x_32;
}
}
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Command_accLevelAtCtor_match__1___rarg), 9, 0);
return x_2;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_level_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = x_3 + x_8;
x_3 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
uint8_t l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_3);
x_6 = 0;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
x_8 = 0;
return x_8;
}
else
{
size_t x_9; size_t x_10; uint8_t x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2(x_2, x_1, x_9, x_10);
return x_11;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Command_accLevelAtCtor___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to compute resulting universe level of inductive datatype, provide universe explicitly");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_accLevelAtCtor___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_accLevelAtCtor___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
case 1:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_3, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_3, x_26);
lean_dec(x_3);
x_1 = x_23;
x_3 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_3);
x_29 = lean_level_eq(x_1, x_2);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Level_occurs(x_2, x_1);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_5);
x_31 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(x_4, x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_array_push(x_4, x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_11);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_11);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_4);
lean_dec(x_1);
x_35 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_36 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_36;
}
}
else
{
lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
}
}
case 4:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_3, x_38);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Level_occurs(x_2, x_1);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_box(0);
x_12 = x_41;
goto block_21;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_43 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_42, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = lean_level_eq(x_1, x_2);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Level_occurs(x_2, x_1);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_box(0);
x_12 = x_46;
goto block_21;
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_47 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_48 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_47, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_11);
return x_49;
}
}
}
case 5:
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_eq(x_3, x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Level_occurs(x_2, x_1);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_12 = x_53;
goto block_21;
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_55 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_54, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_55;
}
}
else
{
uint8_t x_56; 
x_56 = lean_level_eq(x_1, x_2);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Level_occurs(x_2, x_1);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_box(0);
x_12 = x_58;
goto block_21;
}
else
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_60 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_59, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_60;
}
}
else
{
lean_object* x_61; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_11);
return x_61;
}
}
}
default: 
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
lean_dec(x_1);
lean_inc(x_5);
lean_inc(x_3);
x_64 = l_Lean_Elab_Command_accLevelAtCtor(x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_1 = x_63;
x_4 = x_65;
x_11 = x_66;
goto _start;
}
else
{
uint8_t x_68; 
lean_dec(x_63);
lean_dec(x_5);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_64);
if (x_68 == 0)
{
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
block_21:
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_3);
lean_dec(x_3);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(x_4, x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_push(x_4, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_1);
x_19 = l_Lean_Elab_Command_accLevelAtCtor___closed__2;
x_20 = l_Lean_throwError___at_Lean_Elab_Term_throwTypeMismatchError___spec__1___rarg(x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_20;
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Elab_Command_accLevelAtCtor___spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_contains___at_Lean_Elab_Command_accLevelAtCtor___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_accLevelAtCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Command_accLevelAtCtor(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
lean_dec(x_4);
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_1, x_13);
lean_dec(x_1);
x_15 = lean_box_uint64(x_12);
x_16 = lean_apply_6(x_5, x_14, x_9, x_10, x_11, x_15, x_3);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_5);
x_17 = lean_apply_3(x_6, x_1, x_2, x_3);
return x_17;
}
}
else
{
lean_dec(x_5);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_dec(x_2);
x_22 = lean_box_uint64(x_21);
x_23 = lean_apply_5(x_4, x_18, x_19, x_20, x_22, x_3);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_4);
x_24 = lean_apply_3(x_6, x_7, x_2, x_3);
return x_24;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux_match__1___rarg), 6, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_expr_instantiate1(x_1, x_6);
x_15 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_2, x_3, x_4, x_14, x_5, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_expr_instantiate1(x_1, x_5);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_2, x_3, x_14, x_13, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 0)
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_3, x_19);
x_21 = (uint8_t)((x_18 << 24) >> 61);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__1___boxed), 13, 5);
lean_closure_set(x_22, 0, x_17);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_20);
lean_closure_set(x_22, 4, x_5);
x_23 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_15, x_21, x_16, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
else
{
if (lean_obj_tag(x_4) == 7)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_4, 2);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_26);
x_29 = l___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp(x_26, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVarsImp___spec__1(x_30, x_8, x_9, x_10, x_11, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_6);
lean_inc(x_2);
x_35 = l_Lean_Elab_Command_accLevelAtCtor(x_33, x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = (uint8_t)((x_28 << 24) >> 61);
x_39 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__2___boxed), 12, 4);
lean_closure_set(x_39, 0, x_27);
lean_closure_set(x_39, 1, x_1);
lean_closure_set(x_39, 2, x_2);
lean_closure_set(x_39, 3, x_36);
x_40 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_Term_0__Lean_Elab_Term_elabImplicitLambda___spec__1___rarg(x_25, x_38, x_26, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_35);
if (x_41 == 0)
{
return x_35;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_35, 0);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_35);
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
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_5);
lean_ctor_set(x_49, 1, x_12);
return x_49;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_1, x_2, x_4, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniversesFromCtorTypeAux(x_1, x_2, x_3, x_16, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_18;
x_5 = x_15;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_14, 2);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_4 = x_18;
x_5 = x_15;
x_12 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Array_empty___closed__1;
x_13 = l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2(x_1, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_foldlM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* l_Lean_Elab_Command_mkResultUniverse(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Array_isEmpty___rarg(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_3 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Array_toList___rarg(x_1);
x_7 = l_Lean_Level_mkNaryMax(x_6);
x_8 = l_Lean_Level_isZero(x_7);
if (x_8 == 0)
{
if (x_5 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Level_normalize(x_7);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_Level_isNeverZero(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_levelOne;
x_12 = l_Lean_mkLevelMax(x_7, x_11);
x_13 = l_Lean_Level_normalize(x_12);
lean_dec(x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Level_normalize(x_7);
lean_dec(x_7);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Level_normalize(x_7);
lean_dec(x_7);
return x_15;
}
}
else
{
if (x_5 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = l_Array_toList___rarg(x_1);
x_17 = l_Lean_Level_mkNaryMax(x_16);
x_18 = l_Lean_Level_normalize(x_17);
lean_dec(x_17);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_levelOne;
return x_19;
}
}
}
}
lean_object* l_Lean_Elab_Command_mkResultUniverse___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Command_mkResultUniverse(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_11 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
lean_ctor_set(x_6, 1, x_12);
x_13 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(x_1, x_2, x_8);
lean_ctor_set(x_3, 1, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_3, 1);
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_18 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_16, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(x_1, x_2, x_14);
lean_ctor_set(x_3, 1, x_21);
lean_ctor_set(x_3, 0, x_20);
return x_3;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_22 = lean_ctor_get(x_3, 0);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_3);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_26 = x_22;
} else {
 lean_dec_ref(x_22);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_1);
x_28 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_1, x_2, x_25, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(x_1, x_2, x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_5, 2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = 8192;
x_12 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_10);
x_13 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_10, x_11, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(x_10, x_11, x_9);
lean_ctor_set(x_5, 2, x_15);
lean_ctor_set(x_5, 1, x_14);
x_16 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(x_1, x_7);
lean_ctor_set(x_2, 1, x_16);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
x_20 = lean_ctor_get(x_5, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_21, 0, x_1);
x_22 = 8192;
x_23 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_21);
x_24 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_21, x_22, x_19, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(x_21, x_22, x_20);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_18);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(x_1, x_17);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_2);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 2);
lean_inc(x_33);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 lean_ctor_release(x_29, 2);
 x_34 = x_29;
} else {
 lean_dec_ref(x_29);
 x_34 = lean_box(0);
}
lean_inc(x_1);
x_35 = lean_alloc_closure((void*)(l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed), 2, 1);
lean_closure_set(x_35, 0, x_1);
x_36 = 8192;
x_37 = l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_inc(x_35);
x_38 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM_visit(x_35, x_36, x_32, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(x_35, x_36, x_33);
if (lean_is_scalar(x_34)) {
 x_41 = lean_alloc_ctor(0, 3, 0);
} else {
 x_41 = x_34;
}
lean_ctor_set(x_41, 0, x_31);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(x_1, x_30);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__3(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__3(x_5);
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
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__3(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("updateResultingUniverse us: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", r: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", rOffset: ");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUniverses(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_22; lean_object* x_23; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_16 = x_13;
} else {
 lean_dec_ref(x_13);
 x_16 = lean_box(0);
}
x_44 = lean_st_ref_get(x_11, x_15);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*1);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = 0;
x_22 = x_49;
x_23 = x_48;
goto block_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2;
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__2(x_51, x_6, x_7, x_8, x_9, x_10, x_11, x_50);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_53);
lean_dec(x_53);
x_22 = x_55;
x_23 = x_54;
goto block_43;
}
block_21:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l_Lean_Elab_Command_mkResultUniverse(x_14, x_2);
lean_dec(x_2);
lean_dec(x_14);
x_19 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2(x_18, x_4);
if (lean_is_scalar(x_16)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_16;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
block_43:
{
if (x_22 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = x_23;
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_24 = l_Array_toList___rarg(x_14);
x_25 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__3(x_24);
x_26 = l_Lean_MessageData_ofList(x_25);
lean_dec(x_25);
x_27 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__2;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__4;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_1);
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__6;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_2);
x_35 = l_Lean_fmt___at_Lean_Position_Lean_Data_Position___instance__2___spec__1(x_2);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2;
x_41 = l_Lean_addTrace___at___private_Lean_Elab_Term_0__Lean_Elab_Term_postponeElabTerm___spec__1(x_40, x_39, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_17 = x_42;
goto block_21;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_13);
if (x_56 == 0)
{
return x_13;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_accLevelAtCtor___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Level_getOffsetAux(x_11, x_13);
x_15 = l_Lean_Level_getLevelOffset(x_11);
lean_dec(x_11);
x_16 = l_Lean_Level_isParam(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_2);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__2;
x_18 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1(x_15, x_14, x_1, x_2, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__1(x_1, x_4, x_3);
return x_5;
}
}
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___spec__2___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("bootstrap");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("inductiveCheckResultingUniverse");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__2;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("by default the `inductive/structure commands report an error if the resulting universe is not zero, but may be zero for some universe parameters. Reason: unless this type is a subsingleton, it is hardly what the user wants since it can only eliminate into `Prop`. In the `Init` package, we define subsingletons, and we use this option to disable the check. This option may be deleted in the future after we improve the validator");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn____x40_Lean_Data_Options___hyg_479____closed__3;
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__1;
x_3 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__5;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__4;
x_3 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__6;
x_4 = lean_register_option(x_2, x_3, x_1);
return x_4;
}
}
uint8_t l_Lean_Elab_Command_getCheckResultingUniverseOption(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__4;
x_3 = 1;
x_4 = l_Lean_KVMap_getBool(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Command_getCheckResultingUniverseOption___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Command_getCheckResultingUniverseOption(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkResultingUniverse___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid universe polymorphic type, the resultant universe is not Prop (i.e., 0), but it may be Prop for some parameter values (solution: use 'u+1' or 'max 1 u'");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Command_checkResultingUniverse___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Command_checkResultingUniverse___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Command_checkResultingUniverse(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Elab_Command_getCheckResultingUniverseOption(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_MetavarContext_instantiateLevelMVars___at_Lean_Meta_instantiateLevelMVarsImp___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Level_isZero(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Level_isNeverZero(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_13);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_15);
x_20 = l_Lean_indentD(x_19);
x_21 = l_Lean_Elab_Command_checkResultingUniverse___closed__2;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_16);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_2);
x_26 = lean_box(0);
lean_ctor_set(x_13, 0, x_26);
return x_13;
}
}
else
{
lean_object* x_27; 
lean_dec(x_15);
lean_dec(x_2);
x_27 = lean_box(0);
lean_ctor_set(x_13, 0, x_27);
return x_13;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = l_Lean_Level_isZero(x_28);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_Level_isNeverZero(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_28);
x_33 = l_Lean_indentD(x_32);
x_34 = l_Lean_Elab_Command_checkResultingUniverse___closed__2;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_29);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_28);
lean_dec(x_2);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_29);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
lean_dec(x_2);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_29);
return x_42;
}
}
}
}
}
lean_object* l_Lean_Elab_Command_checkResultingUniverse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Command_checkResultingUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkResultingUniverses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_Command_checkResultingUniverse(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_collectUsedFVars(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_1 = x_13;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_15);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
}
lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Term_collectUsedFVars(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_12, 2);
lean_inc(x_17);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_1 = x_13;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
uint8_t x_25; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_CollectFVars_Lean_Util_CollectFVars___instance__1___closed__1;
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_List_forM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectUsed___spec__2(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_12, x_15);
lean_dec(x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Elab_Term_removeUnused(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_removeUnused(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_apply_1(x_3, x_17);
x_19 = l_Lean_Meta_withLCtx___at_Lean_Elab_Term_elabSyntheticHole___spec__1___rarg(x_15, x_16, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg___boxed), 10, 0);
return x_2;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_5);
lean_inc(x_1);
x_18 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_ctor_set(x_13, 1, x_19);
x_21 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_21, 0, x_2);
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
lean_ctor_set(x_2, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_13);
lean_free_object(x_2);
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
lean_free_object(x_13);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_1);
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
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_1);
x_38 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_39);
x_42 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_35, x_3, x_4, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
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
lean_ctor_set(x_2, 1, x_43);
lean_ctor_set(x_2, 0, x_41);
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
lean_free_object(x_2);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
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
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_36);
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_5);
lean_dec(x_1);
x_51 = lean_ctor_get(x_38, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_53 = x_38;
} else {
 lean_dec_ref(x_38);
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
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_2);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_1);
x_60 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_58, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_57);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_56, x_3, x_4, x_5, x_6, x_7, x_8, x_62);
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
lean_dec(x_5);
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
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_5);
lean_inc(x_1);
x_19 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
lean_inc(x_1);
x_22 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_13, 2, x_23);
lean_ctor_set(x_13, 1, x_20);
x_25 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_ctor_set(x_2, 1, x_27);
lean_ctor_set(x_25, 0, x_2);
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
lean_ctor_set(x_2, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_free_object(x_2);
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
lean_dec(x_20);
lean_free_object(x_13);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_free_object(x_13);
lean_dec(x_18);
lean_dec(x_16);
lean_free_object(x_2);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
return x_19;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_19);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
x_46 = lean_ctor_get(x_13, 2);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_1);
x_47 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_45, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_5);
lean_inc(x_1);
x_50 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_51);
x_54 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
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
lean_ctor_set(x_2, 1, x_55);
lean_ctor_set(x_2, 0, x_53);
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_2);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_53);
lean_free_object(x_2);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_61 = x_54;
} else {
 lean_dec_ref(x_54);
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
lean_dec(x_48);
lean_dec(x_44);
lean_free_object(x_2);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_1);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_65 = x_50;
} else {
 lean_dec_ref(x_50);
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
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_46);
lean_dec(x_44);
lean_free_object(x_2);
lean_dec(x_43);
lean_dec(x_5);
lean_dec(x_1);
x_67 = lean_ctor_get(x_47, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_69 = x_47;
} else {
 lean_dec_ref(x_47);
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
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_2, 0);
x_72 = lean_ctor_get(x_2, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_2);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_71, 2);
lean_inc(x_75);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 lean_ctor_release(x_71, 2);
 x_76 = x_71;
} else {
 lean_dec_ref(x_71);
 x_76 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_1);
x_77 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_1, x_74, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_5);
lean_inc(x_1);
x_80 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
if (lean_is_scalar(x_76)) {
 x_83 = lean_alloc_ctor(0, 3, 0);
} else {
 x_83 = x_76;
}
lean_ctor_set(x_83, 0, x_73);
lean_ctor_set(x_83, 1, x_78);
lean_ctor_set(x_83, 2, x_81);
x_84 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_83);
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_92 = x_84;
} else {
 lean_dec_ref(x_84);
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
lean_dec(x_78);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_1);
x_94 = lean_ctor_get(x_80, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_80, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_96 = x_80;
} else {
 lean_dec_ref(x_80);
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
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_5);
lean_dec(x_1);
x_98 = lean_ctor_get(x_77, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_77, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_100 = x_77;
} else {
 lean_dec_ref(x_77);
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
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
lean_object* l_List_foldl___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_CollectLevelParams_main(x_5, x_1);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_List_foldl___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_CollectLevelParams_main(x_5, x_1);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_List_foldl___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__1(x_6, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_CollectLevelParams_Lean_Util_CollectLevelParams___instance__1___closed__1;
x_3 = l_List_foldl___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive___spec__2(x_2, x_1);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Nat_foldAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_5, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_5, x_9);
lean_dec(x_5);
x_11 = lean_nat_add(x_10, x_9);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_11);
x_13 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2;
x_14 = lean_array_get(x_13, x_1, x_12);
x_15 = l_Lean_Expr_Lean_Expr___instance__11;
x_16 = lean_array_get(x_15, x_2, x_12);
lean_dec(x_12);
x_17 = lean_ctor_get(x_14, 3);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_3);
x_18 = l_Lean_mkConst(x_17, x_3);
x_19 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_6, x_16, x_18);
x_5 = x_10;
x_6 = x_19;
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
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_List_map___at_Lean_Meta_addGlobalInstanceImp___spec__1(x_3);
x_5 = lean_array_get_size(x_1);
x_6 = l_Std_HashMap_Std_Data_HashMap___instance__1___closed__1;
lean_inc(x_5);
x_7 = l_Nat_foldAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1(x_1, x_2, x_4, x_5, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Nat_foldAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldAux___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_239; lean_object* x_240; size_t x_241; uint8_t x_242; 
x_7 = lean_ptr_addr(x_5);
x_8 = x_4 == 0 ? 0 : x_7 % x_4;
x_239 = lean_ctor_get(x_6, 0);
lean_inc(x_239);
x_240 = lean_array_uget(x_239, x_8);
x_241 = lean_ptr_addr(x_240);
lean_dec(x_240);
x_242 = x_241 == x_7;
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = l_Lean_Expr_isFVar(x_5);
if (x_243 == 0)
{
lean_object* x_244; 
lean_dec(x_239);
x_244 = lean_box(0);
x_9 = x_244;
goto block_238;
}
else
{
lean_object* x_245; 
x_245 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_2, x_5);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; 
lean_dec(x_239);
x_246 = lean_box(0);
x_9 = x_246;
goto block_238;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
lean_dec(x_245);
x_248 = lean_unsigned_to_nat(0u);
x_249 = l_Array_extract___rarg(x_3, x_248, x_1);
x_250 = l_Lean_mkAppN(x_247, x_249);
lean_dec(x_249);
x_251 = lean_array_uset(x_239, x_8, x_5);
x_252 = lean_ctor_get(x_6, 1);
lean_inc(x_252);
lean_dec(x_6);
lean_inc(x_250);
x_253 = lean_array_uset(x_252, x_8, x_250);
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_250);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_239);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_256 = lean_ctor_get(x_6, 1);
lean_inc(x_256);
x_257 = lean_array_uget(x_256, x_8);
lean_dec(x_256);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_6);
return x_258;
}
block_238:
{
lean_dec(x_9);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_1);
x_13 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_10, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
x_16 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_11, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_inc(x_5);
x_21 = lean_array_uset(x_20, x_8, x_5);
x_22 = !lean_is_exclusive(x_5);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_5, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_5, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_expr_update_app(x_5, x_14, x_18);
lean_inc(x_26);
x_27 = lean_array_uset(x_25, x_8, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_5);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set_uint64(x_30, sizeof(void*)*2, x_12);
x_31 = lean_expr_update_app(x_30, x_14, x_18);
lean_inc(x_31);
x_32 = lean_array_uset(x_29, x_8, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_16, 1, x_33);
lean_ctor_set(x_16, 0, x_31);
return x_16;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_inc(x_5);
x_37 = lean_array_uset(x_36, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_38 = x_5;
} else {
 lean_dec_ref(x_5);
 x_38 = lean_box(0);
}
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(5, 2, 8);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_11);
lean_ctor_set_uint64(x_40, sizeof(void*)*2, x_12);
x_41 = lean_expr_update_app(x_40, x_14, x_34);
lean_inc(x_41);
x_42 = lean_array_uset(x_39, x_8, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_5, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_5, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_5, 2);
lean_inc(x_47);
x_48 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_46);
lean_inc(x_3);
lean_inc(x_1);
x_49 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_46, x_6);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_47);
x_52 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_47, x_51);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_ctor_get(x_52, 1);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_inc(x_5);
x_57 = lean_array_uset(x_56, x_8, x_5);
x_58 = !lean_is_exclusive(x_5);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_5, 2);
lean_dec(x_59);
x_60 = lean_ctor_get(x_5, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_5, 0);
lean_dec(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = (uint8_t)((x_48 << 24) >> 61);
x_64 = lean_expr_update_lambda(x_5, x_63, x_50, x_54);
lean_inc(x_64);
x_65 = lean_array_uset(x_62, x_8, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_52, 1, x_66);
lean_ctor_set(x_52, 0, x_64);
return x_52;
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_5);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_68, 0, x_45);
lean_ctor_set(x_68, 1, x_46);
lean_ctor_set(x_68, 2, x_47);
lean_ctor_set_uint64(x_68, sizeof(void*)*3, x_48);
x_69 = (uint8_t)((x_48 << 24) >> 61);
x_70 = lean_expr_update_lambda(x_68, x_69, x_50, x_54);
lean_inc(x_70);
x_71 = lean_array_uset(x_67, x_8, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_52, 1, x_72);
lean_ctor_set(x_52, 0, x_70);
return x_52;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_52, 0);
x_74 = lean_ctor_get(x_52, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_52);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_inc(x_5);
x_76 = lean_array_uset(x_75, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_77 = x_5;
} else {
 lean_dec_ref(x_5);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(6, 3, 8);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_45);
lean_ctor_set(x_79, 1, x_46);
lean_ctor_set(x_79, 2, x_47);
lean_ctor_set_uint64(x_79, sizeof(void*)*3, x_48);
x_80 = (uint8_t)((x_48 << 24) >> 61);
x_81 = lean_expr_update_lambda(x_79, x_80, x_50, x_73);
lean_inc(x_81);
x_82 = lean_array_uset(x_78, x_8, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
case 7:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_85 = lean_ctor_get(x_5, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_5, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_5, 2);
lean_inc(x_87);
x_88 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_86);
lean_inc(x_3);
lean_inc(x_1);
x_89 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_86, x_6);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_87);
x_92 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_87, x_91);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_inc(x_5);
x_97 = lean_array_uset(x_96, x_8, x_5);
x_98 = !lean_is_exclusive(x_5);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_99 = lean_ctor_get(x_5, 2);
lean_dec(x_99);
x_100 = lean_ctor_get(x_5, 1);
lean_dec(x_100);
x_101 = lean_ctor_get(x_5, 0);
lean_dec(x_101);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_dec(x_95);
x_103 = (uint8_t)((x_88 << 24) >> 61);
x_104 = lean_expr_update_forall(x_5, x_103, x_90, x_94);
lean_inc(x_104);
x_105 = lean_array_uset(x_102, x_8, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_97);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_92, 1, x_106);
lean_ctor_set(x_92, 0, x_104);
return x_92;
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_5);
x_107 = lean_ctor_get(x_95, 1);
lean_inc(x_107);
lean_dec(x_95);
x_108 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_108, 0, x_85);
lean_ctor_set(x_108, 1, x_86);
lean_ctor_set(x_108, 2, x_87);
lean_ctor_set_uint64(x_108, sizeof(void*)*3, x_88);
x_109 = (uint8_t)((x_88 << 24) >> 61);
x_110 = lean_expr_update_forall(x_108, x_109, x_90, x_94);
lean_inc(x_110);
x_111 = lean_array_uset(x_107, x_8, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_97);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set(x_92, 1, x_112);
lean_ctor_set(x_92, 0, x_110);
return x_92;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_ctor_get(x_92, 0);
x_114 = lean_ctor_get(x_92, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_92);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_inc(x_5);
x_116 = lean_array_uset(x_115, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_117 = x_5;
} else {
 lean_dec_ref(x_5);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
lean_dec(x_114);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(7, 3, 8);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_85);
lean_ctor_set(x_119, 1, x_86);
lean_ctor_set(x_119, 2, x_87);
lean_ctor_set_uint64(x_119, sizeof(void*)*3, x_88);
x_120 = (uint8_t)((x_88 << 24) >> 61);
x_121 = lean_expr_update_forall(x_119, x_120, x_90, x_113);
lean_inc(x_121);
x_122 = lean_array_uset(x_118, x_8, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_116);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
case 8:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint64_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_125 = lean_ctor_get(x_5, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_5, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_5, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_5, 3);
lean_inc(x_128);
x_129 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_126);
lean_inc(x_3);
lean_inc(x_1);
x_130 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_126, x_6);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_127);
lean_inc(x_3);
lean_inc(x_1);
x_133 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_127, x_132);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
lean_inc(x_128);
x_136 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_128, x_135);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_inc(x_5);
x_141 = lean_array_uset(x_140, x_8, x_5);
x_142 = !lean_is_exclusive(x_5);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_143 = lean_ctor_get(x_5, 3);
lean_dec(x_143);
x_144 = lean_ctor_get(x_5, 2);
lean_dec(x_144);
x_145 = lean_ctor_get(x_5, 1);
lean_dec(x_145);
x_146 = lean_ctor_get(x_5, 0);
lean_dec(x_146);
x_147 = lean_ctor_get(x_139, 1);
lean_inc(x_147);
lean_dec(x_139);
x_148 = lean_expr_update_let(x_5, x_131, x_134, x_138);
lean_inc(x_148);
x_149 = lean_array_uset(x_147, x_8, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_141);
lean_ctor_set(x_150, 1, x_149);
lean_ctor_set(x_136, 1, x_150);
lean_ctor_set(x_136, 0, x_148);
return x_136;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_5);
x_151 = lean_ctor_get(x_139, 1);
lean_inc(x_151);
lean_dec(x_139);
x_152 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_152, 0, x_125);
lean_ctor_set(x_152, 1, x_126);
lean_ctor_set(x_152, 2, x_127);
lean_ctor_set(x_152, 3, x_128);
lean_ctor_set_uint64(x_152, sizeof(void*)*4, x_129);
x_153 = lean_expr_update_let(x_152, x_131, x_134, x_138);
lean_inc(x_153);
x_154 = lean_array_uset(x_151, x_8, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_141);
lean_ctor_set(x_155, 1, x_154);
lean_ctor_set(x_136, 1, x_155);
lean_ctor_set(x_136, 0, x_153);
return x_136;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_156 = lean_ctor_get(x_136, 0);
x_157 = lean_ctor_get(x_136, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_136);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_inc(x_5);
x_159 = lean_array_uset(x_158, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_160 = x_5;
} else {
 lean_dec_ref(x_5);
 x_160 = lean_box(0);
}
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
if (lean_is_scalar(x_160)) {
 x_162 = lean_alloc_ctor(8, 4, 8);
} else {
 x_162 = x_160;
}
lean_ctor_set(x_162, 0, x_125);
lean_ctor_set(x_162, 1, x_126);
lean_ctor_set(x_162, 2, x_127);
lean_ctor_set(x_162, 3, x_128);
lean_ctor_set_uint64(x_162, sizeof(void*)*4, x_129);
x_163 = lean_expr_update_let(x_162, x_131, x_134, x_156);
lean_inc(x_163);
x_164 = lean_array_uset(x_161, x_8, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
case 10:
{
lean_object* x_167; lean_object* x_168; uint64_t x_169; lean_object* x_170; uint8_t x_171; 
x_167 = lean_ctor_get(x_5, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_5, 1);
lean_inc(x_168);
x_169 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_168);
x_170 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_168, x_6);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = lean_ctor_get(x_170, 1);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_inc(x_5);
x_175 = lean_array_uset(x_174, x_8, x_5);
x_176 = !lean_is_exclusive(x_5);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_5, 1);
lean_dec(x_177);
x_178 = lean_ctor_get(x_5, 0);
lean_dec(x_178);
x_179 = lean_ctor_get(x_173, 1);
lean_inc(x_179);
lean_dec(x_173);
x_180 = lean_expr_update_mdata(x_5, x_172);
lean_inc(x_180);
x_181 = lean_array_uset(x_179, x_8, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_175);
lean_ctor_set(x_182, 1, x_181);
lean_ctor_set(x_170, 1, x_182);
lean_ctor_set(x_170, 0, x_180);
return x_170;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_5);
x_183 = lean_ctor_get(x_173, 1);
lean_inc(x_183);
lean_dec(x_173);
x_184 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_184, 0, x_167);
lean_ctor_set(x_184, 1, x_168);
lean_ctor_set_uint64(x_184, sizeof(void*)*2, x_169);
x_185 = lean_expr_update_mdata(x_184, x_172);
lean_inc(x_185);
x_186 = lean_array_uset(x_183, x_8, x_185);
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_175);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set(x_170, 1, x_187);
lean_ctor_set(x_170, 0, x_185);
return x_170;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_188 = lean_ctor_get(x_170, 0);
x_189 = lean_ctor_get(x_170, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_170);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
lean_inc(x_5);
x_191 = lean_array_uset(x_190, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_192 = x_5;
} else {
 lean_dec_ref(x_5);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
lean_dec(x_189);
if (lean_is_scalar(x_192)) {
 x_194 = lean_alloc_ctor(10, 2, 8);
} else {
 x_194 = x_192;
}
lean_ctor_set(x_194, 0, x_167);
lean_ctor_set(x_194, 1, x_168);
lean_ctor_set_uint64(x_194, sizeof(void*)*2, x_169);
x_195 = lean_expr_update_mdata(x_194, x_188);
lean_inc(x_195);
x_196 = lean_array_uset(x_193, x_8, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_191);
lean_ctor_set(x_197, 1, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
case 11:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint64_t x_202; lean_object* x_203; uint8_t x_204; 
x_199 = lean_ctor_get(x_5, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_5, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_5, 2);
lean_inc(x_201);
x_202 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_201);
x_203 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_4, x_201, x_6);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
lean_inc(x_5);
x_208 = lean_array_uset(x_207, x_8, x_5);
x_209 = !lean_is_exclusive(x_5);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_ctor_get(x_5, 2);
lean_dec(x_210);
x_211 = lean_ctor_get(x_5, 1);
lean_dec(x_211);
x_212 = lean_ctor_get(x_5, 0);
lean_dec(x_212);
x_213 = lean_ctor_get(x_206, 1);
lean_inc(x_213);
lean_dec(x_206);
x_214 = lean_expr_update_proj(x_5, x_205);
lean_inc(x_214);
x_215 = lean_array_uset(x_213, x_8, x_214);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_208);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_203, 1, x_216);
lean_ctor_set(x_203, 0, x_214);
return x_203;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_5);
x_217 = lean_ctor_get(x_206, 1);
lean_inc(x_217);
lean_dec(x_206);
x_218 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_218, 0, x_199);
lean_ctor_set(x_218, 1, x_200);
lean_ctor_set(x_218, 2, x_201);
lean_ctor_set_uint64(x_218, sizeof(void*)*3, x_202);
x_219 = lean_expr_update_proj(x_218, x_205);
lean_inc(x_219);
x_220 = lean_array_uset(x_217, x_8, x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_208);
lean_ctor_set(x_221, 1, x_220);
lean_ctor_set(x_203, 1, x_221);
lean_ctor_set(x_203, 0, x_219);
return x_203;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_222 = lean_ctor_get(x_203, 0);
x_223 = lean_ctor_get(x_203, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_203);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_inc(x_5);
x_225 = lean_array_uset(x_224, x_8, x_5);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_226 = x_5;
} else {
 lean_dec_ref(x_5);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_dec(x_223);
if (lean_is_scalar(x_226)) {
 x_228 = lean_alloc_ctor(11, 3, 8);
} else {
 x_228 = x_226;
}
lean_ctor_set(x_228, 0, x_199);
lean_ctor_set(x_228, 1, x_200);
lean_ctor_set(x_228, 2, x_201);
lean_ctor_set_uint64(x_228, sizeof(void*)*3, x_202);
x_229 = lean_expr_update_proj(x_228, x_222);
lean_inc(x_229);
x_230 = lean_array_uset(x_227, x_8, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_225);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
case 12:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_233 = l_Lean_Meta_AbstractMVars_abstractExprMVars___closed__1;
x_234 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___closed__4;
x_235 = lean_panic_fn(x_233, x_234);
x_236 = lean_apply_1(x_235, x_6);
return x_236;
}
default: 
{
lean_object* x_237; 
lean_dec(x_3);
lean_dec(x_1);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_5);
lean_ctor_set(x_237, 1, x_6);
return x_237;
}
}
}
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 8192;
x_13 = l_Lean_Expr_ReplaceImpl_initCache;
lean_inc(x_3);
x_14 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_12, x_4, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_16;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed), 11, 2);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_22 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_19, x_20, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_ctor_set(x_15, 1, x_23);
x_25 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_24);
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
lean_dec(x_15);
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
lean_free_object(x_15);
lean_dec(x_18);
lean_free_object(x_4);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_22);
if (x_35 == 0)
{
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 0);
x_37 = lean_ctor_get(x_22, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_22);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_4, 1);
x_40 = lean_ctor_get(x_15, 0);
x_41 = lean_ctor_get(x_15, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_15);
lean_inc(x_2);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_43 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed), 11, 2);
lean_closure_set(x_43, 0, x_1);
lean_closure_set(x_43, 1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_41, x_42, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
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
lean_ctor_set(x_4, 1, x_49);
lean_ctor_set(x_4, 0, x_47);
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_4);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_47);
lean_free_object(x_4);
x_53 = lean_ctor_get(x_48, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_55 = x_48;
} else {
 lean_dec_ref(x_48);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_40);
lean_free_object(x_4);
lean_dec(x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_ctor_get(x_44, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_44, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_4, 0);
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_4);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
lean_inc(x_2);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_67 = lean_alloc_closure((void*)(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed), 11, 2);
lean_closure_set(x_67, 0, x_1);
lean_closure_set(x_67, 1, x_3);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_68 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_elabLetDeclAux___spec__1___rarg(x_64, x_66, x_67, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
if (lean_is_scalar(x_65)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_65;
}
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_69);
x_72 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_71);
lean_ctor_set(x_76, 1, x_73);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_71);
x_78 = lean_ctor_get(x_72, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_72, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_80 = x_72;
} else {
 lean_dec_ref(x_72);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_68, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_84 = x_68;
} else {
 lean_dec_ref(x_68);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_15, 1);
x_20 = lean_ctor_get(x_15, 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_20, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_ctor_set(x_15, 2, x_22);
x_24 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(x_1, x_2, x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_ctor_set(x_4, 1, x_26);
lean_ctor_set(x_24, 0, x_4);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_4, 1, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_15);
lean_free_object(x_4);
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
uint8_t x_34; 
lean_free_object(x_15);
lean_dec(x_19);
lean_dec(x_18);
lean_free_object(x_4);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_4, 1);
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
x_41 = lean_ctor_get(x_15, 2);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_41, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_40);
lean_ctor_set(x_45, 2, x_43);
x_46 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(x_1, x_2, x_3, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
lean_ctor_set(x_4, 1, x_47);
lean_ctor_set(x_4, 0, x_45);
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_4);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_45);
lean_free_object(x_4);
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
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_40);
lean_dec(x_39);
lean_free_object(x_4);
lean_dec(x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_42, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_57 = x_42;
} else {
 lean_dec_ref(x_42);
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
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
x_63 = lean_ctor_get(x_59, 2);
lean_inc(x_63);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_64 = x_59;
} else {
 lean_dec_ref(x_59);
 x_64 = lean_box(0);
}
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_65 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2(x_1, x_2, x_3, x_63, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
if (lean_is_scalar(x_64)) {
 x_68 = lean_alloc_ctor(0, 3, 0);
} else {
 x_68 = x_64;
}
lean_ctor_set(x_68, 0, x_61);
lean_ctor_set(x_68, 1, x_62);
lean_ctor_set(x_68, 2, x_66);
x_69 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(x_1, x_2, x_3, x_60, x_5, x_6, x_7, x_8, x_9, x_10, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_70);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_68);
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_ctor_get(x_65, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_65, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_81 = x_65;
} else {
 lean_dec_ref(x_65);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkIndFVar2Const(x_1, x_2, x_3);
x_15 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__3(x_4, x_5, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM_visit___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__1(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_12;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*5);
lean_dec(x_6);
x_9 = 1;
x_10 = x_2 + x_9;
x_11 = l_Std_HashMapImp_insert___at_Lean_ClassState_addEntry___spec__6(x_4, x_7, x_8);
x_2 = x_10;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 7);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
x_11 = 1;
x_12 = x_2 + x_11;
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_8, x_8);
if (x_14 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
x_2 = x_12;
goto _start;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1(x_7, x_16, x_17, x_4);
lean_dec(x_7);
x_2 = x_12;
x_4 = x_18;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Std_HashMap_Std_Data_HashMap___instance__1___closed__1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_2, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = l_Std_HashMap_Std_Data_HashMap___instance__1___closed__1;
return x_7;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Std_HashMap_Std_Data_HashMap___instance__1___closed__1;
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2(x_1, x_8, x_9, x_10);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_HashMap_find_x21___rarg___closed__1;
x_2 = l_Std_HashMap_find_x21___rarg___closed__2;
x_3 = lean_unsigned_to_nat(161u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Std_PersistentHashMap_find_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_11 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_8);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(x_2, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_Init_Core___instance__31;
x_14 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1;
x_15 = lean_box(x_13);
x_16 = lean_panic_fn(x_15, x_14);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; 
x_18 = 1;
x_19 = l_Lean_Expr_inferImplicit(x_10, x_1, x_18);
lean_ctor_set(x_6, 1, x_19);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
x_21 = l_Lean_Expr_inferImplicit(x_10, x_1, x_20);
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
x_25 = l_Lean_Expr_inferImplicit(x_10, x_1, x_24);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
uint8_t x_26; lean_object* x_27; 
x_26 = 0;
x_27 = l_Lean_Expr_inferImplicit(x_10, x_1, x_26);
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
x_31 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_28);
x_32 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(x_2, x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = l_Init_Core___instance__31;
x_34 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1;
x_35 = lean_box(x_33);
x_36 = lean_panic_fn(x_35, x_34);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_38 = 1;
x_39 = l_Lean_Expr_inferImplicit(x_30, x_1, x_38);
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
x_42 = l_Lean_Expr_inferImplicit(x_30, x_1, x_41);
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
x_47 = l_Lean_Expr_inferImplicit(x_30, x_1, x_46);
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
x_50 = l_Lean_Expr_inferImplicit(x_30, x_1, x_49);
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
x_57 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_53);
x_58 = l_Std_HashMapImp_find_x3f___at_Lean_hasOutParams___spec__5(x_2, x_54);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = l_Init_Core___instance__31;
x_60 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1;
x_61 = lean_box(x_59);
x_62 = lean_panic_fn(x_61, x_60);
x_63 = lean_unbox(x_62);
lean_dec(x_62);
if (x_63 == 0)
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = 1;
x_65 = l_Lean_Expr_inferImplicit(x_55, x_1, x_64);
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
x_69 = l_Lean_Expr_inferImplicit(x_55, x_1, x_68);
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
x_75 = l_Lean_Expr_inferImplicit(x_55, x_1, x_74);
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
x_79 = l_Lean_Expr_inferImplicit(x_55, x_1, x_78);
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
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_9);
lean_ctor_set(x_6, 2, x_10);
x_11 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(x_1, x_2, x_8);
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
x_16 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_15);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(x_1, x_2, x_12);
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
x_25 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 3, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(x_1, x_2, x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkCtor2InferMod(x_1);
x_5 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(x_2, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_rec_on(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_declareTacticSyntax___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
lean_object* l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_ibelow(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_declareTacticSyntax___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
lean_object* l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_below(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_declareTacticSyntax___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
lean_object* l_Lean_mkNoConfusion___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_no_confusion(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_declareTacticSyntax___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
lean_object* l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_cases_on(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_declareTacticSyntax___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
if (x_2 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__2(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (x_1 == 0)
{
lean_object* x_13; 
x_13 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
else
{
if (x_2 == 0)
{
lean_object* x_14; 
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__1(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
else
{
lean_object* x_15; 
lean_inc(x_10);
lean_inc(x_6);
x_15 = l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__1(x_1, x_2, x_3, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
lean_dec(x_16);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
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
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__3(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (x_1 == 0)
{
lean_object* x_15; 
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
else
{
if (x_5 == 0)
{
lean_object* x_16; 
x_16 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
else
{
if (x_6 == 0)
{
lean_object* x_17; 
x_17 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_4, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_12);
lean_inc(x_8);
x_18 = l_Lean_mkNoConfusion___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(x_3, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__2(x_1, x_2, x_3, x_4, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_20);
lean_dec(x_19);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_8);
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
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6(uint8_t x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = x_7 < x_6;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_uget(x_5, x_7);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_9);
x_20 = l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
if (x_3 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_inc(x_13);
lean_inc(x_9);
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__3(x_3, x_4, x_19, x_8, x_1, x_2, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
lean_dec(x_8);
lean_dec(x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = x_7 + x_26;
x_7 = x_27;
x_8 = x_25;
x_15 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_13);
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
lean_inc(x_13);
lean_inc(x_9);
x_34 = l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_13);
lean_inc(x_9);
x_37 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__3(x_3, x_4, x_19, x_8, x_1, x_2, x_35, x_9, x_10, x_11, x_12, x_13, x_14, x_36);
lean_dec(x_35);
lean_dec(x_8);
lean_dec(x_19);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = 1;
x_42 = x_7 + x_41;
x_7 = x_42;
x_8 = x_40;
x_15 = x_39;
goto _start;
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_9);
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
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
x_48 = !lean_is_exclusive(x_34);
if (x_48 == 0)
{
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_34, 0);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_34);
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
uint8_t x_52; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
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
}
}
lean_object* l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_binduction_on(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_declareTacticSyntax___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
lean_object* l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_mk_brec_on(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_throwKernelException___at_Lean_Elab_Term_declareTacticSyntax___spec__2(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_6);
lean_dec(x_2);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_7, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
lean_ctor_set(x_18, 0, x_16);
x_22 = lean_st_ref_set(x_7, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_18, 1);
x_30 = lean_ctor_get(x_18, 2);
x_31 = lean_ctor_get(x_18, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_16);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_st_ref_set(x_7, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___lambda__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_1 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_5);
x_12 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
if (x_2 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7(x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Term_0__Lean_Elab_Term_applyAttributesCore___spec__1___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_5 < x_4;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_7);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_array_uget(x_3, x_5);
if (x_1 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_7);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___lambda__1(x_1, x_2, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_5 + x_22;
x_5 = x_23;
x_6 = x_21;
x_13 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec(x_7);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
if (x_2 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_16, 3);
lean_inc(x_29);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_7);
x_30 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___lambda__1(x_1, x_2, x_29, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 1;
x_35 = x_5 + x_34;
x_5 = x_35;
x_6 = x_33;
x_13 = x_32;
goto _start;
}
else
{
uint8_t x_37; 
lean_dec(x_11);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_6);
x_41 = lean_ctor_get(x_16, 3);
lean_inc(x_41);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_7);
x_42 = l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8(x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_11);
lean_inc(x_7);
x_45 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___lambda__1(x_1, x_2, x_41, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_43);
lean_dec(x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = 1;
x_50 = x_5 + x_49;
x_5 = x_50;
x_6 = x_48;
x_13 = x_47;
goto _start;
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_7);
x_52 = !lean_is_exclusive(x_45);
if (x_52 == 0)
{
return x_45;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_45, 0);
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_45);
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
lean_dec(x_41);
lean_dec(x_11);
lean_dec(x_7);
x_56 = !lean_is_exclusive(x_42);
if (x_56 == 0)
{
return x_42;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_42, 0);
x_58 = lean_ctor_get(x_42, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_42);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("PUnit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_eq_x3f___closed__2;
lean_inc(x_12);
x_14 = l_Lean_Environment_contains(x_12, x_13);
x_15 = l_Lean_Expr_heq_x3f___closed__2;
lean_inc(x_12);
x_16 = l_Lean_Environment_contains(x_12, x_15);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2;
lean_inc(x_12);
x_18 = l_Lean_Environment_contains(x_12, x_17);
x_19 = l_Lean_Init_LeanInit___instance__19___rarg___closed__2;
x_20 = l_Lean_Environment_contains(x_12, x_19);
x_21 = lean_array_get_size(x_1);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = lean_box(0);
lean_inc(x_6);
lean_inc(x_2);
x_25 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6(x_14, x_16, x_18, x_20, x_1, x_22, x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9(x_18, x_20, x_1, x_22, x_23, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
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
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
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
lean_dec(x_6);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
lean_object* l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkIBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkBelow___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_mkNoConfusion___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkNoConfusion___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkCasesOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__2(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___lambda__3(x_15, x_16, x_3, x_4, x_17, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_16 = lean_unbox(x_1);
lean_dec(x_1);
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_22 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__6(x_16, x_17, x_18, x_19, x_5, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
return x_22;
}
}
lean_object* l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkBInductionOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkBRecOn___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___lambda__1(x_12, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_18 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___spec__9(x_14, x_15, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_foldM_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_dec(x_5);
x_18 = lean_nat_sub(x_4, x_17);
x_19 = lean_nat_sub(x_18, x_16);
lean_dec(x_18);
x_20 = l_Lean_Expr_Lean_Expr___instance__11;
x_21 = lean_array_get(x_20, x_3, x_19);
x_22 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3;
x_23 = lean_array_get(x_22, x_1, x_19);
lean_dec(x_19);
x_24 = lean_ctor_get(x_23, 4);
lean_inc(x_24);
lean_inc(x_9);
lean_inc(x_2);
x_25 = l_Lean_Meta_mkForallFVars___at_Lean_Elab_Term_elabForall___spec__2(x_2, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_28 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors(x_21, x_2, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_23, 0);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
lean_ctor_set(x_33, 2, x_29);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
x_5 = x_17;
x_6 = x_34;
x_13 = x_30;
goto _start;
}
else
{
uint8_t x_36; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
return x_28;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = lean_ctor_get(x_28, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_28);
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
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_13);
return x_44;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_3 < x_2;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_4);
x_14 = lean_array_uget(x_1, x_3);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = 0;
x_19 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
x_20 = l_Lean_Elab_Term_applyAttributesAt(x_15, x_17, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = x_3 + x_22;
x_24 = lean_box(0);
x_3 = x_23;
x_4 = x_24;
x_11 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
lean_inc(x_9);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_collectLevelParamsInInductive(x_9);
x_18 = l_Lean_Elab_sortDeclLevelParams(x_1, x_2, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_throwError___at_Lean_Elab_Term_throwErrorIfErrors___spec__1___rarg(x_21, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_23);
x_24 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_replaceIndFVarsWithConsts(x_3, x_4, x_23, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod(x_3, x_6, x_25);
x_28 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set(x_28, 2, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*3, x_7);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_28);
x_29 = l_Lean_Elab_Term_ensureNoUnassignedMVars(x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_10);
x_31 = l_Lean_addDecl___at_Lean_Elab_Term_declareTacticSyntax___spec__1(x_28, x_10, x_11, x_12, x_13, x_14, x_15, x_30);
lean_dec(x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_10);
x_33 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions(x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_usize_of_nat(x_8);
x_36 = 0;
x_37 = lean_box(0);
x_38 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2(x_3, x_35, x_36, x_37, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_47 = !lean_is_exclusive(x_33);
if (x_47 == 0)
{
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_33);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
return x_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_31, 0);
x_53 = lean_ctor_get(x_31, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_31);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_55 = !lean_is_exclusive(x_29);
if (x_55 == 0)
{
return x_29;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_29, 0);
x_57 = lean_ctor_get(x_29, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_29);
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
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_24);
if (x_59 == 0)
{
return x_24;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_24, 0);
x_61 = lean_ctor_get(x_24, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_24);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_array_get_size(x_10);
x_19 = lean_nat_add(x_18, x_1);
lean_inc(x_13);
x_20 = l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateParams___spec__2(x_10, x_2, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_11);
x_23 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_levelMVarToParam(x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_22);
if (x_9 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_24);
x_26 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkResultingUniverses(x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(x_3, x_4, x_5, x_6, x_18, x_19, x_7, x_8, x_24, x_11, x_12, x_13, x_14, x_15, x_16, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_35 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse(x_19, x_33, x_11, x_12, x_13, x_14, x_15, x_16, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(x_3, x_4, x_5, x_6, x_18, x_19, x_7, x_8, x_36, x_11, x_12, x_13, x_14, x_15, x_16, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_20);
if (x_43 == 0)
{
return x_20;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_20, 0);
x_45 = lean_ctor_get(x_20, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_20);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_get_size(x_7);
x_17 = lean_box(0);
x_18 = lean_array_get_size(x_1);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_18);
x_19 = l_Nat_foldM_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1(x_2, x_7, x_8, x_18, x_18, x_17, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_reverse___rarg(x_20);
x_23 = 0;
x_24 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l_Lean_Elab_Term_synthesizeSyntheticMVars_loop(x_23, x_24, x_9, x_10, x_11, x_12, x_13, x_14, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_22);
x_27 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse(x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_9);
x_30 = l_Lean_Elab_Command_shouldInferResultUniverse(x_28, x_9, x_10, x_11, x_12, x_13, x_14, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_box(x_5);
lean_inc(x_22);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2___boxed), 17, 9);
lean_closure_set(x_34, 0, x_16);
lean_closure_set(x_34, 1, x_22);
lean_closure_set(x_34, 2, x_3);
lean_closure_set(x_34, 3, x_4);
lean_closure_set(x_34, 4, x_1);
lean_closure_set(x_34, 5, x_8);
lean_closure_set(x_34, 6, x_33);
lean_closure_set(x_34, 7, x_18);
lean_closure_set(x_34, 8, x_31);
x_35 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withUsed___rarg(x_6, x_22, x_34, x_9, x_10, x_11, x_12, x_13, x_14, x_32);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_40; 
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_27);
if (x_40 == 0)
{
return x_27;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_27, 0);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_27);
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
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_25);
if (x_44 == 0)
{
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_19);
if (x_48 == 0)
{
return x_19;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_19, 0);
x_50 = lean_ctor_get(x_19, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_19);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(x_4);
lean_inc(x_6);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3___boxed), 15, 6);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_6);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_3);
lean_closure_set(x_15, 4, x_14);
lean_closure_set(x_15, 5, x_5);
x_16 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg(x_6, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get(x_10, x_2, x_11);
x_13 = l_Lean_Elab_Term_getLevelNames(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_3);
x_16 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_12, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*2 + 3);
lean_dec(x_19);
x_21 = lean_ctor_get(x_12, 0);
lean_inc(x_21);
lean_dec(x_12);
lean_inc(x_2);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeader), 8, 1);
lean_closure_set(x_22, 0, x_2);
x_23 = lean_box(x_20);
lean_inc(x_18);
x_24 = lean_alloc_closure((void*)(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4___boxed), 13, 5);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_14);
lean_closure_set(x_24, 2, x_18);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_1);
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Term_Lean_Elab_Term___instance__8___spec__2___rarg), 9, 2);
lean_closure_set(x_25, 0, x_22);
lean_closure_set(x_25, 1, x_24);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 3);
x_28 = l_Lean_replaceRef(x_21, x_27);
lean_dec(x_27);
lean_dec(x_21);
lean_ctor_set(x_7, 3, x_28);
x_29 = l_Lean_Elab_Term_withLevelNames___rarg(x_18, x_25, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
x_32 = lean_ctor_get(x_7, 2);
x_33 = lean_ctor_get(x_7, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_34 = l_Lean_replaceRef(x_21, x_33);
lean_dec(x_33);
lean_dec(x_21);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_34);
x_36 = l_Lean_Elab_Term_withLevelNames___rarg(x_18, x_25, x_3, x_4, x_5, x_6, x_35, x_8, x_17);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Nat_foldM_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Nat_foldM_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_7);
lean_dec(x_7);
x_19 = lean_unbox(x_9);
lean_dec(x_9);
x_20 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_8, x_19, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_20;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__3(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_2);
return x_17;
}
}
lean_object* l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl___lambda__4(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = l_Lean_Elab_Term_resetMessageLog(x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 3);
x_15 = l_Lean_replaceRef(x_1, x_14);
lean_dec(x_14);
lean_ctor_set(x_8, 3, x_15);
x_16 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl(x_3, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 2);
x_20 = lean_ctor_get(x_8, 3);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_21 = l_Lean_replaceRef(x_1, x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_21);
x_23 = l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkInductiveDecl(x_3, x_2, x_4, x_5, x_6, x_7, x_22, x_9, x_12);
return x_23;
}
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_1, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 3);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_st_ref_get(x_3, x_4);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Command_0__Lean_Elab_Command_getVarDecls(x_12);
lean_dec(x_12);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed), 10, 2);
lean_closure_set(x_15, 0, x_8);
lean_closure_set(x_15, 1, x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabBinders___rarg), 9, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_Command_liftTermElabM___rarg(x_10, x_16, x_2, x_3, x_13);
return x_17;
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Command_elabInductiveViews___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Elab_Command_elabInductiveViews___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Command_elabInductiveViews(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_ReplaceLevel(lean_object*);
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(lean_object*);
lean_object* initialize_Lean_Util_Constructions(lean_object*);
lean_object* initialize_Lean_Elab_Command(lean_object*);
lean_object* initialize_Lean_Elab_CollectFVars(lean_object*);
lean_object* initialize_Lean_Elab_DefView(lean_object*);
lean_object* initialize_Lean_Elab_DeclUtil(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Inductive(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
res = initialize_Lean_Elab_DefView(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_DeclUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__1);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4____closed__2);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__3 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___lambda__1___closed__3);
l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__3 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___lambda__2___closed__3);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__1 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__1);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__2 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__2);
l_Lean_Elab_Command_checkValidInductiveModifier___closed__3 = _init_l_Lean_Elab_Command_checkValidInductiveModifier___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidInductiveModifier___closed__3);
l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__3 = _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___lambda__1___closed__3);
l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__3 = _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___lambda__2___closed__3);
l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__3 = _init_l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___lambda__3___closed__3);
l_Lean_Elab_Command_checkValidCtorModifier___closed__1 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__1);
l_Lean_Elab_Command_checkValidCtorModifier___closed__2 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__2);
l_Lean_Elab_Command_checkValidCtorModifier___closed__3 = _init_l_Lean_Elab_Command_checkValidCtorModifier___closed__3();
lean_mark_persistent(l_Lean_Elab_Command_checkValidCtorModifier___closed__3);
l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__1);
l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__2 = _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1___closed__2);
l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1 = _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Inductive___instance__1);
l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2___closed__1);
l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2 = _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Inductive___instance__2);
l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3___closed__1 = _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3___closed__1);
l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3 = _init_l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3();
lean_mark_persistent(l_Lean_Elab_Command_Lean_Elab_Inductive___instance__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabHeaderAux___lambda__2___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkNumParams___spec__1___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkUnsafe___spec__1___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__1);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__2);
l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__3 = _init_l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkLevelNames___spec__1___closed__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_throwUnexpectedInductiveType___rarg___closed__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingType___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___lambda__1___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_checkParamsAndResultType___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_withInductiveLocalDecls___rarg___boxed__const__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__1 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__1);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__2 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__2);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__3 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__3);
l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__4 = _init_l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__1___closed__4);
l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__1 = _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__1);
l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__2 = _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__4___closed__2);
l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__1 = _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__1();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__1);
l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__2 = _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__2();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__2);
l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__3 = _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__3();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__3);
l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__4 = _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__4();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__4);
l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__5 = _init_l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__5();
lean_mark_persistent(l_List_mapM___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_elabCtors___spec__2___lambda__5___closed__5);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__4 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__4);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__5 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__5);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__6 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_getResultingUniverse___closed__6);
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
l_Lean_Elab_Command_accLevelAtCtor___closed__1 = _init_l_Lean_Elab_Command_accLevelAtCtor___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_accLevelAtCtor___closed__1);
l_Lean_Elab_Command_accLevelAtCtor___closed__2 = _init_l_Lean_Elab_Command_accLevelAtCtor___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_accLevelAtCtor___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__2);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__3 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__3);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__4 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__4);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__5 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__5);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__6 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___lambda__1___closed__6);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_updateResultingUniverse___closed__2);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__1 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__1();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__1);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__2 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__2();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__2);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__3 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__3();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__3);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__4 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__4();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__4);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__5 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__5();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__5);
l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__6 = _init_l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__6();
lean_mark_persistent(l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494____closed__6);
res = l_Lean_Elab_Command_initFn____x40_Lean_Elab_Inductive___hyg_2494_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Command_checkResultingUniverse___closed__1 = _init_l_Lean_Elab_Command_checkResultingUniverse___closed__1();
lean_mark_persistent(l_Lean_Elab_Command_checkResultingUniverse___closed__1);
l_Lean_Elab_Command_checkResultingUniverse___closed__2 = _init_l_Lean_Elab_Command_checkResultingUniverse___closed__2();
lean_mark_persistent(l_Lean_Elab_Command_checkResultingUniverse___closed__2);
l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1 = _init_l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1();
lean_mark_persistent(l_List_map___at___private_Lean_Elab_Inductive_0__Lean_Elab_Command_applyInferMod___spec__1___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__1);
l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2 = _init_l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2();
lean_mark_persistent(l___private_Lean_Elab_Inductive_0__Lean_Elab_Command_mkAuxConstructions___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
