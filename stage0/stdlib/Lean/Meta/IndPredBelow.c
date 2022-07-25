// Lean compiler output
// Module: Lean.Meta.IndPredBelow
// Imports: Init Lean.Meta.Constructions Lean.Meta.Transform Lean.Meta.Tactic Lean.Meta.Match.Match Lean.Meta.Reduce
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
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_introNPRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__11;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__6;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2(lean_object*);
lean_object* l_Std_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_IndPredBelow_mkBelow___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__7;
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_updatePrefix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Meta_IndPredBelow_mkBelow___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3(lean_object*);
lean_object* l_List_zipWith___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_instInhabitedVariables;
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__2;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__3;
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_101_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__13;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_IndPredBelow_mkBelow___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__5;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5;
static lean_object* l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__2;
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3;
lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__1;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_zip___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__8;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3;
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___boxed(lean_object**);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_803____at_Lean_IR_IRType_beq___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__3;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__5;
lean_object* l_Lean_ConstantInfo_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__14;
static lean_object* l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3;
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__4;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__9;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashableExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2;
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__9;
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__2;
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__6;
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
lean_object* l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed(lean_object*);
lean_object* l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2;
lean_object* l_List_mapTRAux___at_Lean_Meta_Match_Alt_toMessageData___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__5;
lean_object* l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2(lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
lean_object* l_Lean_Meta_Match_MkMatcherInput_numDiscrs(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1;
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Meta_evalExprCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkInductiveType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceOptions(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2;
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_IndPredBelow_mkBelow___spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1;
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__2;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__4;
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12;
extern lean_object* l_Lean_Meta_Match_instInhabitedPattern;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7044_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_IndPredBelow_mkBelow___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth;
lean_object* l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__12;
static lean_object* l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__1;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__4;
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_commitWhen___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_rebuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_TSyntax_getNat___spec__1(lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__7;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__4;
lean_object* l_instHashableProd___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__11;
uint8_t l_Lean_Expr_binderInfo(lean_object*);
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instBEqExpr;
static lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__4;
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoCtor___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_IndPredBelow_mkBelow___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1;
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__4;
extern lean_object* l_Lean_instInhabitedInductiveVal;
static lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__5;
static lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2;
extern lean_object* l_Lean_brecOnSuffix;
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__2;
static lean_object* l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__5;
static lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__6;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__1;
static lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__7;
uint8_t l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__2;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__16;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_rebuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__3;
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn___closed__3;
static lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__3;
static lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkInductiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___boxed(lean_object*, lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("maxBackwardChainingDepth", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("The maximum search depth used in the backwards chaining part of the proof of `brecOn` for inductive predicates.", 111);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
x_3 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__2;
x_3 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__5;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_6____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_2 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2;
x_3 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("motive", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("motive_", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_lt(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__2;
x_12 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_11, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_nat_add(x_2, x_9);
x_14 = l_Nat_repr(x_13);
x_15 = l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__3;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
x_20 = l_Lean_Name_str___override(x_19, x_18);
x_21 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_20, x_5, x_6, x_7);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_IndPredBelow_mkContext_motiveName(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = l_Array_insertAt___rarg(x_1, x_2, x_4);
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkForallFVars(x_10, x_3, x_11, x_12, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
lean_inc(x_4);
x_12 = l_Array_toSubarray___rarg(x_4, x_11, x_1);
x_13 = l_Array_ofSubarray___rarg(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_13, x_11, x_2, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1___boxed), 9, 3);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_5);
x_18 = 1;
x_19 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_3, x_18, x_15, x_17, x_6, x_7, x_8, x_9, x_16);
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
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = 1;
x_13 = lean_usize_sub(x_3, x_12);
x_14 = lean_array_uget(x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__2), 10, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_5, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_3 = x_13;
x_5 = x_19;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
else
{
lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = 1;
x_13 = lean_usize_sub(x_3, x_12);
x_14 = lean_array_uget(x_2, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__2), 10, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_16);
lean_closure_set(x_17, 2, x_15);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_5, x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_3 = x_13;
x_5 = x_19;
x_10 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
else
{
lean_object* x_26; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_10);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_le(x_9, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_15 = 0;
x_16 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1(x_2, x_1, x_14, x_15, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_9);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_3);
lean_ctor_set(x_19, 1, x_8);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_21 = 0;
x_22 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2(x_2, x_1, x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_4, x_5);
x_7 = l_Lean_Expr_const___override(x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_fvarId_x21(x_5);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_7, x_2, x_11);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(x_1);
lean_inc(x_2);
x_10 = l_Lean_mkAppN(x_9, x_2);
x_11 = l_Lean_Meta_mkArrow(x_10, x_3, x_4, x_5, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_get_size(x_2);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_2);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1(x_15, x_16, x_2);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = lean_box(x_18);
x_22 = lean_box(x_19);
x_23 = lean_box(x_20);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 10, 5);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_12);
lean_closure_set(x_24, 2, x_21);
lean_closure_set(x_24, 3, x_22);
lean_closure_set(x_24, 4, x_23);
x_25 = l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(x_17, x_24, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_17);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkContext_mkHeader___lambda__1), 8, 1);
lean_closure_set(x_11, 0, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_IndPredBelow_mkContext_addMotives(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_14);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_9 = l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(x_1);
lean_inc(x_2);
x_10 = l_Lean_mkAppN(x_9, x_2);
x_11 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
x_12 = l_Lean_Meta_mkArrow(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 0;
x_16 = 1;
x_17 = 1;
x_18 = l_Lean_Meta_mkForallFVars(x_2, x_13, x_15, x_16, x_17, x_4, x_5, x_6, x_7, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_8, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_IndPredBelow_mkContext_motiveType(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_13, x_2, x_15);
x_2 = x_18;
x_3 = x_19;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_16 = lean_array_fget(x_2, x_4);
x_17 = l_Lean_Meta_IndPredBelow_mkContext_motiveName(x_1, x_4, x_7, x_8, x_9, x_10, x_11);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_22 = lean_array_push(x_6, x_20);
x_3 = x_15;
x_4 = x_21;
x_5 = lean_box(0);
x_6 = x_22;
x_11 = x_19;
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_4, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_5, x_4);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_5, x_4, x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_Meta_IndPredBelow_mkContext_mkHeader(x_1, x_2, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = lean_usize_add(x_4, x_19);
x_21 = lean_array_uset(x_15, x_4, x_17);
x_4 = x_20;
x_5 = x_21;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("below", 5);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
x_9 = l_Lean_Name_append(x_5, x_8);
lean_dec(x_5);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 3);
lean_inc(x_10);
x_11 = l_List_redLength___rarg(x_10);
x_12 = lean_mk_empty_array_with_capacity(x_11);
lean_dec(x_11);
x_13 = l_List_toArrayAux___rarg(x_10, x_12);
x_14 = lean_array_get_size(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = 0;
lean_inc(x_13);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1(x_15, x_16, x_13, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_array_get_size(x_18);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_18);
x_22 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2(x_21, x_16, x_18, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_23);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3(x_23, x_23, x_25, x_27, lean_box(0), x_26, x_2, x_3, x_4, x_5, x_24);
lean_dec(x_23);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
lean_inc(x_18);
lean_inc(x_31);
lean_inc(x_29);
x_32 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4(x_29, x_31, x_21, x_16, x_18, x_2, x_3, x_4, x_5, x_30);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5(x_15, x_16, x_13);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_18);
lean_ctor_set(x_36, 2, x_35);
lean_ctor_set(x_36, 3, x_34);
lean_ctor_set(x_36, 4, x_31);
lean_ctor_set(x_32, 0, x_36);
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5(x_15, x_16, x_13);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_18);
lean_ctor_set(x_40, 2, x_39);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_31);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_13);
x_42 = !lean_is_exclusive(x_32);
if (x_42 == 0)
{
return x_32;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_32, 0);
x_44 = lean_ctor_get(x_32, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_32);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_22);
if (x_46 == 0)
{
return x_22;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_22, 0);
x_48 = lean_ctor_get(x_22, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_22);
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
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_17);
if (x_50 == 0)
{
return x_17;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_17, 0);
x_52 = lean_ctor_get(x_17, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_17);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_7);
if (x_54 == 0)
{
return x_7;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_7, 0);
x_56 = lean_ctor_get(x_7, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_7);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedInductiveVal;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Expr_const___override(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Expr_const___override(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__1;
x_2 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__2;
x_3 = lean_unsigned_to_nat(70u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
if (x_7 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_14 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_15 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_17, x_8);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__2(x_18, x_12, x_13, x_10);
x_20 = l_Lean_Expr_replaceFVars(x_3, x_9, x_19);
lean_dec(x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_array_fget(x_4, x_6);
lean_dec(x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_23, x_8);
x_25 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__3(x_24, x_12, x_13, x_10);
x_26 = l_Lean_Expr_replaceFVars(x_3, x_9, x_25);
lean_dec(x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__2(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__3(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_7);
lean_dec(x_5);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_array_get_size(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_16);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 3);
lean_inc(x_21);
lean_inc(x_20);
x_22 = l_Array_append___rarg(x_20, x_21);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_lt(x_2, x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_4, 4);
lean_inc(x_26);
x_27 = l_Array_append___rarg(x_20, x_26);
x_28 = lean_ctor_get(x_1, 4);
lean_inc(x_28);
x_29 = lean_array_get_size(x_6);
x_30 = l_Array_toSubarray___rarg(x_6, x_28, x_29);
x_31 = l_Array_ofSubarray___rarg(x_30);
x_32 = l_Array_append___rarg(x_27, x_31);
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
if (x_18 == 0)
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_15);
x_79 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_80 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_79);
x_34 = x_80;
goto block_78;
}
else
{
lean_object* x_81; 
x_81 = lean_array_fget(x_15, x_17);
lean_dec(x_15);
x_34 = x_81;
goto block_78;
}
block_78:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_36, x_19);
x_38 = l_Lean_Expr_const___override(x_14, x_37);
x_39 = l_Lean_mkAppN(x_38, x_22);
x_40 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_41 = lean_array_push(x_40, x_39);
x_42 = l_Array_append___rarg(x_32, x_41);
if (x_25 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; 
lean_dec(x_23);
x_43 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_44 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_43);
x_45 = l_Lean_mkAppN(x_44, x_42);
x_46 = 0;
x_47 = 1;
x_48 = 1;
x_49 = l_Lean_Meta_mkForallFVars(x_33, x_45, x_46, x_47, x_48, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_51);
lean_dec(x_51);
lean_dec(x_4);
lean_ctor_set(x_49, 0, x_52);
return x_49;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_49, 0);
x_54 = lean_ctor_get(x_49, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_49);
x_55 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_53);
lean_dec(x_53);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_4);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_49);
if (x_57 == 0)
{
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_49, 0);
x_59 = lean_ctor_get(x_49, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_49);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_array_fget(x_23, x_2);
lean_dec(x_23);
x_62 = l_Lean_mkAppN(x_61, x_42);
x_63 = 0;
x_64 = 1;
x_65 = 1;
x_66 = l_Lean_Meta_mkForallFVars(x_33, x_62, x_63, x_64, x_65, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_68);
lean_dec(x_68);
lean_dec(x_4);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_72 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_70);
lean_dec(x_70);
lean_dec(x_4);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_4);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_66);
if (x_74 == 0)
{
return x_66;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_66, 0);
x_76 = lean_ctor_get(x_66, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_66);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
case 1:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_7);
lean_dec(x_5);
x_82 = lean_ctor_get(x_3, 0);
lean_inc(x_82);
lean_dec(x_3);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_1, 1);
lean_inc(x_84);
x_85 = lean_array_get_size(x_84);
x_86 = lean_unsigned_to_nat(0u);
x_87 = lean_nat_dec_lt(x_86, x_85);
lean_dec(x_85);
x_88 = lean_box(0);
x_89 = lean_ctor_get(x_4, 2);
lean_inc(x_89);
x_90 = lean_ctor_get(x_4, 3);
lean_inc(x_90);
lean_inc(x_89);
x_91 = l_Array_append___rarg(x_89, x_90);
x_92 = lean_ctor_get(x_4, 1);
lean_inc(x_92);
x_93 = lean_array_get_size(x_92);
x_94 = lean_nat_dec_lt(x_2, x_93);
lean_dec(x_93);
x_95 = lean_ctor_get(x_4, 4);
lean_inc(x_95);
x_96 = l_Array_append___rarg(x_89, x_95);
x_97 = lean_ctor_get(x_1, 4);
lean_inc(x_97);
x_98 = lean_array_get_size(x_6);
x_99 = l_Array_toSubarray___rarg(x_6, x_97, x_98);
x_100 = l_Array_ofSubarray___rarg(x_99);
x_101 = l_Array_append___rarg(x_96, x_100);
x_102 = lean_ctor_get(x_4, 0);
lean_inc(x_102);
if (x_87 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_84);
x_148 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_149 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_148);
x_103 = x_149;
goto block_147;
}
else
{
lean_object* x_150; 
x_150 = lean_array_fget(x_84, x_86);
lean_dec(x_84);
x_103 = x_150;
goto block_147;
}
block_147:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_105, x_88);
x_107 = l_Lean_Expr_const___override(x_83, x_106);
x_108 = l_Lean_mkAppN(x_107, x_91);
x_109 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_110 = lean_array_push(x_109, x_108);
x_111 = l_Array_append___rarg(x_101, x_110);
if (x_94 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; 
lean_dec(x_92);
x_112 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_113 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_112);
x_114 = l_Lean_mkAppN(x_113, x_111);
x_115 = 0;
x_116 = 1;
x_117 = 1;
x_118 = l_Lean_Meta_mkForallFVars(x_102, x_114, x_115, x_116, x_117, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_120);
lean_dec(x_120);
lean_dec(x_4);
lean_ctor_set(x_118, 0, x_121);
return x_118;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_118, 0);
x_123 = lean_ctor_get(x_118, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_118);
x_124 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_122);
lean_dec(x_122);
lean_dec(x_4);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
uint8_t x_126; 
lean_dec(x_4);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_118);
if (x_126 == 0)
{
return x_118;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_118, 0);
x_128 = lean_ctor_get(x_118, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_118);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; lean_object* x_135; 
x_130 = lean_array_fget(x_92, x_2);
lean_dec(x_92);
x_131 = l_Lean_mkAppN(x_130, x_111);
x_132 = 0;
x_133 = 1;
x_134 = 1;
x_135 = l_Lean_Meta_mkForallFVars(x_102, x_131, x_132, x_133, x_134, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_137);
lean_dec(x_137);
lean_dec(x_4);
lean_ctor_set(x_135, 0, x_138);
return x_135;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_135, 0);
x_140 = lean_ctor_get(x_135, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_135);
x_141 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_139);
lean_dec(x_139);
lean_dec(x_4);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
uint8_t x_143; 
lean_dec(x_4);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_135);
if (x_143 == 0)
{
return x_135;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_135, 0);
x_145 = lean_ctor_get(x_135, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_135);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
}
}
case 2:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_7);
lean_dec(x_5);
x_151 = lean_ctor_get(x_3, 0);
lean_inc(x_151);
lean_dec(x_3);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_ctor_get(x_1, 1);
lean_inc(x_153);
x_154 = lean_array_get_size(x_153);
x_155 = lean_unsigned_to_nat(0u);
x_156 = lean_nat_dec_lt(x_155, x_154);
lean_dec(x_154);
x_157 = lean_box(0);
x_158 = lean_ctor_get(x_4, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_4, 3);
lean_inc(x_159);
lean_inc(x_158);
x_160 = l_Array_append___rarg(x_158, x_159);
x_161 = lean_ctor_get(x_4, 1);
lean_inc(x_161);
x_162 = lean_array_get_size(x_161);
x_163 = lean_nat_dec_lt(x_2, x_162);
lean_dec(x_162);
x_164 = lean_ctor_get(x_4, 4);
lean_inc(x_164);
x_165 = l_Array_append___rarg(x_158, x_164);
x_166 = lean_ctor_get(x_1, 4);
lean_inc(x_166);
x_167 = lean_array_get_size(x_6);
x_168 = l_Array_toSubarray___rarg(x_6, x_166, x_167);
x_169 = l_Array_ofSubarray___rarg(x_168);
x_170 = l_Array_append___rarg(x_165, x_169);
x_171 = lean_ctor_get(x_4, 0);
lean_inc(x_171);
if (x_156 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_153);
x_217 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_218 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_217);
x_172 = x_218;
goto block_216;
}
else
{
lean_object* x_219; 
x_219 = lean_array_fget(x_153, x_155);
lean_dec(x_153);
x_172 = x_219;
goto block_216;
}
block_216:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_174, x_157);
x_176 = l_Lean_Expr_const___override(x_152, x_175);
x_177 = l_Lean_mkAppN(x_176, x_160);
x_178 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_179 = lean_array_push(x_178, x_177);
x_180 = l_Array_append___rarg(x_170, x_179);
if (x_163 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; lean_object* x_187; 
lean_dec(x_161);
x_181 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_182 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_181);
x_183 = l_Lean_mkAppN(x_182, x_180);
x_184 = 0;
x_185 = 1;
x_186 = 1;
x_187 = l_Lean_Meta_mkForallFVars(x_171, x_183, x_184, x_185, x_186, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_187) == 0)
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_187, 0);
x_190 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_189);
lean_dec(x_189);
lean_dec(x_4);
lean_ctor_set(x_187, 0, x_190);
return x_187;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_187, 0);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_187);
x_193 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_191);
lean_dec(x_191);
lean_dec(x_4);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
uint8_t x_195; 
lean_dec(x_4);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_187);
if (x_195 == 0)
{
return x_187;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_187, 0);
x_197 = lean_ctor_get(x_187, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_187);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; lean_object* x_204; 
x_199 = lean_array_fget(x_161, x_2);
lean_dec(x_161);
x_200 = l_Lean_mkAppN(x_199, x_180);
x_201 = 0;
x_202 = 1;
x_203 = 1;
x_204 = l_Lean_Meta_mkForallFVars(x_171, x_200, x_201, x_202, x_203, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_204) == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_206);
lean_dec(x_206);
lean_dec(x_4);
lean_ctor_set(x_204, 0, x_207);
return x_204;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_204, 0);
x_209 = lean_ctor_get(x_204, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_204);
x_210 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_208);
lean_dec(x_208);
lean_dec(x_4);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
uint8_t x_212; 
lean_dec(x_4);
lean_dec(x_1);
x_212 = !lean_is_exclusive(x_204);
if (x_212 == 0)
{
return x_204;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_204, 0);
x_214 = lean_ctor_get(x_204, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_204);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
}
case 3:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_7);
lean_dec(x_5);
x_220 = lean_ctor_get(x_3, 0);
lean_inc(x_220);
lean_dec(x_3);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_ctor_get(x_1, 1);
lean_inc(x_222);
x_223 = lean_array_get_size(x_222);
x_224 = lean_unsigned_to_nat(0u);
x_225 = lean_nat_dec_lt(x_224, x_223);
lean_dec(x_223);
x_226 = lean_box(0);
x_227 = lean_ctor_get(x_4, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_4, 3);
lean_inc(x_228);
lean_inc(x_227);
x_229 = l_Array_append___rarg(x_227, x_228);
x_230 = lean_ctor_get(x_4, 1);
lean_inc(x_230);
x_231 = lean_array_get_size(x_230);
x_232 = lean_nat_dec_lt(x_2, x_231);
lean_dec(x_231);
x_233 = lean_ctor_get(x_4, 4);
lean_inc(x_233);
x_234 = l_Array_append___rarg(x_227, x_233);
x_235 = lean_ctor_get(x_1, 4);
lean_inc(x_235);
x_236 = lean_array_get_size(x_6);
x_237 = l_Array_toSubarray___rarg(x_6, x_235, x_236);
x_238 = l_Array_ofSubarray___rarg(x_237);
x_239 = l_Array_append___rarg(x_234, x_238);
x_240 = lean_ctor_get(x_4, 0);
lean_inc(x_240);
if (x_225 == 0)
{
lean_object* x_286; lean_object* x_287; 
lean_dec(x_222);
x_286 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_287 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_286);
x_241 = x_287;
goto block_285;
}
else
{
lean_object* x_288; 
x_288 = lean_array_fget(x_222, x_224);
lean_dec(x_222);
x_241 = x_288;
goto block_285;
}
block_285:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_243, x_226);
x_245 = l_Lean_Expr_const___override(x_221, x_244);
x_246 = l_Lean_mkAppN(x_245, x_229);
x_247 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_248 = lean_array_push(x_247, x_246);
x_249 = l_Array_append___rarg(x_239, x_248);
if (x_232 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; uint8_t x_254; uint8_t x_255; lean_object* x_256; 
lean_dec(x_230);
x_250 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_251 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_250);
x_252 = l_Lean_mkAppN(x_251, x_249);
x_253 = 0;
x_254 = 1;
x_255 = 1;
x_256 = l_Lean_Meta_mkForallFVars(x_240, x_252, x_253, x_254, x_255, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_256) == 0)
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; 
x_258 = lean_ctor_get(x_256, 0);
x_259 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_258);
lean_dec(x_258);
lean_dec(x_4);
lean_ctor_set(x_256, 0, x_259);
return x_256;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_ctor_get(x_256, 0);
x_261 = lean_ctor_get(x_256, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_256);
x_262 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_260);
lean_dec(x_260);
lean_dec(x_4);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
else
{
uint8_t x_264; 
lean_dec(x_4);
lean_dec(x_1);
x_264 = !lean_is_exclusive(x_256);
if (x_264 == 0)
{
return x_256;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_256, 0);
x_266 = lean_ctor_get(x_256, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_256);
x_267 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
}
else
{
lean_object* x_268; lean_object* x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; lean_object* x_273; 
x_268 = lean_array_fget(x_230, x_2);
lean_dec(x_230);
x_269 = l_Lean_mkAppN(x_268, x_249);
x_270 = 0;
x_271 = 1;
x_272 = 1;
x_273 = l_Lean_Meta_mkForallFVars(x_240, x_269, x_270, x_271, x_272, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_273) == 0)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_273, 0);
x_276 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_275);
lean_dec(x_275);
lean_dec(x_4);
lean_ctor_set(x_273, 0, x_276);
return x_273;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = lean_ctor_get(x_273, 0);
x_278 = lean_ctor_get(x_273, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_273);
x_279 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_277);
lean_dec(x_277);
lean_dec(x_4);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
uint8_t x_281; 
lean_dec(x_4);
lean_dec(x_1);
x_281 = !lean_is_exclusive(x_273);
if (x_281 == 0)
{
return x_273;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_273, 0);
x_283 = lean_ctor_get(x_273, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_273);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
}
}
case 4:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_7);
lean_dec(x_5);
x_289 = lean_ctor_get(x_3, 0);
lean_inc(x_289);
lean_dec(x_3);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_ctor_get(x_1, 1);
lean_inc(x_291);
x_292 = lean_array_get_size(x_291);
x_293 = lean_unsigned_to_nat(0u);
x_294 = lean_nat_dec_lt(x_293, x_292);
lean_dec(x_292);
x_295 = lean_box(0);
x_296 = lean_ctor_get(x_4, 2);
lean_inc(x_296);
x_297 = lean_ctor_get(x_4, 3);
lean_inc(x_297);
lean_inc(x_296);
x_298 = l_Array_append___rarg(x_296, x_297);
x_299 = lean_ctor_get(x_4, 1);
lean_inc(x_299);
x_300 = lean_array_get_size(x_299);
x_301 = lean_nat_dec_lt(x_2, x_300);
lean_dec(x_300);
x_302 = lean_ctor_get(x_4, 4);
lean_inc(x_302);
x_303 = l_Array_append___rarg(x_296, x_302);
x_304 = lean_ctor_get(x_1, 4);
lean_inc(x_304);
x_305 = lean_array_get_size(x_6);
x_306 = l_Array_toSubarray___rarg(x_6, x_304, x_305);
x_307 = l_Array_ofSubarray___rarg(x_306);
x_308 = l_Array_append___rarg(x_303, x_307);
x_309 = lean_ctor_get(x_4, 0);
lean_inc(x_309);
if (x_294 == 0)
{
lean_object* x_355; lean_object* x_356; 
lean_dec(x_291);
x_355 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_356 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_355);
x_310 = x_356;
goto block_354;
}
else
{
lean_object* x_357; 
x_357 = lean_array_fget(x_291, x_293);
lean_dec(x_291);
x_310 = x_357;
goto block_354;
}
block_354:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
lean_dec(x_310);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec(x_311);
x_313 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_312, x_295);
x_314 = l_Lean_Expr_const___override(x_290, x_313);
x_315 = l_Lean_mkAppN(x_314, x_298);
x_316 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_317 = lean_array_push(x_316, x_315);
x_318 = l_Array_append___rarg(x_308, x_317);
if (x_301 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; uint8_t x_323; uint8_t x_324; lean_object* x_325; 
lean_dec(x_299);
x_319 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_320 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_319);
x_321 = l_Lean_mkAppN(x_320, x_318);
x_322 = 0;
x_323 = 1;
x_324 = 1;
x_325 = l_Lean_Meta_mkForallFVars(x_309, x_321, x_322, x_323, x_324, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_325) == 0)
{
uint8_t x_326; 
x_326 = !lean_is_exclusive(x_325);
if (x_326 == 0)
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_ctor_get(x_325, 0);
x_328 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_327);
lean_dec(x_327);
lean_dec(x_4);
lean_ctor_set(x_325, 0, x_328);
return x_325;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_329 = lean_ctor_get(x_325, 0);
x_330 = lean_ctor_get(x_325, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_325);
x_331 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_329);
lean_dec(x_329);
lean_dec(x_4);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
else
{
uint8_t x_333; 
lean_dec(x_4);
lean_dec(x_1);
x_333 = !lean_is_exclusive(x_325);
if (x_333 == 0)
{
return x_325;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_325, 0);
x_335 = lean_ctor_get(x_325, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_325);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; uint8_t x_340; uint8_t x_341; lean_object* x_342; 
x_337 = lean_array_fget(x_299, x_2);
lean_dec(x_299);
x_338 = l_Lean_mkAppN(x_337, x_318);
x_339 = 0;
x_340 = 1;
x_341 = 1;
x_342 = l_Lean_Meta_mkForallFVars(x_309, x_338, x_339, x_340, x_341, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_342) == 0)
{
uint8_t x_343; 
x_343 = !lean_is_exclusive(x_342);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_342, 0);
x_345 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_344);
lean_dec(x_344);
lean_dec(x_4);
lean_ctor_set(x_342, 0, x_345);
return x_342;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_346 = lean_ctor_get(x_342, 0);
x_347 = lean_ctor_get(x_342, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_342);
x_348 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_346);
lean_dec(x_346);
lean_dec(x_4);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_347);
return x_349;
}
}
else
{
uint8_t x_350; 
lean_dec(x_4);
lean_dec(x_1);
x_350 = !lean_is_exclusive(x_342);
if (x_350 == 0)
{
return x_342;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_342, 0);
x_352 = lean_ctor_get(x_342, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_342);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
}
}
case 5:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_358 = lean_ctor_get(x_5, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_5, 1);
lean_inc(x_359);
lean_dec(x_5);
x_360 = lean_array_set(x_6, x_7, x_359);
x_361 = lean_unsigned_to_nat(1u);
x_362 = lean_nat_sub(x_7, x_361);
lean_dec(x_7);
x_5 = x_358;
x_6 = x_360;
x_7 = x_362;
goto _start;
}
case 6:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_7);
lean_dec(x_5);
x_364 = lean_ctor_get(x_3, 0);
lean_inc(x_364);
lean_dec(x_3);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
lean_dec(x_364);
x_366 = lean_ctor_get(x_1, 1);
lean_inc(x_366);
x_367 = lean_array_get_size(x_366);
x_368 = lean_unsigned_to_nat(0u);
x_369 = lean_nat_dec_lt(x_368, x_367);
lean_dec(x_367);
x_370 = lean_box(0);
x_371 = lean_ctor_get(x_4, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_4, 3);
lean_inc(x_372);
lean_inc(x_371);
x_373 = l_Array_append___rarg(x_371, x_372);
x_374 = lean_ctor_get(x_4, 1);
lean_inc(x_374);
x_375 = lean_array_get_size(x_374);
x_376 = lean_nat_dec_lt(x_2, x_375);
lean_dec(x_375);
x_377 = lean_ctor_get(x_4, 4);
lean_inc(x_377);
x_378 = l_Array_append___rarg(x_371, x_377);
x_379 = lean_ctor_get(x_1, 4);
lean_inc(x_379);
x_380 = lean_array_get_size(x_6);
x_381 = l_Array_toSubarray___rarg(x_6, x_379, x_380);
x_382 = l_Array_ofSubarray___rarg(x_381);
x_383 = l_Array_append___rarg(x_378, x_382);
x_384 = lean_ctor_get(x_4, 0);
lean_inc(x_384);
if (x_369 == 0)
{
lean_object* x_430; lean_object* x_431; 
lean_dec(x_366);
x_430 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_431 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_430);
x_385 = x_431;
goto block_429;
}
else
{
lean_object* x_432; 
x_432 = lean_array_fget(x_366, x_368);
lean_dec(x_366);
x_385 = x_432;
goto block_429;
}
block_429:
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
lean_dec(x_385);
x_387 = lean_ctor_get(x_386, 1);
lean_inc(x_387);
lean_dec(x_386);
x_388 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_387, x_370);
x_389 = l_Lean_Expr_const___override(x_365, x_388);
x_390 = l_Lean_mkAppN(x_389, x_373);
x_391 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_392 = lean_array_push(x_391, x_390);
x_393 = l_Array_append___rarg(x_383, x_392);
if (x_376 == 0)
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; uint8_t x_397; uint8_t x_398; uint8_t x_399; lean_object* x_400; 
lean_dec(x_374);
x_394 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_395 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_394);
x_396 = l_Lean_mkAppN(x_395, x_393);
x_397 = 0;
x_398 = 1;
x_399 = 1;
x_400 = l_Lean_Meta_mkForallFVars(x_384, x_396, x_397, x_398, x_399, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_400) == 0)
{
uint8_t x_401; 
x_401 = !lean_is_exclusive(x_400);
if (x_401 == 0)
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_400, 0);
x_403 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_402);
lean_dec(x_402);
lean_dec(x_4);
lean_ctor_set(x_400, 0, x_403);
return x_400;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_404 = lean_ctor_get(x_400, 0);
x_405 = lean_ctor_get(x_400, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_400);
x_406 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_404);
lean_dec(x_404);
lean_dec(x_4);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_406);
lean_ctor_set(x_407, 1, x_405);
return x_407;
}
}
else
{
uint8_t x_408; 
lean_dec(x_4);
lean_dec(x_1);
x_408 = !lean_is_exclusive(x_400);
if (x_408 == 0)
{
return x_400;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_409 = lean_ctor_get(x_400, 0);
x_410 = lean_ctor_get(x_400, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_400);
x_411 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_411, 0, x_409);
lean_ctor_set(x_411, 1, x_410);
return x_411;
}
}
}
else
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; uint8_t x_415; uint8_t x_416; lean_object* x_417; 
x_412 = lean_array_fget(x_374, x_2);
lean_dec(x_374);
x_413 = l_Lean_mkAppN(x_412, x_393);
x_414 = 0;
x_415 = 1;
x_416 = 1;
x_417 = l_Lean_Meta_mkForallFVars(x_384, x_413, x_414, x_415, x_416, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_417) == 0)
{
uint8_t x_418; 
x_418 = !lean_is_exclusive(x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_417, 0);
x_420 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_419);
lean_dec(x_419);
lean_dec(x_4);
lean_ctor_set(x_417, 0, x_420);
return x_417;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_421 = lean_ctor_get(x_417, 0);
x_422 = lean_ctor_get(x_417, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_417);
x_423 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_421);
lean_dec(x_421);
lean_dec(x_4);
x_424 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_422);
return x_424;
}
}
else
{
uint8_t x_425; 
lean_dec(x_4);
lean_dec(x_1);
x_425 = !lean_is_exclusive(x_417);
if (x_425 == 0)
{
return x_417;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_417, 0);
x_427 = lean_ctor_get(x_417, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_417);
x_428 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
return x_428;
}
}
}
}
}
case 7:
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_7);
lean_dec(x_5);
x_433 = lean_ctor_get(x_3, 0);
lean_inc(x_433);
lean_dec(x_3);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
lean_dec(x_433);
x_435 = lean_ctor_get(x_1, 1);
lean_inc(x_435);
x_436 = lean_array_get_size(x_435);
x_437 = lean_unsigned_to_nat(0u);
x_438 = lean_nat_dec_lt(x_437, x_436);
lean_dec(x_436);
x_439 = lean_box(0);
x_440 = lean_ctor_get(x_4, 2);
lean_inc(x_440);
x_441 = lean_ctor_get(x_4, 3);
lean_inc(x_441);
lean_inc(x_440);
x_442 = l_Array_append___rarg(x_440, x_441);
x_443 = lean_ctor_get(x_4, 1);
lean_inc(x_443);
x_444 = lean_array_get_size(x_443);
x_445 = lean_nat_dec_lt(x_2, x_444);
lean_dec(x_444);
x_446 = lean_ctor_get(x_4, 4);
lean_inc(x_446);
x_447 = l_Array_append___rarg(x_440, x_446);
x_448 = lean_ctor_get(x_1, 4);
lean_inc(x_448);
x_449 = lean_array_get_size(x_6);
x_450 = l_Array_toSubarray___rarg(x_6, x_448, x_449);
x_451 = l_Array_ofSubarray___rarg(x_450);
x_452 = l_Array_append___rarg(x_447, x_451);
x_453 = lean_ctor_get(x_4, 0);
lean_inc(x_453);
if (x_438 == 0)
{
lean_object* x_499; lean_object* x_500; 
lean_dec(x_435);
x_499 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_500 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_499);
x_454 = x_500;
goto block_498;
}
else
{
lean_object* x_501; 
x_501 = lean_array_fget(x_435, x_437);
lean_dec(x_435);
x_454 = x_501;
goto block_498;
}
block_498:
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_455 = lean_ctor_get(x_454, 0);
lean_inc(x_455);
lean_dec(x_454);
x_456 = lean_ctor_get(x_455, 1);
lean_inc(x_456);
lean_dec(x_455);
x_457 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_456, x_439);
x_458 = l_Lean_Expr_const___override(x_434, x_457);
x_459 = l_Lean_mkAppN(x_458, x_442);
x_460 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_461 = lean_array_push(x_460, x_459);
x_462 = l_Array_append___rarg(x_452, x_461);
if (x_445 == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; uint8_t x_467; uint8_t x_468; lean_object* x_469; 
lean_dec(x_443);
x_463 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_464 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_463);
x_465 = l_Lean_mkAppN(x_464, x_462);
x_466 = 0;
x_467 = 1;
x_468 = 1;
x_469 = l_Lean_Meta_mkForallFVars(x_453, x_465, x_466, x_467, x_468, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_469) == 0)
{
uint8_t x_470; 
x_470 = !lean_is_exclusive(x_469);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; 
x_471 = lean_ctor_get(x_469, 0);
x_472 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_471);
lean_dec(x_471);
lean_dec(x_4);
lean_ctor_set(x_469, 0, x_472);
return x_469;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_473 = lean_ctor_get(x_469, 0);
x_474 = lean_ctor_get(x_469, 1);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_469);
x_475 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_473);
lean_dec(x_473);
lean_dec(x_4);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_474);
return x_476;
}
}
else
{
uint8_t x_477; 
lean_dec(x_4);
lean_dec(x_1);
x_477 = !lean_is_exclusive(x_469);
if (x_477 == 0)
{
return x_469;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; 
x_478 = lean_ctor_get(x_469, 0);
x_479 = lean_ctor_get(x_469, 1);
lean_inc(x_479);
lean_inc(x_478);
lean_dec(x_469);
x_480 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
return x_480;
}
}
}
else
{
lean_object* x_481; lean_object* x_482; uint8_t x_483; uint8_t x_484; uint8_t x_485; lean_object* x_486; 
x_481 = lean_array_fget(x_443, x_2);
lean_dec(x_443);
x_482 = l_Lean_mkAppN(x_481, x_462);
x_483 = 0;
x_484 = 1;
x_485 = 1;
x_486 = l_Lean_Meta_mkForallFVars(x_453, x_482, x_483, x_484, x_485, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_486) == 0)
{
uint8_t x_487; 
x_487 = !lean_is_exclusive(x_486);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; 
x_488 = lean_ctor_get(x_486, 0);
x_489 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_488);
lean_dec(x_488);
lean_dec(x_4);
lean_ctor_set(x_486, 0, x_489);
return x_486;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_490 = lean_ctor_get(x_486, 0);
x_491 = lean_ctor_get(x_486, 1);
lean_inc(x_491);
lean_inc(x_490);
lean_dec(x_486);
x_492 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_490);
lean_dec(x_490);
lean_dec(x_4);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_491);
return x_493;
}
}
else
{
uint8_t x_494; 
lean_dec(x_4);
lean_dec(x_1);
x_494 = !lean_is_exclusive(x_486);
if (x_494 == 0)
{
return x_486;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_486, 0);
x_496 = lean_ctor_get(x_486, 1);
lean_inc(x_496);
lean_inc(x_495);
lean_dec(x_486);
x_497 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_497, 0, x_495);
lean_ctor_set(x_497, 1, x_496);
return x_497;
}
}
}
}
}
case 8:
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
lean_dec(x_7);
lean_dec(x_5);
x_502 = lean_ctor_get(x_3, 0);
lean_inc(x_502);
lean_dec(x_3);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
lean_dec(x_502);
x_504 = lean_ctor_get(x_1, 1);
lean_inc(x_504);
x_505 = lean_array_get_size(x_504);
x_506 = lean_unsigned_to_nat(0u);
x_507 = lean_nat_dec_lt(x_506, x_505);
lean_dec(x_505);
x_508 = lean_box(0);
x_509 = lean_ctor_get(x_4, 2);
lean_inc(x_509);
x_510 = lean_ctor_get(x_4, 3);
lean_inc(x_510);
lean_inc(x_509);
x_511 = l_Array_append___rarg(x_509, x_510);
x_512 = lean_ctor_get(x_4, 1);
lean_inc(x_512);
x_513 = lean_array_get_size(x_512);
x_514 = lean_nat_dec_lt(x_2, x_513);
lean_dec(x_513);
x_515 = lean_ctor_get(x_4, 4);
lean_inc(x_515);
x_516 = l_Array_append___rarg(x_509, x_515);
x_517 = lean_ctor_get(x_1, 4);
lean_inc(x_517);
x_518 = lean_array_get_size(x_6);
x_519 = l_Array_toSubarray___rarg(x_6, x_517, x_518);
x_520 = l_Array_ofSubarray___rarg(x_519);
x_521 = l_Array_append___rarg(x_516, x_520);
x_522 = lean_ctor_get(x_4, 0);
lean_inc(x_522);
if (x_507 == 0)
{
lean_object* x_568; lean_object* x_569; 
lean_dec(x_504);
x_568 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_569 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_568);
x_523 = x_569;
goto block_567;
}
else
{
lean_object* x_570; 
x_570 = lean_array_fget(x_504, x_506);
lean_dec(x_504);
x_523 = x_570;
goto block_567;
}
block_567:
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
lean_dec(x_523);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec(x_524);
x_526 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_525, x_508);
x_527 = l_Lean_Expr_const___override(x_503, x_526);
x_528 = l_Lean_mkAppN(x_527, x_511);
x_529 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_530 = lean_array_push(x_529, x_528);
x_531 = l_Array_append___rarg(x_521, x_530);
if (x_514 == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; uint8_t x_536; uint8_t x_537; lean_object* x_538; 
lean_dec(x_512);
x_532 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_533 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_532);
x_534 = l_Lean_mkAppN(x_533, x_531);
x_535 = 0;
x_536 = 1;
x_537 = 1;
x_538 = l_Lean_Meta_mkForallFVars(x_522, x_534, x_535, x_536, x_537, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_538) == 0)
{
uint8_t x_539; 
x_539 = !lean_is_exclusive(x_538);
if (x_539 == 0)
{
lean_object* x_540; lean_object* x_541; 
x_540 = lean_ctor_get(x_538, 0);
x_541 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_540);
lean_dec(x_540);
lean_dec(x_4);
lean_ctor_set(x_538, 0, x_541);
return x_538;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_542 = lean_ctor_get(x_538, 0);
x_543 = lean_ctor_get(x_538, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_538);
x_544 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_542);
lean_dec(x_542);
lean_dec(x_4);
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
return x_545;
}
}
else
{
uint8_t x_546; 
lean_dec(x_4);
lean_dec(x_1);
x_546 = !lean_is_exclusive(x_538);
if (x_546 == 0)
{
return x_538;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_538, 0);
x_548 = lean_ctor_get(x_538, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_538);
x_549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_548);
return x_549;
}
}
}
else
{
lean_object* x_550; lean_object* x_551; uint8_t x_552; uint8_t x_553; uint8_t x_554; lean_object* x_555; 
x_550 = lean_array_fget(x_512, x_2);
lean_dec(x_512);
x_551 = l_Lean_mkAppN(x_550, x_531);
x_552 = 0;
x_553 = 1;
x_554 = 1;
x_555 = l_Lean_Meta_mkForallFVars(x_522, x_551, x_552, x_553, x_554, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_555) == 0)
{
uint8_t x_556; 
x_556 = !lean_is_exclusive(x_555);
if (x_556 == 0)
{
lean_object* x_557; lean_object* x_558; 
x_557 = lean_ctor_get(x_555, 0);
x_558 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_557);
lean_dec(x_557);
lean_dec(x_4);
lean_ctor_set(x_555, 0, x_558);
return x_555;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_559 = lean_ctor_get(x_555, 0);
x_560 = lean_ctor_get(x_555, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_555);
x_561 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_559);
lean_dec(x_559);
lean_dec(x_4);
x_562 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_562, 0, x_561);
lean_ctor_set(x_562, 1, x_560);
return x_562;
}
}
else
{
uint8_t x_563; 
lean_dec(x_4);
lean_dec(x_1);
x_563 = !lean_is_exclusive(x_555);
if (x_563 == 0)
{
return x_555;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_555, 0);
x_565 = lean_ctor_get(x_555, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_555);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
}
}
}
case 9:
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_7);
lean_dec(x_5);
x_571 = lean_ctor_get(x_3, 0);
lean_inc(x_571);
lean_dec(x_3);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec(x_571);
x_573 = lean_ctor_get(x_1, 1);
lean_inc(x_573);
x_574 = lean_array_get_size(x_573);
x_575 = lean_unsigned_to_nat(0u);
x_576 = lean_nat_dec_lt(x_575, x_574);
lean_dec(x_574);
x_577 = lean_box(0);
x_578 = lean_ctor_get(x_4, 2);
lean_inc(x_578);
x_579 = lean_ctor_get(x_4, 3);
lean_inc(x_579);
lean_inc(x_578);
x_580 = l_Array_append___rarg(x_578, x_579);
x_581 = lean_ctor_get(x_4, 1);
lean_inc(x_581);
x_582 = lean_array_get_size(x_581);
x_583 = lean_nat_dec_lt(x_2, x_582);
lean_dec(x_582);
x_584 = lean_ctor_get(x_4, 4);
lean_inc(x_584);
x_585 = l_Array_append___rarg(x_578, x_584);
x_586 = lean_ctor_get(x_1, 4);
lean_inc(x_586);
x_587 = lean_array_get_size(x_6);
x_588 = l_Array_toSubarray___rarg(x_6, x_586, x_587);
x_589 = l_Array_ofSubarray___rarg(x_588);
x_590 = l_Array_append___rarg(x_585, x_589);
x_591 = lean_ctor_get(x_4, 0);
lean_inc(x_591);
if (x_576 == 0)
{
lean_object* x_637; lean_object* x_638; 
lean_dec(x_573);
x_637 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_638 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_637);
x_592 = x_638;
goto block_636;
}
else
{
lean_object* x_639; 
x_639 = lean_array_fget(x_573, x_575);
lean_dec(x_573);
x_592 = x_639;
goto block_636;
}
block_636:
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
lean_dec(x_592);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
lean_dec(x_593);
x_595 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_594, x_577);
x_596 = l_Lean_Expr_const___override(x_572, x_595);
x_597 = l_Lean_mkAppN(x_596, x_580);
x_598 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_599 = lean_array_push(x_598, x_597);
x_600 = l_Array_append___rarg(x_590, x_599);
if (x_583 == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; uint8_t x_605; uint8_t x_606; lean_object* x_607; 
lean_dec(x_581);
x_601 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_602 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_601);
x_603 = l_Lean_mkAppN(x_602, x_600);
x_604 = 0;
x_605 = 1;
x_606 = 1;
x_607 = l_Lean_Meta_mkForallFVars(x_591, x_603, x_604, x_605, x_606, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_607) == 0)
{
uint8_t x_608; 
x_608 = !lean_is_exclusive(x_607);
if (x_608 == 0)
{
lean_object* x_609; lean_object* x_610; 
x_609 = lean_ctor_get(x_607, 0);
x_610 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_609);
lean_dec(x_609);
lean_dec(x_4);
lean_ctor_set(x_607, 0, x_610);
return x_607;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_607, 0);
x_612 = lean_ctor_get(x_607, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_607);
x_613 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_611);
lean_dec(x_611);
lean_dec(x_4);
x_614 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_612);
return x_614;
}
}
else
{
uint8_t x_615; 
lean_dec(x_4);
lean_dec(x_1);
x_615 = !lean_is_exclusive(x_607);
if (x_615 == 0)
{
return x_607;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_607, 0);
x_617 = lean_ctor_get(x_607, 1);
lean_inc(x_617);
lean_inc(x_616);
lean_dec(x_607);
x_618 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_618, 0, x_616);
lean_ctor_set(x_618, 1, x_617);
return x_618;
}
}
}
else
{
lean_object* x_619; lean_object* x_620; uint8_t x_621; uint8_t x_622; uint8_t x_623; lean_object* x_624; 
x_619 = lean_array_fget(x_581, x_2);
lean_dec(x_581);
x_620 = l_Lean_mkAppN(x_619, x_600);
x_621 = 0;
x_622 = 1;
x_623 = 1;
x_624 = l_Lean_Meta_mkForallFVars(x_591, x_620, x_621, x_622, x_623, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_624) == 0)
{
uint8_t x_625; 
x_625 = !lean_is_exclusive(x_624);
if (x_625 == 0)
{
lean_object* x_626; lean_object* x_627; 
x_626 = lean_ctor_get(x_624, 0);
x_627 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_626);
lean_dec(x_626);
lean_dec(x_4);
lean_ctor_set(x_624, 0, x_627);
return x_624;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_628 = lean_ctor_get(x_624, 0);
x_629 = lean_ctor_get(x_624, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_624);
x_630 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_628);
lean_dec(x_628);
lean_dec(x_4);
x_631 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_629);
return x_631;
}
}
else
{
uint8_t x_632; 
lean_dec(x_4);
lean_dec(x_1);
x_632 = !lean_is_exclusive(x_624);
if (x_632 == 0)
{
return x_624;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_624, 0);
x_634 = lean_ctor_get(x_624, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_624);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
return x_635;
}
}
}
}
}
case 10:
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; uint8_t x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_7);
lean_dec(x_5);
x_640 = lean_ctor_get(x_3, 0);
lean_inc(x_640);
lean_dec(x_3);
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
lean_dec(x_640);
x_642 = lean_ctor_get(x_1, 1);
lean_inc(x_642);
x_643 = lean_array_get_size(x_642);
x_644 = lean_unsigned_to_nat(0u);
x_645 = lean_nat_dec_lt(x_644, x_643);
lean_dec(x_643);
x_646 = lean_box(0);
x_647 = lean_ctor_get(x_4, 2);
lean_inc(x_647);
x_648 = lean_ctor_get(x_4, 3);
lean_inc(x_648);
lean_inc(x_647);
x_649 = l_Array_append___rarg(x_647, x_648);
x_650 = lean_ctor_get(x_4, 1);
lean_inc(x_650);
x_651 = lean_array_get_size(x_650);
x_652 = lean_nat_dec_lt(x_2, x_651);
lean_dec(x_651);
x_653 = lean_ctor_get(x_4, 4);
lean_inc(x_653);
x_654 = l_Array_append___rarg(x_647, x_653);
x_655 = lean_ctor_get(x_1, 4);
lean_inc(x_655);
x_656 = lean_array_get_size(x_6);
x_657 = l_Array_toSubarray___rarg(x_6, x_655, x_656);
x_658 = l_Array_ofSubarray___rarg(x_657);
x_659 = l_Array_append___rarg(x_654, x_658);
x_660 = lean_ctor_get(x_4, 0);
lean_inc(x_660);
if (x_645 == 0)
{
lean_object* x_706; lean_object* x_707; 
lean_dec(x_642);
x_706 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_707 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_706);
x_661 = x_707;
goto block_705;
}
else
{
lean_object* x_708; 
x_708 = lean_array_fget(x_642, x_644);
lean_dec(x_642);
x_661 = x_708;
goto block_705;
}
block_705:
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
lean_dec(x_661);
x_663 = lean_ctor_get(x_662, 1);
lean_inc(x_663);
lean_dec(x_662);
x_664 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_663, x_646);
x_665 = l_Lean_Expr_const___override(x_641, x_664);
x_666 = l_Lean_mkAppN(x_665, x_649);
x_667 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_668 = lean_array_push(x_667, x_666);
x_669 = l_Array_append___rarg(x_659, x_668);
if (x_652 == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; uint8_t x_674; uint8_t x_675; lean_object* x_676; 
lean_dec(x_650);
x_670 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_671 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_670);
x_672 = l_Lean_mkAppN(x_671, x_669);
x_673 = 0;
x_674 = 1;
x_675 = 1;
x_676 = l_Lean_Meta_mkForallFVars(x_660, x_672, x_673, x_674, x_675, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_676) == 0)
{
uint8_t x_677; 
x_677 = !lean_is_exclusive(x_676);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; 
x_678 = lean_ctor_get(x_676, 0);
x_679 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_678);
lean_dec(x_678);
lean_dec(x_4);
lean_ctor_set(x_676, 0, x_679);
return x_676;
}
else
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_680 = lean_ctor_get(x_676, 0);
x_681 = lean_ctor_get(x_676, 1);
lean_inc(x_681);
lean_inc(x_680);
lean_dec(x_676);
x_682 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_680);
lean_dec(x_680);
lean_dec(x_4);
x_683 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_683, 0, x_682);
lean_ctor_set(x_683, 1, x_681);
return x_683;
}
}
else
{
uint8_t x_684; 
lean_dec(x_4);
lean_dec(x_1);
x_684 = !lean_is_exclusive(x_676);
if (x_684 == 0)
{
return x_676;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = lean_ctor_get(x_676, 0);
x_686 = lean_ctor_get(x_676, 1);
lean_inc(x_686);
lean_inc(x_685);
lean_dec(x_676);
x_687 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
return x_687;
}
}
}
else
{
lean_object* x_688; lean_object* x_689; uint8_t x_690; uint8_t x_691; uint8_t x_692; lean_object* x_693; 
x_688 = lean_array_fget(x_650, x_2);
lean_dec(x_650);
x_689 = l_Lean_mkAppN(x_688, x_669);
x_690 = 0;
x_691 = 1;
x_692 = 1;
x_693 = l_Lean_Meta_mkForallFVars(x_660, x_689, x_690, x_691, x_692, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_693) == 0)
{
uint8_t x_694; 
x_694 = !lean_is_exclusive(x_693);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; 
x_695 = lean_ctor_get(x_693, 0);
x_696 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_695);
lean_dec(x_695);
lean_dec(x_4);
lean_ctor_set(x_693, 0, x_696);
return x_693;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_697 = lean_ctor_get(x_693, 0);
x_698 = lean_ctor_get(x_693, 1);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_693);
x_699 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_697);
lean_dec(x_697);
lean_dec(x_4);
x_700 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_698);
return x_700;
}
}
else
{
uint8_t x_701; 
lean_dec(x_4);
lean_dec(x_1);
x_701 = !lean_is_exclusive(x_693);
if (x_701 == 0)
{
return x_693;
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_702 = lean_ctor_get(x_693, 0);
x_703 = lean_ctor_get(x_693, 1);
lean_inc(x_703);
lean_inc(x_702);
lean_dec(x_693);
x_704 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_703);
return x_704;
}
}
}
}
}
default: 
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; uint8_t x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_7);
lean_dec(x_5);
x_709 = lean_ctor_get(x_3, 0);
lean_inc(x_709);
lean_dec(x_3);
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
lean_dec(x_709);
x_711 = lean_ctor_get(x_1, 1);
lean_inc(x_711);
x_712 = lean_array_get_size(x_711);
x_713 = lean_unsigned_to_nat(0u);
x_714 = lean_nat_dec_lt(x_713, x_712);
lean_dec(x_712);
x_715 = lean_box(0);
x_716 = lean_ctor_get(x_4, 2);
lean_inc(x_716);
x_717 = lean_ctor_get(x_4, 3);
lean_inc(x_717);
lean_inc(x_716);
x_718 = l_Array_append___rarg(x_716, x_717);
x_719 = lean_ctor_get(x_4, 1);
lean_inc(x_719);
x_720 = lean_array_get_size(x_719);
x_721 = lean_nat_dec_lt(x_2, x_720);
lean_dec(x_720);
x_722 = lean_ctor_get(x_4, 4);
lean_inc(x_722);
x_723 = l_Array_append___rarg(x_716, x_722);
x_724 = lean_ctor_get(x_1, 4);
lean_inc(x_724);
x_725 = lean_array_get_size(x_6);
x_726 = l_Array_toSubarray___rarg(x_6, x_724, x_725);
x_727 = l_Array_ofSubarray___rarg(x_726);
x_728 = l_Array_append___rarg(x_723, x_727);
x_729 = lean_ctor_get(x_4, 0);
lean_inc(x_729);
if (x_714 == 0)
{
lean_object* x_775; lean_object* x_776; 
lean_dec(x_711);
x_775 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_776 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_775);
x_730 = x_776;
goto block_774;
}
else
{
lean_object* x_777; 
x_777 = lean_array_fget(x_711, x_713);
lean_dec(x_711);
x_730 = x_777;
goto block_774;
}
block_774:
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
lean_dec(x_730);
x_732 = lean_ctor_get(x_731, 1);
lean_inc(x_732);
lean_dec(x_731);
x_733 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_732, x_715);
x_734 = l_Lean_Expr_const___override(x_710, x_733);
x_735 = l_Lean_mkAppN(x_734, x_718);
x_736 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_737 = lean_array_push(x_736, x_735);
x_738 = l_Array_append___rarg(x_728, x_737);
if (x_721 == 0)
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; uint8_t x_742; uint8_t x_743; uint8_t x_744; lean_object* x_745; 
lean_dec(x_719);
x_739 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_740 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_739);
x_741 = l_Lean_mkAppN(x_740, x_738);
x_742 = 0;
x_743 = 1;
x_744 = 1;
x_745 = l_Lean_Meta_mkForallFVars(x_729, x_741, x_742, x_743, x_744, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_745) == 0)
{
uint8_t x_746; 
x_746 = !lean_is_exclusive(x_745);
if (x_746 == 0)
{
lean_object* x_747; lean_object* x_748; 
x_747 = lean_ctor_get(x_745, 0);
x_748 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_747);
lean_dec(x_747);
lean_dec(x_4);
lean_ctor_set(x_745, 0, x_748);
return x_745;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_749 = lean_ctor_get(x_745, 0);
x_750 = lean_ctor_get(x_745, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_745);
x_751 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_749);
lean_dec(x_749);
lean_dec(x_4);
x_752 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_752, 0, x_751);
lean_ctor_set(x_752, 1, x_750);
return x_752;
}
}
else
{
uint8_t x_753; 
lean_dec(x_4);
lean_dec(x_1);
x_753 = !lean_is_exclusive(x_745);
if (x_753 == 0)
{
return x_745;
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_745, 0);
x_755 = lean_ctor_get(x_745, 1);
lean_inc(x_755);
lean_inc(x_754);
lean_dec(x_745);
x_756 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_756, 0, x_754);
lean_ctor_set(x_756, 1, x_755);
return x_756;
}
}
}
else
{
lean_object* x_757; lean_object* x_758; uint8_t x_759; uint8_t x_760; uint8_t x_761; lean_object* x_762; 
x_757 = lean_array_fget(x_719, x_2);
lean_dec(x_719);
x_758 = l_Lean_mkAppN(x_757, x_738);
x_759 = 0;
x_760 = 1;
x_761 = 1;
x_762 = l_Lean_Meta_mkForallFVars(x_729, x_758, x_759, x_760, x_761, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_762) == 0)
{
uint8_t x_763; 
x_763 = !lean_is_exclusive(x_762);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; 
x_764 = lean_ctor_get(x_762, 0);
x_765 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_764);
lean_dec(x_764);
lean_dec(x_4);
lean_ctor_set(x_762, 0, x_765);
return x_762;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_766 = lean_ctor_get(x_762, 0);
x_767 = lean_ctor_get(x_762, 1);
lean_inc(x_767);
lean_inc(x_766);
lean_dec(x_762);
x_768 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_766);
lean_dec(x_766);
lean_dec(x_4);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_767);
return x_769;
}
}
else
{
uint8_t x_770; 
lean_dec(x_4);
lean_dec(x_1);
x_770 = !lean_is_exclusive(x_762);
if (x_770 == 0)
{
return x_762;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_762, 0);
x_772 = lean_ctor_get(x_762, 1);
lean_inc(x_772);
lean_inc(x_771);
lean_dec(x_762);
x_773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set(x_773, 1, x_772);
return x_773;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_rebuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_4, 5);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_10, x_11);
x_13 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1(x_1, x_2, x_3, x_4, x_10, x_14, x_16, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_rebuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_IndPredBelow_mkCtorType_rebuild(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_getLocalDecl(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_LocalDecl_userName(x_8);
lean_dec(x_8);
x_11 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_10, x_4, x_5, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_array_set(x_9, x_10, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_10, x_19);
lean_dec(x_10);
x_5 = lean_box(0);
x_8 = x_16;
x_9 = x_18;
x_10 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_10);
lean_dec(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_22 = l_Lean_mkAppN(x_4, x_7);
x_23 = lean_ctor_get(x_2, 4);
x_24 = lean_array_get_size(x_23);
x_25 = lean_nat_dec_lt(x_3, x_24);
lean_dec(x_24);
x_26 = lean_ctor_get(x_1, 4);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_array_get_size(x_9);
x_28 = l_Array_toSubarray___rarg(x_9, x_26, x_27);
x_29 = l_Array_ofSubarray___rarg(x_28);
x_30 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_31 = lean_array_push(x_30, x_22);
x_32 = l_Array_append___rarg(x_29, x_31);
if (x_25 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
x_33 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_34 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_33);
x_35 = l_Lean_mkAppN(x_34, x_32);
x_36 = 0;
x_37 = 1;
x_38 = 1;
x_39 = l_Lean_Meta_mkForallFVars(x_7, x_35, x_36, x_37, x_38, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_4);
x_42 = l_Lean_Expr_fvarId_x21(x_4);
lean_inc(x_11);
x_43 = l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(x_42, x_11, x_12, x_13, x_14, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Expr_binderInfo(x_4);
lean_dec(x_4);
x_47 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_44, x_46, x_40, x_6, x_11, x_12, x_13, x_14, x_45);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_40);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_56 = lean_array_fget(x_23, x_3);
x_57 = l_Lean_mkAppN(x_56, x_32);
x_58 = 0;
x_59 = 1;
x_60 = 1;
x_61 = l_Lean_Meta_mkForallFVars(x_7, x_57, x_58, x_59, x_60, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_4);
x_64 = l_Lean_Expr_fvarId_x21(x_4);
lean_inc(x_11);
x_65 = l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(x_64, x_11, x_12, x_13, x_14, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Expr_binderInfo(x_4);
lean_dec(x_4);
x_69 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_66, x_68, x_62, x_6, x_11, x_12, x_13, x_14, x_67);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_62);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_65);
if (x_70 == 0)
{
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 0);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_65);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_74 = !lean_is_exclusive(x_61);
if (x_74 == 0)
{
return x_61;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_61, 0);
x_76 = lean_ctor_get(x_61, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_61);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_7, x_13);
x_15 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1(x_1, x_2, x_3, x_4, lean_box(0), x_5, x_6, x_7, x_16, x_18, x_8, x_9, x_10, x_11, x_12);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1___boxed), 12, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_7);
x_14 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_5, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
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
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_name_eq(x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("only trivial inductive applications supported in premises:", 58);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_array_set(x_9, x_10, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_10, x_19);
lean_dec(x_10);
x_4 = lean_box(0);
x_8 = x_16;
x_9 = x_18;
x_10 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_10);
x_22 = l_Lean_Expr_constName_x3f(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l_Lean_indentExpr(x_7);
x_24 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg(x_27, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1___boxed), 2, 1);
lean_closure_set(x_31, 0, x_29);
x_32 = lean_array_get_size(x_30);
x_33 = lean_unsigned_to_nat(0u);
x_34 = l_Array_findIdx_x3f_loop___rarg(x_30, x_31, x_32, x_33, lean_box(0));
lean_dec(x_30);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = l_Lean_indentExpr(x_7);
x_36 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg(x_39, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_7);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
lean_inc(x_6);
lean_inc(x_3);
x_42 = l_Lean_mkAppN(x_3, x_6);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
x_44 = lean_array_get_size(x_43);
x_45 = lean_nat_dec_lt(x_41, x_44);
lean_dec(x_44);
x_46 = lean_ctor_get(x_2, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 4);
lean_inc(x_47);
lean_dec(x_2);
x_48 = l_Array_append___rarg(x_46, x_47);
x_49 = lean_ctor_get(x_1, 4);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_array_get_size(x_9);
x_51 = l_Array_toSubarray___rarg(x_9, x_49, x_50);
x_52 = l_Array_ofSubarray___rarg(x_51);
x_53 = l_Array_append___rarg(x_48, x_52);
x_54 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_55 = lean_array_push(x_54, x_42);
x_56 = l_Array_append___rarg(x_53, x_55);
if (x_45 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; 
lean_dec(x_43);
x_57 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_58 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_57);
x_59 = l_Lean_mkAppN(x_58, x_56);
x_60 = 0;
x_61 = 1;
x_62 = 1;
x_63 = l_Lean_Meta_mkForallFVars(x_6, x_59, x_60, x_61, x_62, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_3);
x_66 = l_Lean_Expr_fvarId_x21(x_3);
lean_inc(x_11);
x_67 = l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(x_66, x_11, x_12, x_13, x_14, x_65);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Expr_binderInfo(x_3);
lean_dec(x_3);
x_71 = lean_apply_1(x_5, x_41);
x_72 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_68, x_70, x_64, x_71, x_11, x_12, x_13, x_14, x_69);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_64);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_67);
if (x_73 == 0)
{
return x_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_63);
if (x_77 == 0)
{
return x_63;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_63, 0);
x_79 = lean_ctor_get(x_63, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_63);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; 
x_81 = lean_array_fget(x_43, x_41);
lean_dec(x_43);
x_82 = l_Lean_mkAppN(x_81, x_56);
x_83 = 0;
x_84 = 1;
x_85 = 1;
x_86 = l_Lean_Meta_mkForallFVars(x_6, x_82, x_83, x_84, x_85, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_3);
x_89 = l_Lean_Expr_fvarId_x21(x_3);
lean_inc(x_11);
x_90 = l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(x_89, x_11, x_12, x_13, x_14, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Expr_binderInfo(x_3);
lean_dec(x_3);
x_94 = lean_apply_1(x_5, x_41);
x_95 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_91, x_93, x_87, x_94, x_11, x_12, x_13, x_14, x_92);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_87);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_96 = !lean_is_exclusive(x_90);
if (x_96 == 0)
{
return x_90;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_90, 0);
x_98 = lean_ctor_get(x_90, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_90);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_100 = !lean_is_exclusive(x_86);
if (x_100 == 0)
{
return x_86;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_86, 0);
x_102 = lean_ctor_get(x_86, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_86);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_6, x_12);
x_14 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
lean_inc(x_6);
x_18 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3(x_1, x_2, x_3, lean_box(0), x_4, x_5, x_6, x_6, x_15, x_17, x_7, x_8, x_9, x_10, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___lambda__1), 11, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_6);
x_13 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_4, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = lean_apply_7(x_2, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
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
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
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
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___boxed), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_push(x_1, x_8);
x_17 = l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(x_2, x_3, x_4, x_5, x_6, x_16, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 6)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_19 = lean_expr_instantiate_rev(x_16, x_6);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(x_3);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___lambda__1___boxed), 15, 7);
lean_closure_set(x_24, 0, x_6);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_17);
x_25 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg(x_15, x_18, x_21, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_expr_instantiate_rev(x_7, x_6);
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
x_35 = 1;
x_36 = l_Lean_Meta_mkLambdaFVars(x_6, x_32, x_34, x_3, x_35, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_5, x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
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
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg___boxed), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_push(x_1, x_8);
x_17 = l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(x_2, x_3, x_4, x_5, x_6, x_16, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_7, sizeof(void*)*3 + 8);
lean_dec(x_7);
x_19 = lean_expr_instantiate_rev(x_16, x_6);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(x_3);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1___boxed), 15, 7);
lean_closure_set(x_24, 0, x_6);
lean_closure_set(x_24, 1, x_1);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_23);
lean_closure_set(x_24, 4, x_4);
lean_closure_set(x_24, 5, x_5);
lean_closure_set(x_24, 6, x_17);
x_25 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg(x_15, x_18, x_21, x_24, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_expr_instantiate_rev(x_7, x_6);
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = 0;
x_35 = 1;
x_36 = l_Lean_Meta_mkForallFVars(x_6, x_32, x_34, x_3, x_35, x_10, x_11, x_12, x_13, x_33);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_5, x_37, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_31);
if (x_44 == 0)
{
return x_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_31, 0);
x_46 = lean_ctor_get(x_31, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_31);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___lambda__1), 9, 3);
lean_closure_set(x_12, 0, x_4);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(x_1, x_2, x_3, x_12, x_7, x_8, x_9, x_10, x_11);
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
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___rarg), 11, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_push(x_1, x_8);
x_17 = l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(x_2, x_3, x_4, x_5, x_6, x_16, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_7) == 8)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_expr_instantiate_rev(x_16, x_6);
lean_dec(x_16);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_expr_instantiate_rev(x_17, x_6);
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_24 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(x_3);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1___boxed), 15, 7);
lean_closure_set(x_28, 0, x_6);
lean_closure_set(x_28, 1, x_1);
lean_closure_set(x_28, 2, x_2);
lean_closure_set(x_28, 3, x_27);
lean_closure_set(x_28, 4, x_4);
lean_closure_set(x_28, 5, x_5);
lean_closure_set(x_28, 6, x_18);
x_29 = l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___rarg(x_15, x_21, x_25, x_28, x_8, x_9, x_10, x_11, x_12, x_13, x_26);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
return x_20;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = lean_ctor_get(x_20, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_20);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_expr_instantiate_rev(x_7, x_6);
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_38, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 0;
x_43 = 1;
x_44 = l_Lean_Meta_mkLambdaFVars(x_6, x_40, x_42, x_3, x_43, x_10, x_11, x_12, x_13, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_5, x_45, x_8, x_9, x_10, x_11, x_12, x_13, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
return x_39;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_39, 0);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_39);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_usize_dec_lt(x_7, x_6);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_uget(x_8, x_7);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_8, x_7, x_19);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_18, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_7, x_24);
x_26 = lean_array_uset(x_20, x_7, x_22);
x_7 = x_25;
x_8 = x_26;
x_15 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_array_set(x_7, x_8, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_8, x_19);
lean_dec(x_8);
x_6 = x_16;
x_7 = x_18;
x_8 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_8);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_7);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_27 = 0;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10(x_1, x_2, x_3, x_4, x_5, x_26, x_27, x_7, x_9, x_10, x_11, x_12, x_13, x_14, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_mkAppN(x_23, x_29);
x_32 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_5, x_31, x_9, x_10, x_11, x_12, x_13, x_14, x_30);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_37; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_22);
if (x_37 == 0)
{
return x_22;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_22, 0);
x_39 = lean_ctor_get(x_22, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_22);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = lean_apply_7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_apply_8(x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg), 9, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__2;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 10);
lean_inc(x_21);
x_22 = lean_nat_dec_eq(x_14, x_15);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_8);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_24 = lean_ctor_get(x_8, 10);
lean_dec(x_24);
x_25 = lean_ctor_get(x_8, 9);
lean_dec(x_25);
x_26 = lean_ctor_get(x_8, 8);
lean_dec(x_26);
x_27 = lean_ctor_get(x_8, 7);
lean_dec(x_27);
x_28 = lean_ctor_get(x_8, 6);
lean_dec(x_28);
x_29 = lean_ctor_get(x_8, 5);
lean_dec(x_29);
x_30 = lean_ctor_get(x_8, 4);
lean_dec(x_30);
x_31 = lean_ctor_get(x_8, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_8, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_8, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_8, 0);
lean_dec(x_34);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_14, x_35);
lean_dec(x_14);
lean_ctor_set(x_8, 3, x_36);
x_37 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
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
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_37);
if (x_42 == 0)
{
return x_37;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_37, 0);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_37);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_14, x_46);
lean_dec(x_14);
x_48 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_48, 0, x_11);
lean_ctor_set(x_48, 1, x_12);
lean_ctor_set(x_48, 2, x_13);
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 4, x_15);
lean_ctor_set(x_48, 5, x_16);
lean_ctor_set(x_48, 6, x_17);
lean_ctor_set(x_48, 7, x_18);
lean_ctor_set(x_48, 8, x_19);
lean_ctor_set(x_48, 9, x_20);
lean_ctor_set(x_48, 10, x_21);
x_49 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_48, x_9, x_10);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_52;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_49, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_56 = x_49;
} else {
 lean_dec_ref(x_49);
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
lean_object* x_58; uint8_t x_59; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_58 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg(x_16, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; lean_object* x_15; 
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
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
switch (lean_obj_tag(x_16)) {
case 5:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_16, x_17);
x_19 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
x_23 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11(x_1, x_2, x_3, x_4, x_5, x_16, x_20, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_23;
}
case 6:
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_25 = l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(x_1, x_2, x_3, x_4, x_5, x_24, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_25;
}
case 7:
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_27 = l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(x_1, x_2, x_3, x_4, x_5, x_26, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_27;
}
case 8:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_29 = l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(x_1, x_2, x_3, x_4, x_5, x_28, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_29;
}
case 10:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_31);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_31, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ptr_addr(x_31);
lean_dec(x_31);
x_36 = lean_ptr_addr(x_33);
x_37 = lean_usize_dec_eq(x_35, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_16);
x_38 = l_Lean_Expr_mdata___override(x_30, x_33);
x_39 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_5, x_38, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
return x_39;
}
else
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_30);
x_40 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_34);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_16);
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
x_41 = !lean_is_exclusive(x_32);
if (x_41 == 0)
{
return x_32;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_32, 0);
x_43 = lean_ctor_get(x_32, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_32);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
case 11:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_16, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_16, 2);
lean_inc(x_47);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_47);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_47, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ptr_addr(x_47);
lean_dec(x_47);
x_52 = lean_ptr_addr(x_49);
x_53 = lean_usize_dec_eq(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_16);
x_54 = l_Lean_Expr_proj___override(x_45, x_46, x_49);
x_55 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_5, x_54, x_7, x_8, x_9, x_10, x_11, x_12, x_50);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_49);
lean_dec(x_46);
lean_dec(x_45);
x_56 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_50);
return x_56;
}
}
else
{
uint8_t x_57; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_16);
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
x_57 = !lean_is_exclusive(x_48);
if (x_57 == 0)
{
return x_48;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
default: 
{
lean_object* x_61; 
x_61 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_61;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Std_HashMap_insert___at_Lean_instantiateExprMVars___spec__3(x_3, x_1, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_14, 0, lean_box(0));
lean_closure_set(x_14, 1, lean_box(0));
lean_closure_set(x_14, 2, x_7);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = lean_apply_8(x_5, lean_box(0), x_14, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_6);
x_19 = l_Std_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_17, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_15);
lean_inc(x_1);
lean_inc(x_6);
x_20 = lean_apply_1(x_1, x_6);
x_21 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1___boxed), 13, 5);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_22);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg), 9, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13(x_4, lean_box(0), x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_18);
lean_dec(x_4);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__2), 3, 2);
lean_closure_set(x_28, 0, x_6);
lean_closure_set(x_28, 1, x_26);
x_29 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_29, 0, x_7);
lean_closure_set(x_29, 1, x_28);
x_30 = lean_apply_8(x_5, lean_box(0), x_29, x_8, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_26);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_26);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_25);
if (x_39 == 0)
{
return x_25;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_25, 0);
x_41 = lean_ctor_get(x_25, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_25);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_ctor_get(x_19, 0);
lean_inc(x_43);
lean_dec(x_19);
lean_ctor_set(x_15, 0, x_43);
return x_15;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_15, 0);
x_45 = lean_ctor_get(x_15, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_15);
lean_inc(x_6);
x_46 = l_Std_HashMapImp_find_x3f___at_Lean_instantiateExprMVars___spec__1(x_44, x_6);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_inc(x_1);
lean_inc(x_6);
x_47 = lean_apply_1(x_1, x_6);
x_48 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_box(x_3);
lean_inc(x_5);
lean_inc(x_4);
x_50 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1___boxed), 13, 5);
lean_closure_set(x_50, 0, x_1);
lean_closure_set(x_50, 1, x_2);
lean_closure_set(x_50, 2, x_49);
lean_closure_set(x_50, 3, x_4);
lean_closure_set(x_50, 4, x_5);
x_51 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg), 9, 2);
lean_closure_set(x_51, 0, x_48);
lean_closure_set(x_51, 1, x_50);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_52 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13(x_4, lean_box(0), x_51, x_7, x_8, x_9, x_10, x_11, x_12, x_45);
lean_dec(x_4);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_53);
x_55 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__2), 3, 2);
lean_closure_set(x_55, 0, x_6);
lean_closure_set(x_55, 1, x_53);
x_56 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_56, 0, x_7);
lean_closure_set(x_56, 1, x_55);
x_57 = lean_apply_8(x_5, lean_box(0), x_56, x_8, x_9, x_10, x_11, x_12, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_53);
x_61 = lean_ctor_get(x_57, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
lean_dec(x_46);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_45);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_15);
if (x_71 == 0)
{
return x_15;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_15, 0);
x_73 = lean_ctor_get(x_15, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_15);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_1(x_2, x_10);
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
}
static lean_object* _init_l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1___boxed), 8, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_box(0);
x_12 = lean_st_ref_get(x_9, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1;
x_15 = lean_st_mk_ref(x_14, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__2;
lean_inc(x_9);
lean_inc(x_16);
x_19 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_2, x_3, x_4, x_11, x_18, x_1, x_16, x_5, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_9, x_21);
lean_dec(x_9);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_16, x_23);
lean_dec(x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_20);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_20);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_9);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_constName_x3f(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_array_get_size(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_findIdx_x3f_loop___rarg(x_13, x_14, x_15, x_16, lean_box(0));
lean_dec(x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_17);
x_20 = lean_st_ref_get(x_7, x_8);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_3, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_23, x_25);
lean_dec(x_23);
x_27 = lean_st_ref_set(x_3, x_26, x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(x_2, x_29, x_3, x_4, x_5, x_6, x_7, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_dec_eq(x_1, x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("only arrows are allowed as premises. Multiple recursive occurrences detected:", 77);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2___boxed), 8, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_st_ref_get(x_6, x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_st_mk_ref(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1;
x_16 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_2);
x_17 = l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1(x_2, x_8, x_15, x_16, x_13, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_6, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_13, x_20);
lean_dec(x_13);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_lt(x_24, x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4(x_22, x_26, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_22);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_22);
x_28 = l_Lean_indentExpr(x_2);
x_29 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__6(x_32, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
return x_33;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
return x_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = lean_ctor_get(x_17, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___lambda__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(x_1, x_2, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10(x_1, x_2, x_16, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11(x_1, x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_inc(x_1);
x_19 = l_Lean_Expr_fvarId_x21(x_1);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_24 = lean_array_push(x_23, x_22);
x_25 = l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___closed__1;
x_26 = lean_array_push(x_25, x_1);
x_27 = lean_array_push(x_26, x_2);
x_28 = lean_array_push(x_27, x_13);
x_29 = l_Array_append___rarg(x_3, x_28);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_5);
lean_ctor_set(x_30, 3, x_6);
lean_ctor_set(x_30, 4, x_7);
lean_ctor_set(x_30, 5, x_8);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_9, x_31);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders), 10, 5);
lean_closure_set(x_33, 0, x_10);
lean_closure_set(x_33, 1, x_11);
lean_closure_set(x_33, 2, x_12);
lean_closure_set(x_33, 3, x_30);
lean_closure_set(x_33, 4, x_32);
x_34 = l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(x_24, x_33, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_24);
return x_34;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_9);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___boxed), 18, 12);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_15);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_5);
lean_closure_set(x_21, 6, x_6);
lean_closure_set(x_21, 7, x_7);
lean_closure_set(x_21, 8, x_8);
lean_closure_set(x_21, 9, x_9);
lean_closure_set(x_21, 10, x_10);
lean_closure_set(x_21, 11, x_11);
x_22 = l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder(x_9, x_12, x_14, x_1, x_13, lean_box(0), x_21, x_16, x_17, x_18, x_19, x_20);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 4);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 5);
lean_inc(x_16);
x_17 = lean_array_get_size(x_14);
x_18 = lean_nat_dec_lt(x_5, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
x_19 = l_Lean_Meta_IndPredBelow_mkCtorType_rebuild(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fget(x_14, x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_20);
x_21 = lean_infer_type(x_20, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_22);
lean_inc(x_1);
x_24 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount(x_1, x_22, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_22);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_4, 5);
lean_dec(x_28);
x_29 = lean_ctor_get(x_4, 4);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 3);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 2);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 1);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 0);
lean_dec(x_33);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_dec(x_24);
x_35 = lean_array_push(x_11, x_20);
lean_ctor_set(x_4, 0, x_35);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_5, x_36);
lean_dec(x_5);
x_5 = x_37;
x_10 = x_34;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_dec(x_24);
x_40 = lean_array_push(x_11, x_20);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_12);
lean_ctor_set(x_41, 2, x_13);
lean_ctor_set(x_41, 3, x_14);
lean_ctor_set(x_41, 4, x_15);
lean_ctor_set(x_41, 5, x_16);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_5, x_42);
lean_dec(x_5);
x_4 = x_41;
x_5 = x_43;
x_10 = x_39;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_24, 1);
lean_inc(x_45);
lean_dec(x_24);
lean_inc(x_22);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_20);
x_46 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2___boxed), 20, 13);
lean_closure_set(x_46, 0, x_20);
lean_closure_set(x_46, 1, x_11);
lean_closure_set(x_46, 2, x_12);
lean_closure_set(x_46, 3, x_13);
lean_closure_set(x_46, 4, x_14);
lean_closure_set(x_46, 5, x_15);
lean_closure_set(x_46, 6, x_16);
lean_closure_set(x_46, 7, x_5);
lean_closure_set(x_46, 8, x_1);
lean_closure_set(x_46, 9, x_2);
lean_closure_set(x_46, 10, x_3);
lean_closure_set(x_46, 11, x_4);
lean_closure_set(x_46, 12, x_22);
x_47 = l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder(x_1, x_4, x_20, x_22, lean_box(0), x_46, x_6, x_7, x_8, x_9, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_24);
if (x_48 == 0)
{
return x_24;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_24, 0);
x_50 = lean_ctor_get(x_24, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_24);
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
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_21);
if (x_52 == 0)
{
return x_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_21, 0);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_21);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___boxed(lean_object** _args) {
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
_start:
{
lean_object* x_19; 
x_19 = l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_9);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2___boxed(lean_object** _args) {
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
lean_object* x_20 = _args[19];
_start:
{
lean_object* x_21; 
x_21 = l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_9, x_10, x_2, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_4, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_4, x_3, x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1___boxed), 8, 2);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_17);
x_19 = 1;
x_20 = lean_box(x_19);
lean_ctor_set(x_12, 1, x_18);
lean_ctor_set(x_12, 0, x_20);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_12);
x_22 = 1;
x_23 = lean_usize_add(x_3, x_22);
x_24 = lean_array_uset(x_14, x_3, x_21);
x_3 = x_23;
x_4 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
lean_inc(x_1);
x_28 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1___boxed), 8, 2);
lean_closure_set(x_28, 0, x_1);
lean_closure_set(x_28, 1, x_27);
x_29 = 1;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_35 = lean_array_uset(x_14, x_3, x_32);
x_3 = x_34;
x_4 = x_35;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_push(x_1, x_5);
x_12 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___rarg(x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_4);
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_apply_6(x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_fget(x_1, x_10);
lean_dec(x_10);
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
lean_inc(x_4);
x_19 = lean_apply_6(x_18, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___rarg___lambda__1), 10, 4);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
x_23 = lean_unbox(x_17);
lean_dec(x_17);
x_24 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_16, x_23, x_20, x_22, x_5, x_6, x_7, x_8, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_16);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_10 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___rarg(x_2, x_3, x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 4);
lean_dec(x_13);
lean_inc(x_5);
x_14 = l_Array_append___rarg(x_12, x_5);
lean_ctor_set(x_1, 4, x_5);
lean_ctor_set(x_1, 0, x_14);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders(x_2, x_3, x_4, x_1, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
x_20 = lean_ctor_get(x_1, 3);
x_21 = lean_ctor_get(x_1, 5);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
lean_inc(x_5);
x_22 = l_Array_append___rarg(x_17, x_5);
x_23 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_5);
lean_ctor_set(x_23, 5, x_21);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders(x_2, x_3, x_4, x_23, x_24, x_6, x_7, x_8, x_9, x_10);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_4);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1(x_4, x_12, x_13, x_10, x_5, x_6, x_7, x_8, x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___lambda__1), 10, 4);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
x_18 = l_Lean_instInhabitedExpr;
x_19 = l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2___rarg(x_18, x_15, x_17, x_5, x_6, x_7, x_8, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_16 = lean_array_fget(x_2, x_4);
x_17 = lean_ctor_get(x_1, 2);
x_18 = lean_array_get_size(x_17);
x_19 = lean_nat_dec_lt(x_4, x_18);
lean_dec(x_18);
x_20 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1___boxed), 7, 1);
lean_closure_set(x_20, 0, x_16);
if (x_19 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_22 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_25 = lean_array_push(x_6, x_23);
x_3 = x_15;
x_4 = x_24;
x_5 = lean_box(0);
x_6 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_array_fget(x_17, x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_30 = lean_array_push(x_6, x_28);
x_3 = x_15;
x_4 = x_29;
x_5 = lean_box(0);
x_6 = x_30;
goto _start;
}
}
else
{
lean_object* x_32; 
lean_dec(x_4);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_11);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = !lean_is_exclusive(x_5);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_5, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_5);
x_15 = lean_array_uset(x_7, x_2, x_14);
x_2 = x_9;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_5, 0);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_5);
x_19 = 0;
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_array_uset(x_7, x_2, x_22);
x_2 = x_9;
x_3 = x_23;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3(x_10, x_11, x_2);
x_13 = l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_5);
x_13 = l_Lean_Meta_IndPredBelow_mkCtorType_addMotives(x_2, x_3, x_4, x_1, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_ctor_get(x_1, 5);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 2, x_15);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_18);
x_20 = l_Lean_Meta_IndPredBelow_mkCtorType_addMotives(x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1(x_1, x_10, x_11, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___lambda__1), 10, 4);
lean_closure_set(x_17, 0, x_4);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_3);
x_18 = l_Lean_instInhabitedExpr;
x_19 = l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2___rarg(x_18, x_15, x_17, x_5, x_6, x_7, x_8, x_16);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
lean_inc(x_4);
x_13 = l_Array_toSubarray___rarg(x_4, x_12, x_11);
x_14 = l_Array_ofSubarray___rarg(x_13);
x_15 = lean_array_get_size(x_4);
x_16 = l_Array_toSubarray___rarg(x_4, x_11, x_15);
x_17 = l_Array_ofSubarray___rarg(x_16);
x_18 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
lean_inc(x_14);
x_19 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_17);
lean_ctor_set(x_19, 4, x_18);
lean_ctor_set(x_19, 5, x_5);
x_20 = l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars(x_1, x_2, x_3, x_19, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkCtorType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType___lambda__1), 10, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
x_12 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkConstructor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_3);
x_9 = l_Lean_getConstInfoCtor___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure___spec__1(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_2, x_13);
lean_dec(x_13);
lean_inc(x_2);
x_15 = l_Lean_Meta_IndPredBelow_mkCtorType(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_11);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_2);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_19 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_18);
x_20 = l_Lean_Name_updatePrefix(x_3, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_15);
x_24 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_25 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_24);
x_26 = l_Lean_Name_updatePrefix(x_3, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_22);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_array_fget(x_12, x_2);
lean_dec(x_2);
lean_dec(x_12);
x_36 = l_Lean_Name_updatePrefix(x_3, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_15, 0, x_37);
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
x_40 = lean_array_fget(x_12, x_2);
lean_dec(x_2);
lean_dec(x_12);
x_41 = l_Lean_Name_updatePrefix(x_3, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_9);
if (x_48 == 0)
{
return x_9;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_9, 0);
x_50 = lean_ctor_get(x_9, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_9);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkInductiveType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Lean_Meta_IndPredBelow_mkConstructor(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkInductiveType___spec__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_3, 1, x_19);
lean_ctor_set(x_3, 0, x_15);
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
lean_ctor_set(x_3, 0, x_15);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_3);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_15);
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
lean_free_object(x_3);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_3, 0);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_33 = l_Lean_Meta_IndPredBelow_mkConstructor(x_1, x_2, x_31, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkInductiveType___spec__1(x_1, x_2, x_32, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
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
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = lean_ctor_get(x_33, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_48 = x_33;
} else {
 lean_dec_ref(x_33);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkInductiveType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 4);
lean_inc(x_9);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkInductiveType___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_2, x_14);
lean_dec(x_14);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_array_get_size(x_16);
x_18 = lean_nat_dec_lt(x_2, x_17);
lean_dec(x_17);
if (x_15 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_19 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_20 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_19);
if (x_18 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_2);
x_21 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_19);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_12);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_array_fget(x_16, x_2);
lean_dec(x_2);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_12);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
}
else
{
lean_object* x_25; 
x_25 = lean_array_fget(x_13, x_2);
lean_dec(x_13);
if (x_18 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
lean_dec(x_2);
x_26 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_27 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_12);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_array_fget(x_16, x_2);
lean_dec(x_2);
lean_dec(x_16);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_12);
lean_ctor_set(x_10, 0, x_30);
return x_10;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_array_get_size(x_33);
x_35 = lean_nat_dec_lt(x_2, x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_array_get_size(x_36);
x_38 = lean_nat_dec_lt(x_2, x_37);
lean_dec(x_37);
if (x_35 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_33);
x_39 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_40 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_39);
if (x_38 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_36);
lean_dec(x_2);
x_41 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_39);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_42, 2, x_31);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_array_fget(x_36, x_2);
lean_dec(x_2);
lean_dec(x_36);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_31);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_32);
return x_46;
}
}
else
{
lean_object* x_47; 
x_47 = lean_array_fget(x_33, x_2);
lean_dec(x_33);
if (x_38 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_36);
lean_dec(x_2);
x_48 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_49 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_48);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_31);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_32);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_array_fget(x_36, x_2);
lean_dec(x_2);
lean_dec(x_36);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_31);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_32);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_10);
if (x_55 == 0)
{
return x_10;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_10, 0);
x_57 = lean_ctor_get(x_10, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_10);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_16 = lean_array_fget(x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_1);
x_17 = l_Lean_Meta_IndPredBelow_mkInductiveType(x_1, x_4, x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_21 = lean_array_push(x_6, x_18);
x_3 = x_15;
x_4 = x_20;
x_5 = lean_box(0);
x_6 = x_21;
x_11 = x_19;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
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
lean_object* x_27; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
x_11 = lean_mk_empty_array_with_capacity(x_8);
lean_inc(x_1);
x_12 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1(x_1, x_7, x_8, x_9, lean_box(0), x_11, x_2, x_3, x_4, x_5, x_6);
if (x_10 == 0)
{
lean_dec(x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_16 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_array_get_size(x_20);
lean_dec(x_20);
x_22 = lean_nat_add(x_19, x_21);
lean_dec(x_21);
lean_dec(x_19);
x_23 = lean_array_to_list(lean_box(0), x_14);
x_24 = lean_ctor_get_uint8(x_16, sizeof(void*)*5 + 1);
lean_dec(x_16);
x_25 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*3, x_24);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_29 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_1, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_array_get_size(x_33);
lean_dec(x_33);
x_35 = lean_nat_add(x_32, x_34);
lean_dec(x_34);
lean_dec(x_32);
x_36 = lean_array_to_list(lean_box(0), x_26);
x_37 = lean_ctor_get_uint8(x_29, sizeof(void*)*5 + 1);
lean_dec(x_29);
x_38 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_38, 2, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*3, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_array_fget(x_7, x_9);
lean_dec(x_7);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_1, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_array_get_size(x_50);
lean_dec(x_50);
x_52 = lean_nat_add(x_49, x_51);
lean_dec(x_51);
lean_dec(x_49);
x_53 = lean_array_to_list(lean_box(0), x_45);
x_54 = lean_ctor_get_uint8(x_46, sizeof(void*)*5 + 1);
lean_dec(x_46);
x_55 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*3, x_54);
lean_ctor_set(x_12, 0, x_55);
return x_12;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_array_fget(x_7, x_9);
lean_dec(x_7);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_1, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
lean_dec(x_1);
x_63 = lean_array_get_size(x_62);
lean_dec(x_62);
x_64 = lean_nat_add(x_61, x_63);
lean_dec(x_63);
lean_dec(x_61);
x_65 = lean_array_to_list(lean_box(0), x_56);
x_66 = lean_ctor_get_uint8(x_58, sizeof(void*)*5 + 1);
lean_dec(x_58);
x_67 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_64);
lean_ctor_set(x_67, 2, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*3, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_57);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_7);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_12);
if (x_69 == 0)
{
return x_12;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_12, 0);
x_71 = lean_ctor_get(x_12, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_12);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_uget(x_2, x_3);
x_12 = l_Lean_Expr_mvarId_x21(x_11);
lean_inc(x_12);
x_13 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_12, x_5, x_6, x_7, x_8, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_1, x_17);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_12, x_18, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
return x_29;
}
}
else
{
lean_object* x_30; size_t x_31; size_t x_32; 
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_dec(x_19);
x_31 = 1;
x_32 = lean_usize_add(x_3, x_31);
x_3 = x_32;
x_9 = x_30;
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; size_t x_39; size_t x_40; 
lean_dec(x_12);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_dec(x_13);
x_39 = 1;
x_40 = lean_usize_add(x_3, x_39);
x_3 = x_40;
x_9 = x_38;
goto _start;
}
}
else
{
uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_42 = 0;
x_43 = lean_box(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_9);
return x_44;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_5, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget(x_4, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3(x_1, x_2, x_3, x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_11 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_12 = l_Lean_Meta_forallMetaTelescope(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_isExprDefEq(x_2, x_17, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_18, 0, x_24);
return x_18;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_dec(x_18);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = l_Lean_LocalDecl_toExpr(x_3);
lean_inc(x_16);
x_31 = l_Lean_mkAppN(x_30, x_16);
x_32 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_4, x_31, x_6, x_7, x_8, x_9, x_29);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_32, 1);
x_35 = lean_ctor_get(x_32, 0);
lean_dec(x_35);
x_36 = lean_array_get_size(x_16);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_lt(x_37, x_36);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; 
lean_dec(x_36);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_39 = 1;
x_40 = lean_box(x_39);
lean_ctor_set(x_32, 0, x_40);
return x_32;
}
else
{
uint8_t x_41; 
x_41 = lean_nat_dec_le(x_36, x_36);
if (x_41 == 0)
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_36);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_42 = 1;
x_43 = lean_box(x_42);
lean_ctor_set(x_32, 0, x_43);
return x_32;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
lean_free_object(x_32);
x_44 = 0;
x_45 = lean_usize_of_nat(x_36);
lean_dec(x_36);
x_46 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(x_5, x_16, x_44, x_45, x_6, x_7, x_8, x_9, x_34);
lean_dec(x_16);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
lean_dec(x_50);
x_51 = 1;
x_52 = lean_box(x_51);
lean_ctor_set(x_46, 0, x_52);
return x_46;
}
else
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = 1;
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_46);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_46, 0);
lean_dec(x_58);
x_59 = 0;
x_60 = lean_box(x_59);
lean_ctor_set(x_46, 0, x_60);
return x_46;
}
else
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_46, 1);
lean_inc(x_61);
lean_dec(x_46);
x_62 = 0;
x_63 = lean_box(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_46);
if (x_65 == 0)
{
return x_46;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_46, 0);
x_67 = lean_ctor_get(x_46, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_46);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_32, 1);
lean_inc(x_69);
lean_dec(x_32);
x_70 = lean_array_get_size(x_16);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_lt(x_71, x_70);
if (x_72 == 0)
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = 1;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_69);
return x_75;
}
else
{
uint8_t x_76; 
x_76 = lean_nat_dec_le(x_70, x_70);
if (x_76 == 0)
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_70);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_77 = 1;
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_69);
return x_79;
}
else
{
size_t x_80; size_t x_81; lean_object* x_82; 
x_80 = 0;
x_81 = lean_usize_of_nat(x_70);
lean_dec(x_70);
x_82 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(x_5, x_16, x_80, x_81, x_6, x_7, x_8, x_9, x_69);
lean_dec(x_16);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_86 = x_82;
} else {
 lean_dec_ref(x_82);
 x_86 = lean_box(0);
}
x_87 = 1;
x_88 = lean_box(x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_85);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_91 = x_82;
} else {
 lean_dec_ref(x_82);
 x_91 = lean_box(0);
}
x_92 = 0;
x_93 = lean_box(x_92);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_82, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_82, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_97 = x_82;
} else {
 lean_dec_ref(x_82);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_99 = !lean_is_exclusive(x_18);
if (x_99 == 0)
{
return x_18;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_18, 0);
x_101 = lean_ctor_get(x_18, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_18);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_12);
if (x_103 == 0)
{
return x_12;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_12, 0);
x_105 = lean_ctor_get(x_12, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_12);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_5, x_6);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_LocalDecl_isAuxDecl(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_LocalDecl_type(x_17);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_20 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1___boxed), 10, 5);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_3);
lean_closure_set(x_20, 2, x_17);
lean_closure_set(x_20, 3, x_1);
lean_closure_set(x_20, 4, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_commitWhen___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___spec__1(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_5, x_25);
x_5 = x_26;
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = 1;
x_31 = lean_box(x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
size_t x_40; size_t x_41; 
lean_dec(x_17);
x_40 = 1;
x_41 = lean_usize_add(x_5, x_40);
x_5 = x_41;
goto _start;
}
}
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_11, x_11);
if (x_17 == 0)
{
uint8_t x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_23 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4(x_1, x_2, x_3, x_10, x_21, x_22, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_10);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec(x_4);
x_25 = lean_array_get_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_9);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_25, x_25);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = 0;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_37 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5(x_1, x_2, x_3, x_24, x_35, x_36, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_24);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_5, x_6);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = l_Lean_LocalDecl_isAuxDecl(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l_Lean_LocalDecl_type(x_17);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_20 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1___boxed), 10, 5);
lean_closure_set(x_20, 0, x_19);
lean_closure_set(x_20, 1, x_3);
lean_closure_set(x_20, 2, x_17);
lean_closure_set(x_20, 3, x_1);
lean_closure_set(x_20, 4, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_commitWhen___at___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___spec__1(x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = 1;
x_26 = lean_usize_add(x_5, x_25);
x_5 = x_26;
x_11 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
x_30 = 1;
x_31 = lean_box(x_30);
lean_ctor_set(x_21, 0, x_31);
return x_21;
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
size_t x_40; size_t x_41; 
lean_dec(x_17);
x_40 = 1;
x_41 = lean_usize_add(x_5, x_40);
x_5 = x_41;
goto _start;
}
}
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_11);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_21 = 0;
x_22 = lean_box(x_21);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_18, x_18);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = 0;
x_25 = lean_box(x_24);
lean_ctor_set(x_11, 0, x_25);
return x_11;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_11);
x_26 = 0;
x_27 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_28 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6(x_1, x_2, x_3, x_17, x_26, x_27, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_17);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_dec(x_11);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_dec(x_4);
x_31 = lean_array_get_size(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_31, x_31);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = 0;
x_39 = lean_box(x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_29);
return x_40;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_43 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6(x_1, x_2, x_3, x_30, x_41, x_42, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_30);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_8);
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
lean_object* x_45; 
x_45 = lean_ctor_get(x_11, 0);
lean_dec(x_45);
return x_11;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_11, 1);
lean_inc(x_46);
lean_dec(x_11);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_11);
if (x_48 == 0)
{
return x_11;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_11, 0);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_11);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_1);
x_9 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2(x_1, x_2, x_10, x_12, x_3, x_4, x_5, x_6, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_13 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_14 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = 0;
x_12 = 1;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_introNCore(x_3, x_9, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_array_get_size(x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
x_20 = l_Lean_Meta_introNCore(x_17, x_19, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_2, 2);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_26 = l_Lean_Meta_introNCore(x_24, x_25, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_31 = l_Lean_Meta_intro1Core(x_30, x_12, x_4, x_5, x_6, x_7, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Lean_Meta_introNCore(x_35, x_19, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_33);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_16);
lean_ctor_set(x_42, 1, x_23);
lean_ctor_set(x_42, 2, x_29);
lean_ctor_set(x_42, 3, x_34);
lean_ctor_set(x_42, 4, x_40);
lean_ctor_set(x_38, 1, x_42);
lean_ctor_set(x_38, 0, x_41);
return x_36;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_16);
lean_ctor_set(x_45, 1, x_23);
lean_ctor_set(x_45, 2, x_29);
lean_ctor_set(x_45, 3, x_34);
lean_ctor_set(x_45, 4, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_36, 0, x_46);
return x_36;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_51 = x_47;
} else {
 lean_dec_ref(x_47);
 x_51 = lean_box(0);
}
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_16);
lean_ctor_set(x_52, 1, x_23);
lean_ctor_set(x_52, 2, x_29);
lean_ctor_set(x_52, 3, x_34);
lean_ctor_set(x_52, 4, x_49);
if (lean_is_scalar(x_51)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_51;
}
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_34);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_16);
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
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
else
{
uint8_t x_63; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_20);
if (x_67 == 0)
{
return x_20;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_20, 0);
x_69 = lean_ctor_get(x_20, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_20);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_71 = !lean_is_exclusive(x_13);
if (x_71 == 0)
{
return x_13;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_13, 0);
x_73 = lean_ctor_get(x_13, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_13);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_proveBrecOn_intros(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = l_Lean_Expr_fvar___override(x_14);
x_16 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_17 = l_Lean_MVarId_apply(x_1, x_15, x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_17, 0);
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_17);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
}
else
{
lean_object* x_31; size_t x_32; size_t x_33; 
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_dec(x_17);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
lean_inc(x_2);
{
size_t _tmp_4 = x_33;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_31;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cannot apply induction hypothesis: ", 35);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_2, 4);
x_20 = lean_box(0);
x_21 = lean_array_get_size(x_19);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1(x_1, x_24, x_19, x_22, x_23, x_24, x_3, x_4, x_5, x_6, x_7);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_8 = x_20;
x_9 = x_28;
goto block_18;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_8 = x_30;
x_9 = x_29;
goto block_18;
}
block_18:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
x_13 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at_Lean_Meta_Split_applyMatchSplitter___spec__1(x_14, x_3, x_4, x_5, x_6, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_2, x_14);
lean_dec(x_14);
x_16 = l_Array_append___rarg(x_3, x_4);
lean_inc(x_6);
x_17 = l_Array_append___rarg(x_16, x_6);
if (x_15 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_18 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_19 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_5);
x_21 = l_Lean_mkAppN(x_20, x_17);
x_22 = 0;
x_23 = 1;
x_24 = 1;
x_25 = l_Lean_Meta_mkLambdaFVars(x_6, x_21, x_22, x_23, x_24, x_8, x_9, x_10, x_11, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_26 = lean_array_fget(x_13, x_2);
x_27 = l_Lean_Expr_const___override(x_26, x_5);
x_28 = l_Lean_mkAppN(x_27, x_17);
x_29 = 0;
x_30 = 1;
x_31 = 1;
x_32 = l_Lean_Meta_mkLambdaFVars(x_6, x_28, x_29, x_30, x_31, x_8, x_9, x_10, x_11, x_12);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_6, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_6, x_17);
lean_dec(x_6);
x_19 = lean_array_fget(x_5, x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_15, x_20, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_7);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1___boxed), 12, 5);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_7);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_3);
lean_closure_set(x_24, 4, x_4);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_25 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_22, x_24, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_29 = lean_array_push(x_9, x_26);
x_6 = x_18;
x_7 = x_28;
x_8 = lean_box(0);
x_9 = x_29;
x_14 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_9);
lean_ctor_set(x_39, 1, x_14);
return x_39;
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("rec", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_12, x_13, x_10);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_array_get_size(x_15);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_17, x_13, x_15);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_20, x_21);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_array_get_size(x_23);
x_25 = lean_mk_empty_array_with_capacity(x_24);
x_26 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
lean_inc(x_14);
x_27 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1(x_1, x_14, x_18, x_22, x_23, x_24, x_26, lean_box(0), x_25, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1;
x_32 = l_Lean_Name_str___override(x_30, x_31);
x_33 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_32, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_List_lengthTRAux___rarg(x_22, x_26);
x_37 = l_Lean_ConstantInfo_numLevelParams(x_34);
x_38 = lean_nat_dec_lt(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
x_39 = l_Lean_ConstantInfo_name(x_34);
lean_dec(x_34);
x_40 = l_Array_append___rarg(x_14, x_28);
if (x_38 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_41 = l_Lean_Expr_const___override(x_39, x_22);
x_42 = l_Lean_mkAppN(x_41, x_40);
x_43 = 0;
x_44 = l_Lean_MVarId_apply(x_3, x_42, x_43, x_5, x_6, x_7, x_8, x_35);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_45 = l_Lean_levelZero;
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_22);
x_47 = l_Lean_Expr_const___override(x_39, x_46);
x_48 = l_Lean_mkAppN(x_47, x_40);
x_49 = 0;
x_50 = l_Lean_MVarId_apply(x_3, x_48, x_49, x_5, x_6, x_7, x_8, x_35);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_33);
if (x_51 == 0)
{
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_33, 0);
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_33);
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
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_27);
if (x_55 == 0)
{
return x_27;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_27, 0);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_27);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_introNPRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_isForall(x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_7, 0, x_1);
return x_7;
}
else
{
uint8_t x_12; lean_object* x_13; 
lean_free_object(x_7);
x_12 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Meta_intro1Core(x_1, x_12, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_1 = x_16;
x_6 = x_15;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = l_Lean_Expr_isForall(x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
else
{
uint8_t x_26; lean_object* x_27; 
x_26 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_27 = l_Lean_Meta_intro1Core(x_1, x_26, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_1 = x_30;
x_6 = x_29;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_34 = x_27;
} else {
 lean_dec_ref(x_27);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_set(x_4, x_5, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_3 = x_11;
x_4 = x_13;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_4);
x_17 = l_Lean_Expr_constName_x21(x_3);
lean_dec(x_3);
x_18 = l_Lean_Expr_constName_x21(x_2);
x_19 = l_Lean_Name_updatePrefix(x_17, x_18);
x_20 = l_Lean_Expr_constLevels_x21(x_2);
lean_inc(x_19);
x_21 = l_Lean_Expr_const___override(x_19, x_20);
x_22 = l_Lean_getConstInfoCtor___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure___spec__1(x_19, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
lean_dec(x_25);
x_27 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_28 = l_Lean_Meta_forallMetaTelescope(x_26, x_27, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkAppN(x_21, x_31);
x_33 = 0;
x_34 = l_Lean_MVarId_apply(x_1, x_32, x_33, x_6, x_7, x_8, x_9, x_30);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
else
{
uint8_t x_39; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_array_set(x_3, x_4, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_2 = x_10;
x_3 = x_12;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_16 = l_Lean_instInhabitedExpr;
x_17 = l_Array_back___rarg(x_16, x_3);
lean_dec(x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_17, x_18);
x_20 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_19);
x_21 = lean_mk_array(x_19, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_19, x_22);
lean_dec(x_19);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1), 10, 5);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_2);
lean_closure_set(x_24, 2, x_17);
lean_closure_set(x_24, 3, x_21);
lean_closure_set(x_24, 4, x_23);
x_25 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_24, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_16 = lean_array_fget(x_2, x_4);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Meta_IndPredBelow_proveBrecOn_introNPRec(x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
x_20 = l_Lean_MVarId_getType(x_18, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_21, x_12);
x_24 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_23);
x_25 = lean_mk_array(x_23, x_24);
x_26 = lean_nat_sub(x_23, x_14);
lean_dec(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__2(x_18, x_21, x_25, x_26, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_31 = lean_array_push(x_6, x_28);
x_3 = x_15;
x_4 = x_30;
x_5 = lean_box(0);
x_6 = x_31;
x_11 = x_29;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
else
{
uint8_t x_37; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
else
{
lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_6);
lean_ctor_set(x_45, 1, x_11);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = lean_usize_sub(x_2, x_6);
x_8 = lean_array_uget(x_1, x_7);
x_9 = l_List_appendTR___rarg(x_8, x_4);
x_2 = x_7;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = l_List_redLength___rarg(x_1);
x_8 = lean_mk_empty_array_with_capacity(x_7);
lean_dec(x_7);
lean_inc(x_1);
x_9 = l_List_toArrayAux___rarg(x_1, x_8);
x_10 = lean_array_get_size(x_9);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3(x_1, x_9, x_10, x_12, lean_box(0), x_11, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(0);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_12, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_20 = 0;
x_21 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4(x_15, x_19, x_20, x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_box(0);
x_25 = lean_array_get_size(x_22);
x_26 = lean_nat_dec_lt(x_12, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_25);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_29 = 0;
x_30 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4(x_22, x_28, x_29, x_24);
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
return x_31;
}
}
}
else
{
uint8_t x_32; 
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
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("couldn't solve by backwards chaining (", 38);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__4;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IndPredBelow", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__6;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__8;
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__9;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__2;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__10;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" = ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__11;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__13;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("): ", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_8 = l_Lean_MVarId_isAssigned___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_IndPredBelow_proveBrecOn_introNPRec(x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_13);
x_15 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_13, x_1, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Nat_repr(x_1);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__14;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__16;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_13);
x_26 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_26, 0, x_13);
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1___boxed), 6, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_13, x_30, x_3, x_4, x_5, x_6, x_18);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_15, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_15, 0, x_34);
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_15);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_15, 0);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_15);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_12);
if (x_42 == 0)
{
return x_12;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_12, 0);
x_44 = lean_ctor_get(x_12, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_12);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_8, 0);
lean_dec(x_47);
x_48 = lean_box(0);
lean_ctor_set(x_8, 0, x_48);
return x_8;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_dec(x_8);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_7 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("applying the induction hypothesis should only return one goal", 61);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_box(0);
lean_inc(x_4);
x_10 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_3, x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_11);
x_13 = l_Lean_Expr_mvarId_x21(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_14 = l_Lean_Meta_IndPredBelow_proveBrecOn_intros(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH(x_17, x_18, x_4, x_5, x_6, x_7, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2;
x_23 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_22, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_27 = l_Lean_Meta_IndPredBelow_proveBrecOn_induction(x_1, x_2, x_26, x_18, x_4, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors(x_28, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_6, 2);
lean_inc(x_33);
x_34 = l_Lean_Meta_IndPredBelow_proveBrecOn___closed__3;
x_35 = l_Lean_Option_get___at_Std_Format_pretty_x27___spec__1(x_33, x_34);
lean_dec(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1(x_35, x_31, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_11, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
return x_36;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_36, 0);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_dec(x_19);
x_52 = l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2;
x_53 = l_Lean_throwError___at_Lean_Meta_abstractRange___spec__1(x_52, x_4, x_5, x_6, x_7, x_51);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_19);
if (x_54 == 0)
{
return x_19;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_19, 0);
x_56 = lean_ctor_get(x_19, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_19);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_14);
if (x_58 == 0)
{
return x_14;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_14, 0);
x_60 = lean_ctor_get(x_14, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_14);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_2, x_13);
lean_dec(x_13);
x_15 = lean_box(0);
lean_inc(x_4);
x_16 = l_Array_append___rarg(x_3, x_4);
lean_inc(x_5);
x_17 = l_Array_append___rarg(x_16, x_5);
x_18 = lean_ctor_get(x_1, 2);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_2, x_19);
lean_dec(x_19);
x_21 = lean_array_get_size(x_4);
x_22 = lean_nat_dec_lt(x_2, x_21);
lean_dec(x_21);
if (x_14 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_73 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_72);
x_23 = x_73;
goto block_71;
}
else
{
lean_object* x_74; 
x_74 = lean_array_fget(x_12, x_2);
x_23 = x_74;
goto block_71;
}
block_71:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_List_mapTRAux___at_Lean_mkConstWithLevelParams___spec__1(x_25, x_15);
if (x_20 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_28 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_27);
x_29 = l_Lean_Expr_const___override(x_28, x_26);
x_30 = l_Lean_mkAppN(x_29, x_17);
if (x_22 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; 
lean_dec(x_4);
x_31 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_27);
lean_inc(x_5);
x_32 = l_Lean_mkAppN(x_31, x_5);
x_33 = l_Lean_Meta_mkArrow(x_30, x_32, x_7, x_8, x_9, x_10, x_11);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = 0;
x_37 = 1;
x_38 = 1;
x_39 = l_Lean_Meta_mkForallFVars(x_5, x_34, x_36, x_37, x_38, x_7, x_8, x_9, x_10, x_35);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; 
x_40 = lean_array_fget(x_4, x_2);
lean_dec(x_4);
lean_inc(x_5);
x_41 = l_Lean_mkAppN(x_40, x_5);
x_42 = l_Lean_Meta_mkArrow(x_30, x_41, x_7, x_8, x_9, x_10, x_11);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = 0;
x_46 = 1;
x_47 = 1;
x_48 = l_Lean_Meta_mkForallFVars(x_5, x_43, x_45, x_46, x_47, x_7, x_8, x_9, x_10, x_44);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_array_fget(x_18, x_2);
x_50 = l_Lean_Expr_const___override(x_49, x_26);
x_51 = l_Lean_mkAppN(x_50, x_17);
if (x_22 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
lean_dec(x_4);
x_52 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_53 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_52);
lean_inc(x_5);
x_54 = l_Lean_mkAppN(x_53, x_5);
x_55 = l_Lean_Meta_mkArrow(x_51, x_54, x_7, x_8, x_9, x_10, x_11);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = 0;
x_59 = 1;
x_60 = 1;
x_61 = l_Lean_Meta_mkForallFVars(x_5, x_56, x_58, x_59, x_60, x_7, x_8, x_9, x_10, x_57);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; 
x_62 = lean_array_fget(x_4, x_2);
lean_dec(x_4);
lean_inc(x_5);
x_63 = l_Lean_mkAppN(x_62, x_5);
x_64 = l_Lean_Meta_mkArrow(x_51, x_63, x_7, x_8, x_9, x_10, x_11);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = 0;
x_68 = 1;
x_69 = 1;
x_70 = l_Lean_Meta_mkForallFVars(x_5, x_65, x_67, x_68, x_69, x_7, x_8, x_9, x_10, x_66);
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1___boxed), 11, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
x_13 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ih", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ih_", 3);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_lt(x_13, x_12);
lean_dec(x_12);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_16, x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2___boxed), 11, 5);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_4);
lean_closure_set(x_20, 2, x_2);
lean_closure_set(x_20, 3, x_3);
lean_closure_set(x_20, 4, x_18);
if (x_14 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_4);
x_21 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2;
x_22 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_21, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
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
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_30 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
x_31 = l_Nat_repr(x_30);
x_32 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3;
x_33 = lean_string_append(x_32, x_31);
lean_dec(x_31);
x_34 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_box(0);
x_37 = l_Lean_Name_str___override(x_36, x_35);
x_38 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_37, x_8, x_9, x_19);
lean_dec(x_9);
lean_dec(x_8);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_20);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_20);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_17);
if (x_46 == 0)
{
return x_17;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_17, 0);
x_48 = lean_ctor_get(x_17, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_17);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_dec(x_5);
x_18 = lean_array_fget(x_4, x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_1);
x_19 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH(x_1, x_3, x_2, x_6, x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_nat_add(x_6, x_16);
lean_dec(x_6);
x_23 = lean_array_push(x_8, x_20);
x_5 = x_17;
x_6 = x_22;
x_7 = lean_box(0);
x_8 = x_23;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
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
lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_13);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = l_Array_append___rarg(x_1, x_5);
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_3, x_12);
lean_dec(x_12);
x_14 = l_Array_ofSubarray___rarg(x_4);
if (x_13 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_15 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_16 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_15);
x_17 = l_Lean_mkAppN(x_16, x_14);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkForallFVars(x_11, x_17, x_18, x_19, x_20, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_22 = lean_array_fget(x_2, x_3);
x_23 = l_Lean_mkAppN(x_22, x_14);
x_24 = 0;
x_25 = 1;
x_26 = 1;
x_27 = l_Lean_Meta_mkForallFVars(x_11, x_23, x_24, x_25, x_26, x_6, x_7, x_8, x_9, x_10);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_10);
lean_inc(x_3);
x_12 = l_Array_toSubarray___rarg(x_3, x_11, x_10);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_add(x_10, x_14);
lean_inc(x_15);
lean_inc(x_3);
x_16 = l_Array_toSubarray___rarg(x_3, x_10, x_15);
x_17 = l_Array_ofSubarray___rarg(x_16);
x_18 = lean_array_get_size(x_3);
lean_inc(x_3);
x_19 = l_Array_toSubarray___rarg(x_3, x_15, x_18);
x_20 = l_Array_ofSubarray___rarg(x_12);
x_21 = lean_mk_empty_array_with_capacity(x_14);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_22 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1(x_1, x_17, x_20, x_13, x_14, x_11, lean_box(0), x_21, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1___boxed), 10, 4);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_17);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_19);
x_26 = l_Lean_instInhabitedExpr;
x_27 = l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2___rarg(x_26, x_23, x_25, x_5, x_6, x_7, x_8, x_24);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_22, 0);
x_30 = lean_ctor_get(x_22, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_22);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_array_get_size(x_8);
x_10 = lean_nat_dec_lt(x_2, x_9);
lean_dec(x_9);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2___boxed), 9, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_2);
x_12 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_13 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_12);
x_14 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_13, x_11, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_fget(x_8, x_2);
lean_dec(x_2);
lean_dec(x_8);
x_16 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_15, x_11, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_brecOnSuffix;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_2);
x_14 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_15 = l_panic___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_ctor_get(x_16, 2);
lean_dec(x_20);
x_21 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1;
x_22 = l_Lean_Name_append(x_18, x_21);
lean_dec(x_18);
lean_inc(x_9);
x_23 = l_Lean_Meta_IndPredBelow_proveBrecOn(x_1, x_15, x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_22);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 0, x_22);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
lean_inc(x_22);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 0, x_22);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_22);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_16);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_22);
lean_free_object(x_16);
lean_dec(x_19);
lean_dec(x_9);
x_37 = !lean_is_exclusive(x_23);
if (x_37 == 0)
{
return x_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_16, 0);
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_16);
x_43 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1;
x_44 = l_Lean_Name_append(x_41, x_43);
lean_dec(x_41);
lean_inc(x_9);
x_45 = l_Lean_Meta_IndPredBelow_proveBrecOn(x_1, x_15, x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_48 = x_45;
} else {
 lean_dec_ref(x_45);
 x_48 = lean_box(0);
}
lean_inc(x_44);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_9);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_46);
lean_ctor_set(x_52, 2, x_51);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
if (lean_is_scalar(x_48)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_48;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_9);
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_57 = x_45;
} else {
 lean_dec_ref(x_45);
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
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_array_fget(x_11, x_2);
lean_dec(x_2);
lean_dec(x_11);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_60, 1);
x_64 = lean_ctor_get(x_60, 2);
lean_dec(x_64);
x_65 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1;
x_66 = l_Lean_Name_append(x_62, x_65);
lean_dec(x_62);
lean_inc(x_9);
x_67 = l_Lean_Meta_IndPredBelow_proveBrecOn(x_1, x_59, x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_66);
lean_ctor_set(x_60, 2, x_9);
lean_ctor_set(x_60, 0, x_66);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_69);
lean_ctor_set(x_72, 2, x_71);
x_73 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_67, 0, x_73);
return x_67;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
lean_inc(x_66);
lean_ctor_set(x_60, 2, x_9);
lean_ctor_set(x_60, 0, x_66);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_60);
lean_ctor_set(x_78, 1, x_74);
lean_ctor_set(x_78, 2, x_77);
x_79 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_79, 0, x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_66);
lean_free_object(x_60);
lean_dec(x_63);
lean_dec(x_9);
x_81 = !lean_is_exclusive(x_67);
if (x_81 == 0)
{
return x_67;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_67, 0);
x_83 = lean_ctor_get(x_67, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_67);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_60, 0);
x_86 = lean_ctor_get(x_60, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_60);
x_87 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1;
x_88 = l_Lean_Name_append(x_85, x_87);
lean_dec(x_85);
lean_inc(x_9);
x_89 = l_Lean_Meta_IndPredBelow_proveBrecOn(x_1, x_59, x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
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
lean_inc(x_88);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_86);
lean_ctor_set(x_93, 2, x_9);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_88);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_90);
lean_ctor_set(x_96, 2, x_95);
x_97 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_97, 0, x_96);
if (lean_is_scalar(x_92)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_92;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_91);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_9);
x_99 = lean_ctor_get(x_89, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_89, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_101 = x_89;
} else {
 lean_dec_ref(x_89);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_8);
if (x_103 == 0)
{
return x_8;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_8, 0);
x_105 = lean_ctor_get(x_8, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_8);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
lean_dec(x_1);
x_14 = l_Lean_Meta_IndPredBelow_getBelowIndices_loop(x_2, x_6, x_3, x_4, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_getBelowIndices_loop___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_48; uint8_t x_49; 
x_48 = lean_array_get_size(x_1);
x_49 = lean_nat_dec_le(x_48, x_4);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = lean_nat_dec_lt(x_4, x_48);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_52 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_51);
x_11 = x_52;
goto block_47;
}
else
{
lean_object* x_53; 
x_53 = lean_array_fget(x_1, x_4);
x_11 = x_53;
goto block_47;
}
}
else
{
lean_object* x_54; 
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_10);
return x_54;
}
block_47:
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_11);
x_12 = lean_infer_type(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_bindingDomain_x21(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_isExprDefEq(x_13, x_15, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1), 11, 4);
lean_closure_set(x_20, 0, x_5);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
x_21 = l_Lean_Meta_IndPredBelow_getBelowIndices_loop___closed__1;
x_22 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(x_2, x_21, x_20, x_6, x_7, x_8, x_9, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_25 = lean_array_push(x_24, x_11);
x_26 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_25, x_26, x_2, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_5);
x_30 = lean_array_push(x_3, x_5);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_4, x_31);
lean_dec(x_4);
x_33 = lean_nat_add(x_5, x_31);
lean_dec(x_5);
x_2 = x_28;
x_3 = x_30;
x_4 = x_32;
x_5 = x_33;
x_10 = x_29;
goto _start;
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_27);
if (x_35 == 0)
{
return x_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 0);
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_12);
if (x_43 == 0)
{
return x_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Meta_IndPredBelow_getBelowIndices_loop(x_2, x_10, x_11, x_12, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfoCtor___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
x_12 = l_Lean_Name_append(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_Name_updatePrefix(x_1, x_12);
x_14 = l_Lean_getConstInfoCtor___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure___spec__1(x_13, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1___boxed), 8, 1);
lean_closure_set(x_19, 0, x_15);
x_20 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_18, x_19, x_2, x_3, x_4, x_5, x_16);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_array_set(x_4, x_5, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_5, x_14);
lean_dec(x_5);
x_3 = x_11;
x_4 = x_13;
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = l_Lean_Expr_constName_x21(x_3);
lean_inc(x_17);
x_18 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_21);
lean_inc(x_4);
x_23 = l_Array_toSubarray___rarg(x_4, x_22, x_21);
x_24 = l_Array_ofSubarray___rarg(x_23);
x_25 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_26 = lean_array_push(x_25, x_1);
x_27 = l_Array_append___rarg(x_24, x_26);
x_28 = lean_array_get_size(x_4);
x_29 = l_Array_toSubarray___rarg(x_4, x_21, x_28);
x_30 = l_Array_ofSubarray___rarg(x_29);
x_31 = l_Array_append___rarg(x_27, x_30);
x_32 = lean_array_push(x_25, x_2);
x_33 = l_Array_append___rarg(x_31, x_32);
x_34 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
x_35 = l_Lean_Name_append(x_17, x_34);
x_36 = l_Lean_Expr_constLevels_x21(x_3);
x_37 = l_Lean_Expr_const___override(x_35, x_36);
x_38 = l_Lean_mkAppN(x_37, x_33);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_17);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_18, 0, x_39);
return x_18;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unsigned_to_nat(0u);
lean_inc(x_42);
lean_inc(x_4);
x_44 = l_Array_toSubarray___rarg(x_4, x_43, x_42);
x_45 = l_Array_ofSubarray___rarg(x_44);
x_46 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_47 = lean_array_push(x_46, x_1);
x_48 = l_Array_append___rarg(x_45, x_47);
x_49 = lean_array_get_size(x_4);
x_50 = l_Array_toSubarray___rarg(x_4, x_42, x_49);
x_51 = l_Array_ofSubarray___rarg(x_50);
x_52 = l_Array_append___rarg(x_48, x_51);
x_53 = lean_array_push(x_46, x_2);
x_54 = l_Array_append___rarg(x_52, x_53);
x_55 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
x_56 = l_Lean_Name_append(x_17, x_55);
x_57 = l_Lean_Expr_constLevels_x21(x_3);
x_58 = l_Lean_Expr_const___override(x_56, x_57);
x_59 = l_Lean_mkAppN(x_58, x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_17);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_41);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_18);
if (x_62 == 0)
{
return x_18;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_18, 0);
x_64 = lean_ctor_get(x_18, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_18);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_25; uint8_t x_26; 
x_25 = lean_array_get_size(x_2);
x_26 = lean_nat_dec_lt(x_3, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_28 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_27);
x_9 = x_28;
goto block_24;
}
else
{
lean_object* x_29; 
x_29 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_9 = x_29;
goto block_24;
}
block_24:
{
lean_object* x_10; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_10 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_11, x_13);
x_15 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1(x_1, x_9, x_11, x_16, x_18, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
case 1:
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
}
case 3:
{
uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_17 = 0;
lean_inc(x_1);
x_18 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_17, x_1, x_2, x_3, x_4, x_5, x_6);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 0);
lean_dec(x_20);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_18, 0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_22);
lean_ctor_set(x_18, 0, x_1);
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
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_1);
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_18, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_32 = x_18;
} else {
 lean_dec_ref(x_18);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
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
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
default: 
{
uint8_t x_39; lean_object* x_40; 
x_39 = 0;
x_40 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_39, x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
return x_40;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_nat_sub(x_6, x_9);
lean_dec(x_6);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Match_instInhabitedPattern;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
x_19 = lean_array_get_size(x_1);
x_20 = lean_nat_dec_lt(x_5, x_19);
lean_dec(x_19);
x_21 = lean_nat_dec_lt(x_5, x_3);
if (x_20 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_23 = l_panic___at_Lean_TSyntax_getNat___spec__1(x_22);
if (x_21 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_panic___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_array_set(x_8, x_23, x_25);
lean_dec(x_23);
x_27 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_27;
x_8 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_array_fget(x_2, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_set(x_8, x_23, x_30);
lean_dec(x_23);
x_32 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_32;
x_8 = x_31;
goto _start;
}
}
else
{
lean_object* x_34; 
x_34 = lean_array_fget(x_1, x_5);
if (x_21 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_36 = l_panic___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_array_set(x_8, x_34, x_37);
lean_dec(x_34);
x_39 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_39;
x_8 = x_38;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_array_fget(x_2, x_5);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
x_43 = lean_array_set(x_8, x_34, x_42);
lean_dec(x_34);
x_44 = lean_nat_add(x_5, x_7);
lean_dec(x_5);
x_4 = x_18;
x_5 = x_44;
x_8 = x_43;
goto _start;
}
}
}
else
{
lean_object* x_46; 
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_13);
return x_46;
}
}
else
{
lean_object* x_47; 
lean_dec(x_5);
lean_dec(x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_8);
lean_ctor_set(x_47, 1, x_13);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_2);
x_8 = l_Lean_Meta_getFVarLocalDecl(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_array_push(x_1, x_10);
x_12 = l_Lean_Expr_fvarId_x21(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_array_push(x_1, x_15);
x_18 = l_Lean_Expr_fvarId_x21(x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" ↦ ", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_st_ref_get(x_8, x_9);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 3);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*1);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
x_32 = 0;
x_10 = x_32;
x_11 = x_31;
goto block_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
lean_inc(x_4);
x_34 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_4, x_5, x_6, x_7, x_8, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_unbox(x_35);
lean_dec(x_35);
x_10 = x_37;
x_11 = x_36;
goto block_26;
}
block_26:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2(x_1, x_2, x_12, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_14 = l_Lean_Meta_Match_Pattern_toMessageData(x_3);
x_15 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_2);
x_19 = l_Lean_Meta_Match_Pattern_toMessageData(x_2);
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
x_22 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_21, x_5, x_6, x_7, x_8, x_11);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2(x_1, x_2, x_23, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_23);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("match", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_Expr_fvar___override(x_9);
x_11 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_12 = lean_array_push(x_11, x_10);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_19 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_18, x_6, x_7, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___boxed), 7, 1);
lean_closure_set(x_22, 0, x_11);
x_23 = 0;
x_24 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_20, x_23, x_17, x_22, x_4, x_5, x_6, x_7, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
case 2:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 3);
lean_inc(x_32);
lean_inc(x_29);
x_33 = l_Lean_getConstInfoCtor___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure___spec__1(x_29, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
x_38 = l_Lean_Name_append(x_36, x_37);
lean_dec(x_36);
lean_inc(x_29);
x_39 = l_Lean_Name_updatePrefix(x_29, x_38);
x_40 = l_Lean_getConstInfoCtor___at___private_Lean_Meta_WHNF_0__Lean_Meta_toCtorWhenStructure___spec__1(x_39, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_43 = l_Lean_Meta_IndPredBelow_getBelowIndices(x_29, x_4, x_5, x_6, x_7, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_34, 3);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_array_get_size(x_44);
x_48 = l_Array_toSubarray___rarg(x_44, x_46, x_47);
x_49 = l_Array_ofSubarray___rarg(x_48);
x_50 = lean_array_get_size(x_49);
x_51 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_52 = 0;
x_53 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1(x_41, x_51, x_52, x_49);
x_54 = lean_ctor_get(x_41, 4);
lean_inc(x_54);
x_55 = lean_box(0);
x_56 = lean_mk_array(x_54, x_55);
x_57 = l_List_redLength___rarg(x_32);
x_58 = lean_mk_empty_array_with_capacity(x_57);
lean_dec(x_57);
x_59 = l_List_toArrayAux___rarg(x_32, x_58);
x_60 = lean_array_get_size(x_59);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_unsigned_to_nat(1u);
lean_inc(x_60);
x_63 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3(x_53, x_59, x_60, x_60, x_61, x_60, x_62, x_56, x_4, x_5, x_6, x_7, x_45);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_53);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_List_redLength___rarg(x_31);
x_67 = lean_mk_empty_array_with_capacity(x_66);
lean_dec(x_66);
x_68 = l_List_toArrayAux___rarg(x_31, x_67);
lean_inc(x_1);
x_69 = lean_array_push(x_68, x_1);
x_70 = lean_ctor_get(x_41, 0);
lean_inc(x_70);
lean_dec(x_41);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
lean_inc(x_30);
lean_inc(x_71);
x_72 = l_Lean_Expr_const___override(x_71, x_30);
lean_inc(x_69);
x_73 = l_Lean_mkAppN(x_72, x_69);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_74 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields(x_1, x_73, x_2, x_64, x_4, x_5, x_6, x_7, x_65);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
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
lean_inc(x_77);
x_79 = lean_array_to_list(lean_box(0), x_77);
x_80 = lean_array_to_list(lean_box(0), x_69);
x_81 = lean_array_to_list(lean_box(0), x_78);
x_82 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_82, 0, x_71);
lean_ctor_set(x_82, 1, x_30);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_81);
x_83 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_84 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3), 9, 4);
lean_closure_set(x_84, 0, x_77);
lean_closure_set(x_84, 1, x_82);
lean_closure_set(x_84, 2, x_3);
lean_closure_set(x_84, 3, x_83);
x_85 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_79, x_84, x_4, x_5, x_6, x_7, x_76);
return x_85;
}
else
{
uint8_t x_86; 
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_74);
if (x_86 == 0)
{
return x_74;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_74, 0);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_74);
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
lean_dec(x_41);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_43);
if (x_90 == 0)
{
return x_43;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_43, 0);
x_92 = lean_ctor_get(x_43, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_43);
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
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_40);
if (x_94 == 0)
{
return x_40;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_40, 0);
x_96 = lean_ctor_get(x_40, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_40);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_33);
if (x_98 == 0)
{
return x_33;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_33, 0);
x_100 = lean_ctor_get(x_33, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_33);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
case 5:
{
uint8_t x_102; 
x_102 = !lean_is_exclusive(x_3);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_3, 0);
x_104 = lean_ctor_get(x_3, 1);
x_105 = lean_ctor_get(x_3, 2);
x_106 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_104, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_106) == 0)
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_108, 1);
lean_ctor_set(x_3, 1, x_110);
lean_ctor_set(x_108, 1, x_3);
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_108, 0);
x_112 = lean_ctor_get(x_108, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_108);
lean_ctor_set(x_3, 1, x_112);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_3);
lean_ctor_set(x_106, 0, x_113);
return x_106;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_106, 0);
x_115 = lean_ctor_get(x_106, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_106);
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
lean_ctor_set(x_3, 1, x_117);
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_3);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_115);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_free_object(x_3);
lean_dec(x_105);
lean_dec(x_103);
x_121 = !lean_is_exclusive(x_106);
if (x_121 == 0)
{
return x_106;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_106, 0);
x_123 = lean_ctor_get(x_106, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_106);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_3, 0);
x_126 = lean_ctor_get(x_3, 1);
x_127 = lean_ctor_get(x_3, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_3);
x_128 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_126, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_129, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_134 = x_129;
} else {
 lean_dec_ref(x_129);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set(x_135, 2, x_127);
if (lean_is_scalar(x_134)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_134;
}
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
if (lean_is_scalar(x_131)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_131;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_130);
return x_137;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_127);
lean_dec(x_125);
x_138 = lean_ctor_get(x_128, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_128, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_140 = x_128;
} else {
 lean_dec_ref(x_128);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
default: 
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_142 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_3);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_8);
return x_144;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_11 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop(x_1, x_3, x_2, x_4, x_10, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_array_set(x_11, x_12, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_12, x_21);
lean_dec(x_12);
x_10 = x_18;
x_11 = x_20;
x_12 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
x_24 = l_Lean_Expr_constName_x3f(x_10);
lean_dec(x_10);
lean_inc(x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
x_26 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_803____at_Lean_IR_IRType_beq___spec__1(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
lean_dec(x_6);
x_27 = lean_array_push(x_4, x_7);
x_28 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop(x_1, x_2, x_9, x_3, x_27, x_5, x_13, x_14, x_15, x_16, x_17);
return x_28;
}
else
{
lean_object* x_29; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_7, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
lean_inc(x_32);
x_34 = lean_array_to_list(lean_box(0), x_32);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_nat_add(x_6, x_35);
lean_dec(x_6);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_33);
x_38 = lean_array_set(x_3, x_36, x_37);
lean_dec(x_36);
x_39 = l_Array_append___rarg(x_5, x_32);
if (lean_obj_tag(x_7) == 2)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_7);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_8);
x_41 = lean_array_push(x_4, x_40);
x_42 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop), 11, 6);
lean_closure_set(x_42, 0, x_1);
lean_closure_set(x_42, 1, x_2);
lean_closure_set(x_42, 2, x_9);
lean_closure_set(x_42, 3, x_38);
lean_closure_set(x_42, 4, x_41);
lean_closure_set(x_42, 5, x_39);
x_43 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_34, x_42, x_13, x_14, x_15, x_16, x_31);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
x_44 = lean_array_push(x_4, x_7);
x_45 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop), 11, 6);
lean_closure_set(x_45, 0, x_1);
lean_closure_set(x_45, 1, x_2);
lean_closure_set(x_45, 2, x_9);
lean_closure_set(x_45, 3, x_38);
lean_closure_set(x_45, 4, x_44);
lean_closure_set(x_45, 5, x_39);
x_46 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_34, x_45, x_13, x_14, x_15, x_16, x_31);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_29);
if (x_47 == 0)
{
return x_29;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_29, 0);
x_49 = lean_ctor_get(x_29, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_29);
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
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Lean_Meta_getFVarLocalDecl(x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
x_16 = l_Lean_Expr_app___override(x_1, x_7);
x_17 = l_Lean_Expr_fvarId_x21(x_7);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_array_push(x_2, x_18);
x_20 = lean_array_push(x_3, x_14);
x_21 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop(x_4, x_5, x_16, x_6, x_19, x_20, x_8, x_9, x_10, x_11, x_15);
return x_21;
}
else
{
uint8_t x_22; 
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
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("a", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_56; 
x_29 = lean_array_get_size(x_4);
x_30 = lean_array_get_size(x_5);
x_56 = lean_nat_dec_le(x_29, x_30);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = lean_nat_dec_lt(x_30, x_29);
lean_dec(x_29);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_59 = l_panic___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_dec(x_30);
x_60 = lean_box(0);
x_12 = x_60;
goto block_28;
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_31 = x_61;
goto block_55;
}
}
else
{
lean_object* x_62; 
x_62 = lean_array_fget(x_4, x_30);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; 
lean_dec(x_30);
x_63 = lean_box(0);
x_12 = x_63;
goto block_28;
}
else
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
lean_dec(x_62);
x_31 = x_64;
goto block_55;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_6);
lean_ctor_set(x_65, 1, x_5);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_11);
return x_66;
}
block_28:
{
lean_object* x_13; 
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_13 = lean_infer_type(x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__2;
x_17 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_16, x_9, x_10, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Expr_bindingDomain_x21(x_14);
lean_dec(x_14);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___lambda__1), 12, 6);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_5);
lean_closure_set(x_21, 2, x_6);
lean_closure_set(x_21, 3, x_1);
lean_closure_set(x_21, 4, x_2);
lean_closure_set(x_21, 5, x_4);
x_22 = 0;
x_23 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_18, x_22, x_20, x_21, x_7, x_8, x_9, x_10, x_19);
return x_23;
}
else
{
uint8_t x_24; 
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
block_55:
{
uint8_t x_32; lean_object* x_33; 
x_32 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_31);
x_33 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_32, x_31, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_34);
x_36 = l_Lean_Expr_app___override(x_3, x_34);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_34);
x_37 = lean_infer_type(x_34, x_7, x_8, x_9, x_10, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_38, x_40);
x_42 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_41);
x_43 = lean_mk_array(x_41, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_41, x_44);
lean_dec(x_41);
x_46 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1(x_1, x_2, x_4, x_5, x_6, x_30, x_31, x_34, x_36, x_38, x_43, x_45, x_7, x_8, x_9, x_10, x_39);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_37);
if (x_47 == 0)
{
return x_37;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_37, 0);
x_49 = lean_ctor_get(x_37, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_37);
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
lean_dec(x_31);
lean_dec(x_30);
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
x_51 = !lean_is_exclusive(x_33);
if (x_51 == 0)
{
return x_33;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_33, 0);
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_33);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1___boxed(lean_object** _args) {
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
lean_object* x_18; 
x_18 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_array_set(x_2, x_3, x_14);
x_16 = l_List_appendTR___rarg(x_4, x_5);
x_17 = lean_array_to_list(lean_box(0), x_15);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_array_set(x_2, x_3, x_19);
x_22 = l_List_appendTR___rarg(x_4, x_5);
x_23 = lean_array_to_list(lean_box(0), x_21);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_3, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_19 = lean_array_to_list(lean_box(0), x_17);
x_20 = lean_array_push(x_4, x_18);
lean_inc(x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1___boxed), 11, 6);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_6);
lean_closure_set(x_21, 3, x_7);
lean_closure_set(x_21, 4, x_19);
lean_closure_set(x_21, 5, x_8);
x_22 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_19, x_21, x_9, x_10, x_11, x_12, x_16);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_13 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
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
x_18 = lean_array_to_list(lean_box(0), x_16);
x_19 = lean_array_push(x_4, x_17);
lean_inc(x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1___boxed), 11, 6);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_5);
lean_closure_set(x_20, 3, x_6);
lean_closure_set(x_20, 4, x_18);
lean_closure_set(x_20, 5, x_7);
x_21 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_18, x_20, x_8, x_9, x_10, x_11, x_15);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
lean_dec(x_4);
x_13 = l_List_redLength___rarg(x_12);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_dec(x_13);
x_15 = l_List_toArrayAux___rarg(x_12, x_14);
x_16 = lean_array_get_size(x_15);
x_17 = lean_nat_dec_lt(x_2, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_19 = l_panic___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(x_18);
x_20 = l_panic___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(x_18);
lean_inc(x_11);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__2), 13, 8);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_3);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_15);
lean_closure_set(x_21, 4, x_19);
lean_closure_set(x_21, 5, x_2);
lean_closure_set(x_21, 6, x_11);
lean_closure_set(x_21, 7, x_10);
x_22 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_11, x_21, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_array_fget(x_15, x_2);
lean_inc(x_11);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__3), 12, 7);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_3);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_15);
lean_closure_set(x_24, 4, x_2);
lean_closure_set(x_24, 5, x_11);
lean_closure_set(x_24, 6, x_10);
x_25 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_11, x_24, x_5, x_6, x_7, x_8, x_9);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("motive := ", 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Array_toSubarray___rarg(x_1, x_10, x_2);
x_12 = l_Array_ofSubarray___rarg(x_11);
x_13 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_14 = lean_array_push(x_13, x_4);
x_15 = l_Array_append___rarg(x_12, x_14);
x_16 = lean_array_get_size(x_1);
x_17 = l_Array_toSubarray___rarg(x_1, x_2, x_16);
x_18 = l_Array_ofSubarray___rarg(x_17);
x_19 = l_Array_append___rarg(x_15, x_18);
x_20 = 0;
x_21 = 1;
x_22 = 1;
x_23 = l_Lean_Meta_mkLambdaFVars(x_19, x_3, x_20, x_21, x_22, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_42 = lean_st_ref_get(x_8, x_25);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 3);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_28 = x_20;
x_29 = x_46;
goto block_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_dec(x_42);
x_48 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_27, x_5, x_6, x_7, x_8, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_49);
lean_dec(x_49);
x_28 = x_51;
x_29 = x_50;
goto block_41;
}
block_41:
{
if (x_28 == 0)
{
lean_object* x_30; 
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_26);
lean_inc(x_24);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_24);
x_32 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_27, x_35, x_5, x_6, x_7, x_8, x_29);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_24);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_24);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_23);
if (x_52 == 0)
{
return x_23;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_23, 0);
x_54 = lean_ctor_get(x_23, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_23);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h_below", 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_1, 5);
x_12 = lean_array_get_size(x_11);
x_13 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2;
x_14 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_13, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Expr_replaceFVars(x_2, x_3, x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___boxed), 9, 3);
lean_closure_set(x_18, 0, x_4);
lean_closure_set(x_18, 1, x_12);
lean_closure_set(x_18, 2, x_5);
x_19 = 0;
x_20 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_15, x_19, x_17, x_18, x_6, x_7, x_8, x_9, x_16);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___boxed), 10, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
x_11 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__5___rarg(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
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
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_4, 1, x_20);
lean_ctor_set(x_4, 0, x_16);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_4, 1, x_21);
lean_ctor_set(x_4, 0, x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_16);
lean_free_object(x_4);
x_24 = !lean_is_exclusive(x_18);
if (x_24 == 0)
{
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
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
lean_free_object(x_4);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(x_1, x_2, x_3, x_32, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(x_1, x_2, x_3, x_33, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_38);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_39);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_35);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
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
lean_dec(x_33);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_LocalDecl_toExpr(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("alt ", 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":\n", 2);
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_15 = lean_array_get_size(x_1);
lean_inc(x_2);
x_16 = l_Array_toSubarray___rarg(x_1, x_2, x_15);
x_17 = l_Array_ofSubarray___rarg(x_16);
x_18 = l_Array_append___rarg(x_3, x_17);
x_19 = lean_array_get_size(x_4);
x_20 = l_Array_toSubarray___rarg(x_4, x_2, x_19);
x_21 = l_Array_ofSubarray___rarg(x_20);
x_22 = l_Array_append___rarg(x_18, x_21);
x_23 = 0;
x_24 = 1;
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_22, x_5, x_23, x_24, x_25, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_54 = lean_st_ref_get(x_13, x_28);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 3);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get_uint8(x_56, sizeof(void*)*1);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_30 = x_23;
x_31 = x_58;
goto block_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
lean_inc(x_8);
x_60 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_8, x_10, x_11, x_12, x_13, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unbox(x_61);
lean_dec(x_61);
x_30 = x_63;
x_31 = x_62;
goto block_53;
}
block_53:
{
if (x_30 == 0)
{
lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_29);
x_33 = l_Nat_repr(x_6);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__2;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__4;
x_39 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_7);
x_41 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_inc(x_27);
x_44 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_44, 0, x_27);
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_8, x_47, x_10, x_11, x_12, x_13, x_31);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_27);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_27);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_64 = !lean_is_exclusive(x_26);
if (x_64 == 0)
{
return x_26;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_26, 0);
x_66 = lean_ctor_get(x_26, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_26);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("xs = ", 5);
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("; oldFVars = ", 13);
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("; fvars = ", 10);
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("; new = ", 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_12 = l_List_redLength___rarg(x_1);
x_13 = lean_mk_empty_array_with_capacity(x_12);
lean_dec(x_12);
x_14 = l_List_toArrayAux___rarg(x_1, x_13);
x_15 = l_List_redLength___rarg(x_2);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
x_17 = l_List_toArrayAux___rarg(x_2, x_16);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(x_19, x_20, x_17);
x_22 = lean_array_get_size(x_21);
x_23 = lean_array_get_size(x_14);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_eq(x_23, x_24);
lean_inc(x_23);
lean_inc(x_21);
x_26 = l_Array_toSubarray___rarg(x_21, x_24, x_23);
x_27 = l_Array_ofSubarray___rarg(x_26);
x_28 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_29 = lean_st_ref_get(x_10, x_11);
if (x_25 == 0)
{
lean_dec(x_22);
x_30 = x_5;
goto block_95;
}
else
{
uint8_t x_96; 
x_96 = lean_nat_dec_eq(x_22, x_24);
lean_dec(x_22);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_array_get_size(x_5);
x_98 = lean_unsigned_to_nat(1u);
x_99 = l_Array_toSubarray___rarg(x_5, x_98, x_97);
x_100 = l_Array_ofSubarray___rarg(x_99);
x_30 = x_100;
goto block_95;
}
else
{
x_30 = x_5;
goto block_95;
}
}
block_95:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_inc(x_23);
lean_inc(x_30);
x_31 = l_Array_toSubarray___rarg(x_30, x_24, x_23);
x_32 = l_Array_ofSubarray___rarg(x_31);
x_33 = l_Lean_Expr_replaceFVars(x_6, x_32, x_27);
lean_dec(x_32);
lean_dec(x_6);
x_85 = lean_ctor_get(x_29, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 3);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_ctor_get_uint8(x_86, sizeof(void*)*1);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_29, 1);
lean_inc(x_88);
lean_dec(x_29);
x_89 = 0;
x_34 = x_89;
x_35 = x_88;
goto block_84;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_29, 1);
lean_inc(x_90);
lean_dec(x_29);
x_91 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_28, x_7, x_8, x_9, x_10, x_90);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_unbox(x_92);
lean_dec(x_92);
x_34 = x_94;
x_35 = x_93;
goto block_84;
}
block_84:
{
if (x_34 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_14);
x_36 = lean_box(0);
x_37 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1(x_30, x_23, x_27, x_21, x_33, x_3, x_4, x_28, x_36, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_inc(x_30);
x_38 = lean_array_to_list(lean_box(0), x_30);
x_39 = lean_box(0);
x_40 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_38, x_39);
x_41 = l_Lean_MessageData_ofList(x_40);
lean_dec(x_40);
x_42 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__2;
x_43 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__4;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_usize_of_nat(x_23);
x_47 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(x_46, x_20, x_14);
x_48 = lean_array_to_list(lean_box(0), x_47);
x_49 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_48, x_39);
x_50 = l_Lean_MessageData_ofList(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__6;
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_21);
x_54 = lean_array_to_list(lean_box(0), x_21);
x_55 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_54, x_39);
x_56 = l_Lean_MessageData_ofList(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__8;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_get_size(x_30);
lean_inc(x_23);
lean_inc(x_30);
x_61 = l_Array_toSubarray___rarg(x_30, x_23, x_60);
x_62 = l_Array_ofSubarray___rarg(x_61);
lean_inc(x_27);
x_63 = l_Array_append___rarg(x_27, x_62);
x_64 = lean_array_get_size(x_63);
x_65 = l_Array_toSubarray___rarg(x_63, x_24, x_64);
x_66 = lean_array_get_size(x_21);
lean_inc(x_23);
lean_inc(x_21);
x_67 = l_Array_toSubarray___rarg(x_21, x_23, x_66);
x_68 = l_Array_ofSubarray___rarg(x_65);
x_69 = l_Array_ofSubarray___rarg(x_67);
x_70 = l_Array_append___rarg(x_68, x_69);
x_71 = lean_array_get_size(x_70);
x_72 = l_Array_toSubarray___rarg(x_70, x_24, x_71);
x_73 = l_Array_ofSubarray___rarg(x_72);
x_74 = lean_array_to_list(lean_box(0), x_73);
x_75 = l_List_mapTRAux___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_74, x_39);
x_76 = l_Lean_MessageData_ofList(x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_59);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_28, x_79, x_7, x_8, x_9, x_10, x_35);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1(x_30, x_23, x_27, x_21, x_33, x_3, x_4, x_28, x_81, x_7, x_8, x_9, x_10, x_82);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_81);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_5, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_5, x_16);
lean_dec(x_5);
x_18 = lean_array_fget(x_4, x_6);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_24);
lean_inc(x_23);
x_25 = l_List_appendTR___rarg(x_23, x_24);
lean_inc(x_20);
lean_inc(x_6);
x_26 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2), 11, 4);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_6);
lean_closure_set(x_26, 3, x_20);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__5___rarg), 7, 2);
lean_closure_set(x_27, 0, x_20);
lean_closure_set(x_27, 1, x_26);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_28 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_25, x_27, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_nat_add(x_6, x_16);
lean_dec(x_6);
x_32 = lean_array_push(x_8, x_29);
x_5 = x_17;
x_6 = x_31;
x_7 = lean_box(0);
x_8 = x_32;
x_13 = x_30;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_13);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_List_appendTR___rarg(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTRAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Match_Pattern_toMessageData(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_Match_Pattern_toMessageData(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_traceMsg", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("[", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("] ", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Util_Trace_0__Lean_addTraceOptions(x_10);
x_13 = lean_st_ref_take(x_6, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 3);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__2;
x_22 = l_Lean_Name_append(x_1, x_21);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__4;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__6;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
x_29 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
lean_inc(x_8);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Std_PersistentArray_push___rarg(x_20, x_32);
lean_ctor_set(x_15, 0, x_33);
x_34 = lean_st_ref_set(x_6, x_14, x_16);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_41 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
x_43 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__2;
x_44 = l_Lean_Name_append(x_1, x_43);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_1);
x_46 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__4;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__6;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_12);
x_51 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_8);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_PersistentArray_push___rarg(x_42, x_54);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_41);
lean_ctor_set(x_14, 3, x_56);
x_57 = lean_st_ref_set(x_6, x_14, x_16);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_box(0);
if (lean_is_scalar(x_59)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_59;
}
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_62 = lean_ctor_get(x_14, 0);
x_63 = lean_ctor_get(x_14, 1);
x_64 = lean_ctor_get(x_14, 2);
x_65 = lean_ctor_get(x_14, 4);
x_66 = lean_ctor_get(x_14, 5);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_14);
x_67 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
x_68 = lean_ctor_get(x_15, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_69 = x_15;
} else {
 lean_dec_ref(x_15);
 x_69 = lean_box(0);
}
x_70 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__2;
x_71 = l_Lean_Name_append(x_1, x_70);
x_72 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_72, 0, x_1);
x_73 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__4;
x_74 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__6;
x_76 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_12);
x_78 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_80, 0, x_71);
lean_ctor_set(x_80, 1, x_79);
lean_inc(x_8);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_8);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Std_PersistentArray_push___rarg(x_68, x_81);
if (lean_is_scalar(x_69)) {
 x_83 = lean_alloc_ctor(0, 1, 1);
} else {
 x_83 = x_69;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_67);
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_62);
lean_ctor_set(x_84, 1, x_63);
lean_ctor_set(x_84, 2, x_64);
lean_ctor_set(x_84, 3, x_83);
lean_ctor_set(x_84, 4, x_65);
lean_ctor_set(x_84, 5, x_66);
x_85 = lean_st_ref_set(x_6, x_84, x_16);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_29 = lean_st_ref_get(x_6, x_7);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = 0;
x_12 = x_34;
x_13 = x_33;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_11, x_3, x_4, x_5, x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unbox(x_37);
lean_dec(x_37);
x_12 = x_39;
x_13 = x_38;
goto block_28;
}
block_28:
{
if (x_12 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_box(0);
x_1 = x_10;
x_2 = x_14;
x_7 = x_13;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_9, 2);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_box(0);
x_18 = l_List_mapTRAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__5(x_16, x_17);
x_19 = l_List_mapTRAux___at_Lean_Meta_Match_Alt_toMessageData___spec__2(x_18, x_17);
x_20 = l_Lean_MessageData_ofList(x_19);
lean_dec(x_19);
x_21 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(x_11, x_23, x_3, x_4, x_5, x_6, x_13);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_1 = x_10;
x_2 = x_26;
x_7 = x_25;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_array_push(x_1, x_3);
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkForallFVars(x_9, x_2, x_10, x_11, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_11 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_1, x_4, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
x_17 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2;
x_18 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_17, x_8, x_9, x_13);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1___boxed), 8, 2);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_5);
x_22 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_23 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_19, x_22, x_16, x_21, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_4);
lean_inc(x_16);
lean_inc(x_3);
x_26 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive(x_3, x_16, x_4, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_3, 5);
lean_inc(x_29);
lean_dec(x_3);
x_30 = l_Lean_Expr_replaceFVars(x_16, x_4, x_29);
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_12);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_15);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
x_35 = lean_ctor_get(x_3, 5);
lean_inc(x_35);
lean_dec(x_3);
x_36 = l_Lean_Expr_replaceFVars(x_16, x_4, x_35);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_16);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_15);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_24);
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_26);
if (x_40 == 0)
{
return x_26;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_26, 0);
x_42 = lean_ctor_get(x_26, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_26);
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
lean_free_object(x_12);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_23);
if (x_44 == 0)
{
return x_23;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_23, 0);
x_46 = lean_ctor_get(x_23, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_23);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_48 = lean_ctor_get(x_12, 0);
x_49 = lean_ctor_get(x_12, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_12);
x_50 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2;
x_51 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_50, x_8, x_9, x_13);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_4);
x_54 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1___boxed), 8, 2);
lean_closure_set(x_54, 0, x_4);
lean_closure_set(x_54, 1, x_5);
x_55 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_49);
x_56 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_forallTelescopeCompatibleAux___spec__15___rarg(x_52, x_55, x_49, x_54, x_6, x_7, x_8, x_9, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_4);
lean_inc(x_49);
lean_inc(x_3);
x_59 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive(x_3, x_49, x_4, x_6, x_7, x_8, x_9, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
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
x_63 = lean_ctor_get(x_3, 5);
lean_inc(x_63);
lean_dec(x_3);
x_64 = l_Lean_Expr_replaceFVars(x_49, x_4, x_63);
lean_dec(x_63);
lean_dec(x_4);
lean_dec(x_49);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_57);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_48);
lean_ctor_set(x_67, 1, x_66);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_57);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_4);
lean_dec(x_3);
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_71 = x_59;
} else {
 lean_dec_ref(x_59);
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
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_73 = lean_ctor_get(x_56, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_56, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_75 = x_56;
} else {
 lean_dec_ref(x_56);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_77 = !lean_is_exclusive(x_11);
if (x_77 == 0)
{
return x_11;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_11, 0);
x_79 = lean_ctor_get(x_11, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_11);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_box(0);
x_8 = l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_zip___rarg___lambda__1), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_Match_getMkMatcherInputInContext(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = l_Lean_Meta_Match_MkMatcherInput_numDiscrs(x_11);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2), 10, 3);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_17 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(x_13, x_15, x_16, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
x_26 = lean_ctor_get(x_11, 3);
lean_inc(x_26);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_26);
x_27 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(x_2, x_4, x_22, x_26, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1;
lean_inc(x_28);
x_31 = l_List_zipWith___rarg(x_30, x_26, x_28);
x_32 = l_List_redLength___rarg(x_31);
x_33 = lean_mk_empty_array_with_capacity(x_32);
lean_dec(x_32);
x_34 = l_List_toArrayAux___rarg(x_31, x_33);
x_35 = lean_ctor_get(x_1, 7);
lean_inc(x_35);
x_36 = l_Array_zip___rarg(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_37 = lean_array_get_size(x_36);
x_38 = lean_mk_empty_array_with_capacity(x_37);
x_39 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_40 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3(x_1, x_11, x_28, x_36, x_37, x_39, lean_box(0), x_38, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_36);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_11, 0);
lean_inc(x_43);
lean_dec(x_11);
x_44 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_43, x_7, x_8, x_42);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_box(0);
lean_inc(x_28);
x_48 = l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(x_47, x_28);
lean_inc(x_28);
x_49 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3___boxed), 6, 1);
lean_closure_set(x_49, 0, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_50 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_48, x_49, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_14, x_52);
lean_dec(x_14);
x_54 = lean_box(0);
x_55 = lean_mk_array(x_53, x_54);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_45);
lean_ctor_set(x_56, 1, x_25);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l_Lean_Meta_Match_mkMatcher(x_56, x_5, x_6, x_7, x_8, x_51);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 3);
lean_inc(x_60);
lean_inc(x_60);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_61 = lean_apply_5(x_60, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
lean_inc(x_63);
x_64 = l_Lean_Meta_check(x_63, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = l_Lean_Expr_app___override(x_63, x_24);
x_68 = lean_ctor_get(x_1, 5);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_array_push(x_68, x_3);
x_70 = l_Lean_mkAppN(x_67, x_69);
x_71 = l_Lean_mkAppN(x_70, x_41);
lean_ctor_set(x_20, 1, x_60);
lean_ctor_set(x_20, 0, x_71);
lean_ctor_set(x_64, 0, x_20);
return x_64;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_dec(x_64);
x_73 = l_Lean_Expr_app___override(x_63, x_24);
x_74 = lean_ctor_get(x_1, 5);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_array_push(x_74, x_3);
x_76 = l_Lean_mkAppN(x_73, x_75);
x_77 = l_Lean_mkAppN(x_76, x_41);
lean_ctor_set(x_20, 1, x_60);
lean_ctor_set(x_20, 0, x_77);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_20);
lean_ctor_set(x_78, 1, x_72);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_63);
lean_dec(x_60);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_64);
if (x_79 == 0)
{
return x_64;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_64, 0);
x_81 = lean_ctor_get(x_64, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_64);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_61);
if (x_83 == 0)
{
return x_61;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_61, 0);
x_85 = lean_ctor_get(x_61, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_61);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_57);
if (x_87 == 0)
{
return x_57;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_57, 0);
x_89 = lean_ctor_get(x_57, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_57);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_45);
lean_dec(x_41);
lean_dec(x_28);
lean_free_object(x_20);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_50);
if (x_91 == 0)
{
return x_50;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_50, 0);
x_93 = lean_ctor_get(x_50, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_50);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_28);
lean_free_object(x_20);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_40);
if (x_95 == 0)
{
return x_40;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_40, 0);
x_97 = lean_ctor_get(x_40, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_40);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_26);
lean_free_object(x_20);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_27);
if (x_99 == 0)
{
return x_27;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_27, 0);
x_101 = lean_ctor_get(x_27, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_27);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_20, 0);
x_104 = lean_ctor_get(x_20, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_20);
x_105 = lean_ctor_get(x_11, 3);
lean_inc(x_105);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_105);
x_106 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(x_2, x_4, x_22, x_105, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1;
lean_inc(x_107);
x_110 = l_List_zipWith___rarg(x_109, x_105, x_107);
x_111 = l_List_redLength___rarg(x_110);
x_112 = lean_mk_empty_array_with_capacity(x_111);
lean_dec(x_111);
x_113 = l_List_toArrayAux___rarg(x_110, x_112);
x_114 = lean_ctor_get(x_1, 7);
lean_inc(x_114);
x_115 = l_Array_zip___rarg(x_113, x_114);
lean_dec(x_114);
lean_dec(x_113);
x_116 = lean_array_get_size(x_115);
x_117 = lean_mk_empty_array_with_capacity(x_116);
x_118 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_119 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3(x_1, x_11, x_107, x_115, x_116, x_118, lean_box(0), x_117, x_5, x_6, x_7, x_8, x_108);
lean_dec(x_115);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_11, 0);
lean_inc(x_122);
lean_dec(x_11);
x_123 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_122, x_7, x_8, x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_box(0);
lean_inc(x_107);
x_127 = l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(x_126, x_107);
lean_inc(x_107);
x_128 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3___boxed), 6, 1);
lean_closure_set(x_128, 0, x_107);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_129 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_127, x_128, x_5, x_6, x_7, x_8, x_125);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_add(x_14, x_131);
lean_dec(x_14);
x_133 = lean_box(0);
x_134 = lean_mk_array(x_132, x_133);
x_135 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_135, 0, x_124);
lean_ctor_set(x_135, 1, x_104);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_107);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_136 = l_Lean_Meta_Match_mkMatcher(x_135, x_5, x_6, x_7, x_8, x_130);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 3);
lean_inc(x_139);
lean_inc(x_139);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_140 = lean_apply_5(x_139, x_5, x_6, x_7, x_8, x_138);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_142 = lean_ctor_get(x_137, 0);
lean_inc(x_142);
lean_dec(x_137);
lean_inc(x_142);
x_143 = l_Lean_Meta_check(x_142, x_5, x_6, x_7, x_8, x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = l_Lean_Expr_app___override(x_142, x_103);
x_147 = lean_ctor_get(x_1, 5);
lean_inc(x_147);
lean_dec(x_1);
x_148 = lean_array_push(x_147, x_3);
x_149 = l_Lean_mkAppN(x_146, x_148);
x_150 = l_Lean_mkAppN(x_149, x_120);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_139);
if (lean_is_scalar(x_145)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_145;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_144);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_142);
lean_dec(x_139);
lean_dec(x_120);
lean_dec(x_103);
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_ctor_get(x_143, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_143, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_155 = x_143;
} else {
 lean_dec_ref(x_143);
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
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_120);
lean_dec(x_103);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_157 = lean_ctor_get(x_140, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_140, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_159 = x_140;
} else {
 lean_dec_ref(x_140);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_120);
lean_dec(x_103);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_161 = lean_ctor_get(x_136, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_136, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_163 = x_136;
} else {
 lean_dec_ref(x_136);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_124);
lean_dec(x_120);
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_165 = lean_ctor_get(x_129, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_129, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_167 = x_129;
} else {
 lean_dec_ref(x_129);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_169 = lean_ctor_get(x_119, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_119, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_171 = x_119;
} else {
 lean_dec_ref(x_119);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_173 = lean_ctor_get(x_106, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_106, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_175 = x_106;
} else {
 lean_dec_ref(x_106);
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
}
else
{
uint8_t x_177; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_17);
if (x_177 == 0)
{
return x_17;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_17, 0);
x_179 = lean_ctor_get(x_17, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_17);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_10);
if (x_181 == 0)
{
return x_10;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_10, 0);
x_183 = lean_ctor_get(x_10, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_10);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_3, x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_2, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lean_Meta_isExprDefEq(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_12, 0, x_22);
return x_12;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_10, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_10);
lean_dec(x_10);
lean_inc(x_2);
x_22 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_2, x_1, x_20, x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_3);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_22, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_22, 0, x_35);
return x_22;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_22, 1);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("could not find below term in the local context", 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Found below term in the local context: ", 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
lean_inc(x_1);
x_11 = l_Lean_Expr_mvarId_x21(x_1);
x_12 = lean_unsigned_to_nat(10u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_11, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_get(x_9, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 3);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*1);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_2);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__1;
x_23 = lean_box(0);
x_24 = lean_apply_6(x_22, x_23, x_6, x_7, x_8, x_9, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_17, 1);
lean_inc(x_25);
lean_dec(x_17);
lean_inc(x_2);
x_26 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_2, x_6, x_7, x_8, x_9, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__1;
x_30 = lean_unbox(x_27);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = lean_apply_6(x_29, x_31, x_6, x_7, x_8, x_9, x_28);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__3;
x_34 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_33, x_6, x_7, x_8, x_9, x_28);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_6(x_29, x_35, x_6, x_7, x_8, x_9, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_dec(x_13);
x_53 = lean_st_ref_get(x_9, x_38);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*1);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = 0;
x_39 = x_58;
x_40 = x_57;
goto block_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
lean_dec(x_53);
lean_inc(x_2);
x_60 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_2, x_6, x_7, x_8, x_9, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unbox(x_61);
lean_dec(x_61);
x_39 = x_63;
x_40 = x_62;
goto block_52;
}
block_52:
{
if (x_39 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_2);
x_41 = lean_box(0);
x_42 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__2(x_3, x_1, x_4, x_41, x_6, x_7, x_8, x_9, x_40);
lean_dec(x_3);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_inc(x_1);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_1);
x_44 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__5;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_47, x_6, x_7, x_8, x_9, x_40);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__2(x_3, x_1, x_4, x_49, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_49);
lean_dec(x_3);
return x_51;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
return x_13;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_13, 0);
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_13);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_12);
x_14 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
else
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_11);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Lean_Meta_isInductivePredicate(x_19, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
lean_inc(x_1);
x_31 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_20, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(0);
lean_inc(x_7);
x_36 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_34, x_35, x_7, x_8, x_9, x_10, x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_75 = lean_st_ref_get(x_10, x_38);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 3);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get_uint8(x_77, sizeof(void*)*1);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = 0;
x_40 = x_80;
x_41 = x_79;
goto block_74;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_39, x_7, x_8, x_9, x_10, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_unbox(x_83);
lean_dec(x_83);
x_40 = x_85;
x_41 = x_84;
goto block_74;
}
block_74:
{
if (x_40 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_37, x_39, x_1, x_20, x_42, x_7, x_8, x_9, x_10, x_41);
if (lean_obj_tag(x_43) == 0)
{
return x_43;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set_tag(x_43, 0);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 1);
lean_inc(x_47);
lean_dec(x_43);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_inc(x_37);
x_50 = l_Lean_Expr_mvarId_x21(x_37);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_51 = l_Lean_Meta_ppGoal(x_50, x_7, x_8, x_9, x_10, x_41);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_52);
x_55 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_39, x_57, x_7, x_8, x_9, x_10, x_53);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_37, x_39, x_1, x_20, x_59, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_61) == 0)
{
return x_61;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
x_64 = lean_box(0);
lean_ctor_set_tag(x_61, 0);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_37);
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_51);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_51, 0);
lean_dec(x_69);
x_70 = lean_box(0);
lean_ctor_set_tag(x_51, 0);
lean_ctor_set(x_51, 0, x_70);
return x_51;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_51, 1);
lean_inc(x_71);
lean_dec(x_51);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_31);
if (x_86 == 0)
{
return x_31;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_31, 0);
x_88 = lean_ctor_get(x_31, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_31);
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
uint8_t x_90; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_21);
if (x_90 == 0)
{
return x_21;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_21, 0);
x_92 = lean_ctor_get(x_21, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_21);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
case 1:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_6);
lean_dec(x_5);
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_94);
x_96 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_95);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_11);
return x_98;
}
else
{
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_96);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_11);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_96, 0);
lean_inc(x_101);
lean_dec(x_96);
x_102 = lean_ctor_get(x_95, 0);
lean_inc(x_102);
lean_dec(x_95);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_103 = l_Lean_Meta_isInductivePredicate(x_101, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
uint8_t x_106; 
lean_dec(x_102);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_103, 0);
lean_dec(x_107);
x_108 = lean_box(0);
lean_ctor_set(x_103, 0, x_108);
return x_103;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
lean_dec(x_103);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_103, 1);
lean_inc(x_112);
lean_dec(x_103);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_102);
lean_inc(x_1);
x_113 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_102, x_7, x_8, x_9, x_10, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_box(0);
lean_inc(x_7);
x_118 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_116, x_117, x_7, x_8, x_9, x_10, x_115);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_157 = lean_st_ref_get(x_10, x_120);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_158, 3);
lean_inc(x_159);
lean_dec(x_158);
x_160 = lean_ctor_get_uint8(x_159, sizeof(void*)*1);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
lean_dec(x_157);
x_162 = 0;
x_122 = x_162;
x_123 = x_161;
goto block_156;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
x_164 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_121, x_7, x_8, x_9, x_10, x_163);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_unbox(x_165);
lean_dec(x_165);
x_122 = x_167;
x_123 = x_166;
goto block_156;
}
block_156:
{
if (x_122 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_box(0);
x_125 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_119, x_121, x_1, x_102, x_124, x_7, x_8, x_9, x_10, x_123);
if (lean_obj_tag(x_125) == 0)
{
return x_125;
}
else
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 0);
lean_dec(x_127);
x_128 = lean_box(0);
lean_ctor_set_tag(x_125, 0);
lean_ctor_set(x_125, 0, x_128);
return x_125;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_125, 1);
lean_inc(x_129);
lean_dec(x_125);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_inc(x_119);
x_132 = l_Lean_Expr_mvarId_x21(x_119);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_133 = l_Lean_Meta_ppGoal(x_132, x_7, x_8, x_9, x_10, x_123);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_134);
x_137 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_138 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
x_140 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_121, x_139, x_7, x_8, x_9, x_10, x_135);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_119, x_121, x_1, x_102, x_141, x_7, x_8, x_9, x_10, x_142);
if (lean_obj_tag(x_143) == 0)
{
return x_143;
}
else
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_143, 0);
lean_dec(x_145);
x_146 = lean_box(0);
lean_ctor_set_tag(x_143, 0);
lean_ctor_set(x_143, 0, x_146);
return x_143;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_119);
lean_dec(x_102);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_133);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_133, 0);
lean_dec(x_151);
x_152 = lean_box(0);
lean_ctor_set_tag(x_133, 0);
lean_ctor_set(x_133, 0, x_152);
return x_133;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_133, 1);
lean_inc(x_153);
lean_dec(x_133);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_102);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_168 = !lean_is_exclusive(x_113);
if (x_168 == 0)
{
return x_113;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_113, 0);
x_170 = lean_ctor_get(x_113, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_113);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_102);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_172 = !lean_is_exclusive(x_103);
if (x_172 == 0)
{
return x_103;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_103, 0);
x_174 = lean_ctor_get(x_103, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_103);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
}
case 2:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_6);
lean_dec(x_5);
x_176 = lean_unsigned_to_nat(0u);
x_177 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_176);
x_178 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_177);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_11);
return x_180;
}
else
{
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_178);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_11);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_178, 0);
lean_inc(x_183);
lean_dec(x_178);
x_184 = lean_ctor_get(x_177, 0);
lean_inc(x_184);
lean_dec(x_177);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_185 = l_Lean_Meta_isInductivePredicate(x_183, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_unbox(x_186);
lean_dec(x_186);
if (x_187 == 0)
{
uint8_t x_188; 
lean_dec(x_184);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_185);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_185, 0);
lean_dec(x_189);
x_190 = lean_box(0);
lean_ctor_set(x_185, 0, x_190);
return x_185;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_185, 1);
lean_inc(x_191);
lean_dec(x_185);
x_192 = lean_box(0);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_185, 1);
lean_inc(x_194);
lean_dec(x_185);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_184);
lean_inc(x_1);
x_195 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_184, x_7, x_8, x_9, x_10, x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_box(0);
lean_inc(x_7);
x_200 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_198, x_199, x_7, x_8, x_9, x_10, x_197);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_239 = lean_st_ref_get(x_10, x_202);
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_240, 3);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_ctor_get_uint8(x_241, sizeof(void*)*1);
lean_dec(x_241);
if (x_242 == 0)
{
lean_object* x_243; uint8_t x_244; 
x_243 = lean_ctor_get(x_239, 1);
lean_inc(x_243);
lean_dec(x_239);
x_244 = 0;
x_204 = x_244;
x_205 = x_243;
goto block_238;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_245 = lean_ctor_get(x_239, 1);
lean_inc(x_245);
lean_dec(x_239);
x_246 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_203, x_7, x_8, x_9, x_10, x_245);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_unbox(x_247);
lean_dec(x_247);
x_204 = x_249;
x_205 = x_248;
goto block_238;
}
block_238:
{
if (x_204 == 0)
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_box(0);
x_207 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_201, x_203, x_1, x_184, x_206, x_7, x_8, x_9, x_10, x_205);
if (lean_obj_tag(x_207) == 0)
{
return x_207;
}
else
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_207, 0);
lean_dec(x_209);
x_210 = lean_box(0);
lean_ctor_set_tag(x_207, 0);
lean_ctor_set(x_207, 0, x_210);
return x_207;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
lean_dec(x_207);
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
else
{
lean_object* x_214; lean_object* x_215; 
lean_inc(x_201);
x_214 = l_Lean_Expr_mvarId_x21(x_201);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_215 = l_Lean_Meta_ppGoal(x_214, x_7, x_8, x_9, x_10, x_205);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_216);
x_219 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_220 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_218);
x_221 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_219);
x_222 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_203, x_221, x_7, x_8, x_9, x_10, x_217);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_201, x_203, x_1, x_184, x_223, x_7, x_8, x_9, x_10, x_224);
if (lean_obj_tag(x_225) == 0)
{
return x_225;
}
else
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_225, 0);
lean_dec(x_227);
x_228 = lean_box(0);
lean_ctor_set_tag(x_225, 0);
lean_ctor_set(x_225, 0, x_228);
return x_225;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_225, 1);
lean_inc(x_229);
lean_dec(x_225);
x_230 = lean_box(0);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_229);
return x_231;
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_201);
lean_dec(x_184);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_232 = !lean_is_exclusive(x_215);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_215, 0);
lean_dec(x_233);
x_234 = lean_box(0);
lean_ctor_set_tag(x_215, 0);
lean_ctor_set(x_215, 0, x_234);
return x_215;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_215, 1);
lean_inc(x_235);
lean_dec(x_215);
x_236 = lean_box(0);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_184);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_195);
if (x_250 == 0)
{
return x_195;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_195, 0);
x_252 = lean_ctor_get(x_195, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_195);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
}
else
{
uint8_t x_254; 
lean_dec(x_184);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_254 = !lean_is_exclusive(x_185);
if (x_254 == 0)
{
return x_185;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_185, 0);
x_256 = lean_ctor_get(x_185, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_185);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
}
}
case 3:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_6);
lean_dec(x_5);
x_258 = lean_unsigned_to_nat(0u);
x_259 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_258);
x_260 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_259);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_box(0);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_11);
return x_262;
}
else
{
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_260);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_263 = lean_box(0);
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_11);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_260, 0);
lean_inc(x_265);
lean_dec(x_260);
x_266 = lean_ctor_get(x_259, 0);
lean_inc(x_266);
lean_dec(x_259);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_267 = l_Lean_Meta_isInductivePredicate(x_265, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; uint8_t x_269; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_unbox(x_268);
lean_dec(x_268);
if (x_269 == 0)
{
uint8_t x_270; 
lean_dec(x_266);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_267);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_267, 0);
lean_dec(x_271);
x_272 = lean_box(0);
lean_ctor_set(x_267, 0, x_272);
return x_267;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_267, 1);
lean_inc(x_273);
lean_dec(x_267);
x_274 = lean_box(0);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_267, 1);
lean_inc(x_276);
lean_dec(x_267);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_266);
lean_inc(x_1);
x_277 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_266, x_7, x_8, x_9, x_10, x_276);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_ctor_get(x_278, 1);
lean_inc(x_280);
lean_dec(x_278);
x_281 = lean_box(0);
lean_inc(x_7);
x_282 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_280, x_281, x_7, x_8, x_9, x_10, x_279);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_321 = lean_st_ref_get(x_10, x_284);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_322, 3);
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_ctor_get_uint8(x_323, sizeof(void*)*1);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; uint8_t x_326; 
x_325 = lean_ctor_get(x_321, 1);
lean_inc(x_325);
lean_dec(x_321);
x_326 = 0;
x_286 = x_326;
x_287 = x_325;
goto block_320;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_327 = lean_ctor_get(x_321, 1);
lean_inc(x_327);
lean_dec(x_321);
x_328 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_285, x_7, x_8, x_9, x_10, x_327);
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_unbox(x_329);
lean_dec(x_329);
x_286 = x_331;
x_287 = x_330;
goto block_320;
}
block_320:
{
if (x_286 == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_box(0);
x_289 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_283, x_285, x_1, x_266, x_288, x_7, x_8, x_9, x_10, x_287);
if (lean_obj_tag(x_289) == 0)
{
return x_289;
}
else
{
uint8_t x_290; 
x_290 = !lean_is_exclusive(x_289);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_289, 0);
lean_dec(x_291);
x_292 = lean_box(0);
lean_ctor_set_tag(x_289, 0);
lean_ctor_set(x_289, 0, x_292);
return x_289;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_289, 1);
lean_inc(x_293);
lean_dec(x_289);
x_294 = lean_box(0);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
}
}
else
{
lean_object* x_296; lean_object* x_297; 
lean_inc(x_283);
x_296 = l_Lean_Expr_mvarId_x21(x_283);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_297 = l_Lean_Meta_ppGoal(x_296, x_7, x_8, x_9, x_10, x_287);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_300, 0, x_298);
x_301 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_302 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
x_303 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_301);
x_304 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_285, x_303, x_7, x_8, x_9, x_10, x_299);
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_283, x_285, x_1, x_266, x_305, x_7, x_8, x_9, x_10, x_306);
if (lean_obj_tag(x_307) == 0)
{
return x_307;
}
else
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_307, 0);
lean_dec(x_309);
x_310 = lean_box(0);
lean_ctor_set_tag(x_307, 0);
lean_ctor_set(x_307, 0, x_310);
return x_307;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_307, 1);
lean_inc(x_311);
lean_dec(x_307);
x_312 = lean_box(0);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_311);
return x_313;
}
}
}
else
{
uint8_t x_314; 
lean_dec(x_283);
lean_dec(x_266);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_314 = !lean_is_exclusive(x_297);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_297, 0);
lean_dec(x_315);
x_316 = lean_box(0);
lean_ctor_set_tag(x_297, 0);
lean_ctor_set(x_297, 0, x_316);
return x_297;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_297, 1);
lean_inc(x_317);
lean_dec(x_297);
x_318 = lean_box(0);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
}
}
}
}
else
{
uint8_t x_332; 
lean_dec(x_266);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_332 = !lean_is_exclusive(x_277);
if (x_332 == 0)
{
return x_277;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_277, 0);
x_334 = lean_ctor_get(x_277, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_277);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
return x_335;
}
}
}
}
else
{
uint8_t x_336; 
lean_dec(x_266);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_336 = !lean_is_exclusive(x_267);
if (x_336 == 0)
{
return x_267;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_267, 0);
x_338 = lean_ctor_get(x_267, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_267);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
}
}
case 4:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_6);
lean_dec(x_5);
x_340 = lean_unsigned_to_nat(0u);
x_341 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_340);
x_342 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_341);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_343 = lean_box(0);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_11);
return x_344;
}
else
{
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_345; lean_object* x_346; 
lean_dec(x_342);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_345 = lean_box(0);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_11);
return x_346;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_342, 0);
lean_inc(x_347);
lean_dec(x_342);
x_348 = lean_ctor_get(x_341, 0);
lean_inc(x_348);
lean_dec(x_341);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_349 = l_Lean_Meta_isInductivePredicate(x_347, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; uint8_t x_351; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_unbox(x_350);
lean_dec(x_350);
if (x_351 == 0)
{
uint8_t x_352; 
lean_dec(x_348);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_352 = !lean_is_exclusive(x_349);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_349, 0);
lean_dec(x_353);
x_354 = lean_box(0);
lean_ctor_set(x_349, 0, x_354);
return x_349;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_349, 1);
lean_inc(x_355);
lean_dec(x_349);
x_356 = lean_box(0);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_355);
return x_357;
}
}
else
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_349, 1);
lean_inc(x_358);
lean_dec(x_349);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_348);
lean_inc(x_1);
x_359 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_348, x_7, x_8, x_9, x_10, x_358);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_box(0);
lean_inc(x_7);
x_364 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_362, x_363, x_7, x_8, x_9, x_10, x_361);
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec(x_364);
x_367 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_403 = lean_st_ref_get(x_10, x_366);
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_404, 3);
lean_inc(x_405);
lean_dec(x_404);
x_406 = lean_ctor_get_uint8(x_405, sizeof(void*)*1);
lean_dec(x_405);
if (x_406 == 0)
{
lean_object* x_407; uint8_t x_408; 
x_407 = lean_ctor_get(x_403, 1);
lean_inc(x_407);
lean_dec(x_403);
x_408 = 0;
x_368 = x_408;
x_369 = x_407;
goto block_402;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_409 = lean_ctor_get(x_403, 1);
lean_inc(x_409);
lean_dec(x_403);
x_410 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_367, x_7, x_8, x_9, x_10, x_409);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_unbox(x_411);
lean_dec(x_411);
x_368 = x_413;
x_369 = x_412;
goto block_402;
}
block_402:
{
if (x_368 == 0)
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_box(0);
x_371 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_365, x_367, x_1, x_348, x_370, x_7, x_8, x_9, x_10, x_369);
if (lean_obj_tag(x_371) == 0)
{
return x_371;
}
else
{
uint8_t x_372; 
x_372 = !lean_is_exclusive(x_371);
if (x_372 == 0)
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_371, 0);
lean_dec(x_373);
x_374 = lean_box(0);
lean_ctor_set_tag(x_371, 0);
lean_ctor_set(x_371, 0, x_374);
return x_371;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_371, 1);
lean_inc(x_375);
lean_dec(x_371);
x_376 = lean_box(0);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_375);
return x_377;
}
}
}
else
{
lean_object* x_378; lean_object* x_379; 
lean_inc(x_365);
x_378 = l_Lean_Expr_mvarId_x21(x_365);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_379 = l_Lean_Meta_ppGoal(x_378, x_7, x_8, x_9, x_10, x_369);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_380 = lean_ctor_get(x_379, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 1);
lean_inc(x_381);
lean_dec(x_379);
x_382 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_382, 0, x_380);
x_383 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_384 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_382);
x_385 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_383);
x_386 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_367, x_385, x_7, x_8, x_9, x_10, x_381);
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
x_389 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_365, x_367, x_1, x_348, x_387, x_7, x_8, x_9, x_10, x_388);
if (lean_obj_tag(x_389) == 0)
{
return x_389;
}
else
{
uint8_t x_390; 
x_390 = !lean_is_exclusive(x_389);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_389, 0);
lean_dec(x_391);
x_392 = lean_box(0);
lean_ctor_set_tag(x_389, 0);
lean_ctor_set(x_389, 0, x_392);
return x_389;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_389, 1);
lean_inc(x_393);
lean_dec(x_389);
x_394 = lean_box(0);
x_395 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
}
else
{
uint8_t x_396; 
lean_dec(x_365);
lean_dec(x_348);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_396 = !lean_is_exclusive(x_379);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; 
x_397 = lean_ctor_get(x_379, 0);
lean_dec(x_397);
x_398 = lean_box(0);
lean_ctor_set_tag(x_379, 0);
lean_ctor_set(x_379, 0, x_398);
return x_379;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_399 = lean_ctor_get(x_379, 1);
lean_inc(x_399);
lean_dec(x_379);
x_400 = lean_box(0);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
}
}
}
else
{
uint8_t x_414; 
lean_dec(x_348);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_414 = !lean_is_exclusive(x_359);
if (x_414 == 0)
{
return x_359;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_359, 0);
x_416 = lean_ctor_get(x_359, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_359);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
}
else
{
uint8_t x_418; 
lean_dec(x_348);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_418 = !lean_is_exclusive(x_349);
if (x_418 == 0)
{
return x_349;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_349, 0);
x_420 = lean_ctor_get(x_349, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_349);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
}
}
case 5:
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_422 = lean_ctor_get(x_4, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_4, 1);
lean_inc(x_423);
lean_dec(x_4);
x_424 = lean_array_set(x_5, x_6, x_423);
x_425 = lean_unsigned_to_nat(1u);
x_426 = lean_nat_sub(x_6, x_425);
lean_dec(x_6);
x_4 = x_422;
x_5 = x_424;
x_6 = x_426;
goto _start;
}
case 6:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; 
lean_dec(x_6);
lean_dec(x_5);
x_428 = lean_unsigned_to_nat(0u);
x_429 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_428);
x_430 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_429);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_431 = lean_box(0);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_11);
return x_432;
}
else
{
if (lean_obj_tag(x_429) == 0)
{
lean_object* x_433; lean_object* x_434; 
lean_dec(x_430);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_433 = lean_box(0);
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_11);
return x_434;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_430, 0);
lean_inc(x_435);
lean_dec(x_430);
x_436 = lean_ctor_get(x_429, 0);
lean_inc(x_436);
lean_dec(x_429);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_437 = l_Lean_Meta_isInductivePredicate(x_435, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; uint8_t x_439; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_unbox(x_438);
lean_dec(x_438);
if (x_439 == 0)
{
uint8_t x_440; 
lean_dec(x_436);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_440 = !lean_is_exclusive(x_437);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_437, 0);
lean_dec(x_441);
x_442 = lean_box(0);
lean_ctor_set(x_437, 0, x_442);
return x_437;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_437, 1);
lean_inc(x_443);
lean_dec(x_437);
x_444 = lean_box(0);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_443);
return x_445;
}
}
else
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_437, 1);
lean_inc(x_446);
lean_dec(x_437);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_436);
lean_inc(x_1);
x_447 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_436, x_7, x_8, x_9, x_10, x_446);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; lean_object* x_457; lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_box(0);
lean_inc(x_7);
x_452 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_450, x_451, x_7, x_8, x_9, x_10, x_449);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_491 = lean_st_ref_get(x_10, x_454);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_492, 3);
lean_inc(x_493);
lean_dec(x_492);
x_494 = lean_ctor_get_uint8(x_493, sizeof(void*)*1);
lean_dec(x_493);
if (x_494 == 0)
{
lean_object* x_495; uint8_t x_496; 
x_495 = lean_ctor_get(x_491, 1);
lean_inc(x_495);
lean_dec(x_491);
x_496 = 0;
x_456 = x_496;
x_457 = x_495;
goto block_490;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
x_497 = lean_ctor_get(x_491, 1);
lean_inc(x_497);
lean_dec(x_491);
x_498 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_455, x_7, x_8, x_9, x_10, x_497);
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_501 = lean_unbox(x_499);
lean_dec(x_499);
x_456 = x_501;
x_457 = x_500;
goto block_490;
}
block_490:
{
if (x_456 == 0)
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_box(0);
x_459 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_453, x_455, x_1, x_436, x_458, x_7, x_8, x_9, x_10, x_457);
if (lean_obj_tag(x_459) == 0)
{
return x_459;
}
else
{
uint8_t x_460; 
x_460 = !lean_is_exclusive(x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_459, 0);
lean_dec(x_461);
x_462 = lean_box(0);
lean_ctor_set_tag(x_459, 0);
lean_ctor_set(x_459, 0, x_462);
return x_459;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_459, 1);
lean_inc(x_463);
lean_dec(x_459);
x_464 = lean_box(0);
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_463);
return x_465;
}
}
}
else
{
lean_object* x_466; lean_object* x_467; 
lean_inc(x_453);
x_466 = l_Lean_Expr_mvarId_x21(x_453);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_467 = l_Lean_Meta_ppGoal(x_466, x_7, x_8, x_9, x_10, x_457);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
x_470 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_470, 0, x_468);
x_471 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_472 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_470);
x_473 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_471);
x_474 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_455, x_473, x_7, x_8, x_9, x_10, x_469);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
x_477 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_453, x_455, x_1, x_436, x_475, x_7, x_8, x_9, x_10, x_476);
if (lean_obj_tag(x_477) == 0)
{
return x_477;
}
else
{
uint8_t x_478; 
x_478 = !lean_is_exclusive(x_477);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; 
x_479 = lean_ctor_get(x_477, 0);
lean_dec(x_479);
x_480 = lean_box(0);
lean_ctor_set_tag(x_477, 0);
lean_ctor_set(x_477, 0, x_480);
return x_477;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_477, 1);
lean_inc(x_481);
lean_dec(x_477);
x_482 = lean_box(0);
x_483 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_481);
return x_483;
}
}
}
else
{
uint8_t x_484; 
lean_dec(x_453);
lean_dec(x_436);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_484 = !lean_is_exclusive(x_467);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_467, 0);
lean_dec(x_485);
x_486 = lean_box(0);
lean_ctor_set_tag(x_467, 0);
lean_ctor_set(x_467, 0, x_486);
return x_467;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_467, 1);
lean_inc(x_487);
lean_dec(x_467);
x_488 = lean_box(0);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_487);
return x_489;
}
}
}
}
}
else
{
uint8_t x_502; 
lean_dec(x_436);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_502 = !lean_is_exclusive(x_447);
if (x_502 == 0)
{
return x_447;
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_503 = lean_ctor_get(x_447, 0);
x_504 = lean_ctor_get(x_447, 1);
lean_inc(x_504);
lean_inc(x_503);
lean_dec(x_447);
x_505 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
return x_505;
}
}
}
}
else
{
uint8_t x_506; 
lean_dec(x_436);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_506 = !lean_is_exclusive(x_437);
if (x_506 == 0)
{
return x_437;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_437, 0);
x_508 = lean_ctor_get(x_437, 1);
lean_inc(x_508);
lean_inc(x_507);
lean_dec(x_437);
x_509 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
return x_509;
}
}
}
}
}
case 7:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
lean_dec(x_6);
lean_dec(x_5);
x_510 = lean_unsigned_to_nat(0u);
x_511 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_510);
x_512 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; 
lean_dec(x_511);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_513 = lean_box(0);
x_514 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_514, 0, x_513);
lean_ctor_set(x_514, 1, x_11);
return x_514;
}
else
{
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_515; lean_object* x_516; 
lean_dec(x_512);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_515 = lean_box(0);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_11);
return x_516;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_512, 0);
lean_inc(x_517);
lean_dec(x_512);
x_518 = lean_ctor_get(x_511, 0);
lean_inc(x_518);
lean_dec(x_511);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_519 = l_Lean_Meta_isInductivePredicate(x_517, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; uint8_t x_521; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_unbox(x_520);
lean_dec(x_520);
if (x_521 == 0)
{
uint8_t x_522; 
lean_dec(x_518);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_522 = !lean_is_exclusive(x_519);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; 
x_523 = lean_ctor_get(x_519, 0);
lean_dec(x_523);
x_524 = lean_box(0);
lean_ctor_set(x_519, 0, x_524);
return x_519;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_525 = lean_ctor_get(x_519, 1);
lean_inc(x_525);
lean_dec(x_519);
x_526 = lean_box(0);
x_527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_527, 0, x_526);
lean_ctor_set(x_527, 1, x_525);
return x_527;
}
}
else
{
lean_object* x_528; lean_object* x_529; 
x_528 = lean_ctor_get(x_519, 1);
lean_inc(x_528);
lean_dec(x_519);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_518);
lean_inc(x_1);
x_529 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_518, x_7, x_8, x_9, x_10, x_528);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; lean_object* x_539; lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = lean_box(0);
lean_inc(x_7);
x_534 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_532, x_533, x_7, x_8, x_9, x_10, x_531);
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
lean_dec(x_534);
x_537 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_573 = lean_st_ref_get(x_10, x_536);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_574, 3);
lean_inc(x_575);
lean_dec(x_574);
x_576 = lean_ctor_get_uint8(x_575, sizeof(void*)*1);
lean_dec(x_575);
if (x_576 == 0)
{
lean_object* x_577; uint8_t x_578; 
x_577 = lean_ctor_get(x_573, 1);
lean_inc(x_577);
lean_dec(x_573);
x_578 = 0;
x_538 = x_578;
x_539 = x_577;
goto block_572;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; 
x_579 = lean_ctor_get(x_573, 1);
lean_inc(x_579);
lean_dec(x_573);
x_580 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_537, x_7, x_8, x_9, x_10, x_579);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_580, 1);
lean_inc(x_582);
lean_dec(x_580);
x_583 = lean_unbox(x_581);
lean_dec(x_581);
x_538 = x_583;
x_539 = x_582;
goto block_572;
}
block_572:
{
if (x_538 == 0)
{
lean_object* x_540; lean_object* x_541; 
x_540 = lean_box(0);
x_541 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_535, x_537, x_1, x_518, x_540, x_7, x_8, x_9, x_10, x_539);
if (lean_obj_tag(x_541) == 0)
{
return x_541;
}
else
{
uint8_t x_542; 
x_542 = !lean_is_exclusive(x_541);
if (x_542 == 0)
{
lean_object* x_543; lean_object* x_544; 
x_543 = lean_ctor_get(x_541, 0);
lean_dec(x_543);
x_544 = lean_box(0);
lean_ctor_set_tag(x_541, 0);
lean_ctor_set(x_541, 0, x_544);
return x_541;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_545 = lean_ctor_get(x_541, 1);
lean_inc(x_545);
lean_dec(x_541);
x_546 = lean_box(0);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_545);
return x_547;
}
}
}
else
{
lean_object* x_548; lean_object* x_549; 
lean_inc(x_535);
x_548 = l_Lean_Expr_mvarId_x21(x_535);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_549 = l_Lean_Meta_ppGoal(x_548, x_7, x_8, x_9, x_10, x_539);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
x_552 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_552, 0, x_550);
x_553 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_554 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_552);
x_555 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_555, 0, x_554);
lean_ctor_set(x_555, 1, x_553);
x_556 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_537, x_555, x_7, x_8, x_9, x_10, x_551);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_535, x_537, x_1, x_518, x_557, x_7, x_8, x_9, x_10, x_558);
if (lean_obj_tag(x_559) == 0)
{
return x_559;
}
else
{
uint8_t x_560; 
x_560 = !lean_is_exclusive(x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_559, 0);
lean_dec(x_561);
x_562 = lean_box(0);
lean_ctor_set_tag(x_559, 0);
lean_ctor_set(x_559, 0, x_562);
return x_559;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_559, 1);
lean_inc(x_563);
lean_dec(x_559);
x_564 = lean_box(0);
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_564);
lean_ctor_set(x_565, 1, x_563);
return x_565;
}
}
}
else
{
uint8_t x_566; 
lean_dec(x_535);
lean_dec(x_518);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_566 = !lean_is_exclusive(x_549);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_549, 0);
lean_dec(x_567);
x_568 = lean_box(0);
lean_ctor_set_tag(x_549, 0);
lean_ctor_set(x_549, 0, x_568);
return x_549;
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_569 = lean_ctor_get(x_549, 1);
lean_inc(x_569);
lean_dec(x_549);
x_570 = lean_box(0);
x_571 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_571, 0, x_570);
lean_ctor_set(x_571, 1, x_569);
return x_571;
}
}
}
}
}
else
{
uint8_t x_584; 
lean_dec(x_518);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_584 = !lean_is_exclusive(x_529);
if (x_584 == 0)
{
return x_529;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_529, 0);
x_586 = lean_ctor_get(x_529, 1);
lean_inc(x_586);
lean_inc(x_585);
lean_dec(x_529);
x_587 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
return x_587;
}
}
}
}
else
{
uint8_t x_588; 
lean_dec(x_518);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_588 = !lean_is_exclusive(x_519);
if (x_588 == 0)
{
return x_519;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_519, 0);
x_590 = lean_ctor_get(x_519, 1);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_519);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
return x_591;
}
}
}
}
}
case 8:
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
lean_dec(x_6);
lean_dec(x_5);
x_592 = lean_unsigned_to_nat(0u);
x_593 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_592);
x_594 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; 
lean_dec(x_593);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_595 = lean_box(0);
x_596 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_596, 0, x_595);
lean_ctor_set(x_596, 1, x_11);
return x_596;
}
else
{
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_597; lean_object* x_598; 
lean_dec(x_594);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_597 = lean_box(0);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_11);
return x_598;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = lean_ctor_get(x_594, 0);
lean_inc(x_599);
lean_dec(x_594);
x_600 = lean_ctor_get(x_593, 0);
lean_inc(x_600);
lean_dec(x_593);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_601 = l_Lean_Meta_isInductivePredicate(x_599, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; uint8_t x_603; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_unbox(x_602);
lean_dec(x_602);
if (x_603 == 0)
{
uint8_t x_604; 
lean_dec(x_600);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_604 = !lean_is_exclusive(x_601);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_601, 0);
lean_dec(x_605);
x_606 = lean_box(0);
lean_ctor_set(x_601, 0, x_606);
return x_601;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_601, 1);
lean_inc(x_607);
lean_dec(x_601);
x_608 = lean_box(0);
x_609 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_607);
return x_609;
}
}
else
{
lean_object* x_610; lean_object* x_611; 
x_610 = lean_ctor_get(x_601, 1);
lean_inc(x_610);
lean_dec(x_601);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_600);
lean_inc(x_1);
x_611 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_600, x_7, x_8, x_9, x_10, x_610);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; uint8_t x_620; lean_object* x_621; lean_object* x_655; lean_object* x_656; lean_object* x_657; uint8_t x_658; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_611, 1);
lean_inc(x_613);
lean_dec(x_611);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = lean_box(0);
lean_inc(x_7);
x_616 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_614, x_615, x_7, x_8, x_9, x_10, x_613);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_616, 1);
lean_inc(x_618);
lean_dec(x_616);
x_619 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_655 = lean_st_ref_get(x_10, x_618);
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_656, 3);
lean_inc(x_657);
lean_dec(x_656);
x_658 = lean_ctor_get_uint8(x_657, sizeof(void*)*1);
lean_dec(x_657);
if (x_658 == 0)
{
lean_object* x_659; uint8_t x_660; 
x_659 = lean_ctor_get(x_655, 1);
lean_inc(x_659);
lean_dec(x_655);
x_660 = 0;
x_620 = x_660;
x_621 = x_659;
goto block_654;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_661 = lean_ctor_get(x_655, 1);
lean_inc(x_661);
lean_dec(x_655);
x_662 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_619, x_7, x_8, x_9, x_10, x_661);
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_662, 1);
lean_inc(x_664);
lean_dec(x_662);
x_665 = lean_unbox(x_663);
lean_dec(x_663);
x_620 = x_665;
x_621 = x_664;
goto block_654;
}
block_654:
{
if (x_620 == 0)
{
lean_object* x_622; lean_object* x_623; 
x_622 = lean_box(0);
x_623 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_617, x_619, x_1, x_600, x_622, x_7, x_8, x_9, x_10, x_621);
if (lean_obj_tag(x_623) == 0)
{
return x_623;
}
else
{
uint8_t x_624; 
x_624 = !lean_is_exclusive(x_623);
if (x_624 == 0)
{
lean_object* x_625; lean_object* x_626; 
x_625 = lean_ctor_get(x_623, 0);
lean_dec(x_625);
x_626 = lean_box(0);
lean_ctor_set_tag(x_623, 0);
lean_ctor_set(x_623, 0, x_626);
return x_623;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = lean_ctor_get(x_623, 1);
lean_inc(x_627);
lean_dec(x_623);
x_628 = lean_box(0);
x_629 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_627);
return x_629;
}
}
}
else
{
lean_object* x_630; lean_object* x_631; 
lean_inc(x_617);
x_630 = l_Lean_Expr_mvarId_x21(x_617);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_631 = l_Lean_Meta_ppGoal(x_630, x_7, x_8, x_9, x_10, x_621);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
lean_dec(x_631);
x_634 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_634, 0, x_632);
x_635 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_636 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_634);
x_637 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_635);
x_638 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_619, x_637, x_7, x_8, x_9, x_10, x_633);
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
x_641 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_617, x_619, x_1, x_600, x_639, x_7, x_8, x_9, x_10, x_640);
if (lean_obj_tag(x_641) == 0)
{
return x_641;
}
else
{
uint8_t x_642; 
x_642 = !lean_is_exclusive(x_641);
if (x_642 == 0)
{
lean_object* x_643; lean_object* x_644; 
x_643 = lean_ctor_get(x_641, 0);
lean_dec(x_643);
x_644 = lean_box(0);
lean_ctor_set_tag(x_641, 0);
lean_ctor_set(x_641, 0, x_644);
return x_641;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_645 = lean_ctor_get(x_641, 1);
lean_inc(x_645);
lean_dec(x_641);
x_646 = lean_box(0);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_645);
return x_647;
}
}
}
else
{
uint8_t x_648; 
lean_dec(x_617);
lean_dec(x_600);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_648 = !lean_is_exclusive(x_631);
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; 
x_649 = lean_ctor_get(x_631, 0);
lean_dec(x_649);
x_650 = lean_box(0);
lean_ctor_set_tag(x_631, 0);
lean_ctor_set(x_631, 0, x_650);
return x_631;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_631, 1);
lean_inc(x_651);
lean_dec(x_631);
x_652 = lean_box(0);
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
}
}
}
else
{
uint8_t x_666; 
lean_dec(x_600);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_666 = !lean_is_exclusive(x_611);
if (x_666 == 0)
{
return x_611;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_667 = lean_ctor_get(x_611, 0);
x_668 = lean_ctor_get(x_611, 1);
lean_inc(x_668);
lean_inc(x_667);
lean_dec(x_611);
x_669 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_669, 0, x_667);
lean_ctor_set(x_669, 1, x_668);
return x_669;
}
}
}
}
else
{
uint8_t x_670; 
lean_dec(x_600);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_670 = !lean_is_exclusive(x_601);
if (x_670 == 0)
{
return x_601;
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = lean_ctor_get(x_601, 0);
x_672 = lean_ctor_get(x_601, 1);
lean_inc(x_672);
lean_inc(x_671);
lean_dec(x_601);
x_673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_673, 0, x_671);
lean_ctor_set(x_673, 1, x_672);
return x_673;
}
}
}
}
}
case 9:
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_6);
lean_dec(x_5);
x_674 = lean_unsigned_to_nat(0u);
x_675 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_674);
x_676 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; 
lean_dec(x_675);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_677 = lean_box(0);
x_678 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_678, 0, x_677);
lean_ctor_set(x_678, 1, x_11);
return x_678;
}
else
{
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_676);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_679 = lean_box(0);
x_680 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_11);
return x_680;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_676, 0);
lean_inc(x_681);
lean_dec(x_676);
x_682 = lean_ctor_get(x_675, 0);
lean_inc(x_682);
lean_dec(x_675);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_683 = l_Lean_Meta_isInductivePredicate(x_681, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; uint8_t x_685; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_unbox(x_684);
lean_dec(x_684);
if (x_685 == 0)
{
uint8_t x_686; 
lean_dec(x_682);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_686 = !lean_is_exclusive(x_683);
if (x_686 == 0)
{
lean_object* x_687; lean_object* x_688; 
x_687 = lean_ctor_get(x_683, 0);
lean_dec(x_687);
x_688 = lean_box(0);
lean_ctor_set(x_683, 0, x_688);
return x_683;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_689 = lean_ctor_get(x_683, 1);
lean_inc(x_689);
lean_dec(x_683);
x_690 = lean_box(0);
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_689);
return x_691;
}
}
else
{
lean_object* x_692; lean_object* x_693; 
x_692 = lean_ctor_get(x_683, 1);
lean_inc(x_692);
lean_dec(x_683);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_682);
lean_inc(x_1);
x_693 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_682, x_7, x_8, x_9, x_10, x_692);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; lean_object* x_703; lean_object* x_737; lean_object* x_738; lean_object* x_739; uint8_t x_740; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
lean_dec(x_693);
x_696 = lean_ctor_get(x_694, 1);
lean_inc(x_696);
lean_dec(x_694);
x_697 = lean_box(0);
lean_inc(x_7);
x_698 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_696, x_697, x_7, x_8, x_9, x_10, x_695);
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_698, 1);
lean_inc(x_700);
lean_dec(x_698);
x_701 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_737 = lean_st_ref_get(x_10, x_700);
x_738 = lean_ctor_get(x_737, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_738, 3);
lean_inc(x_739);
lean_dec(x_738);
x_740 = lean_ctor_get_uint8(x_739, sizeof(void*)*1);
lean_dec(x_739);
if (x_740 == 0)
{
lean_object* x_741; uint8_t x_742; 
x_741 = lean_ctor_get(x_737, 1);
lean_inc(x_741);
lean_dec(x_737);
x_742 = 0;
x_702 = x_742;
x_703 = x_741;
goto block_736;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; 
x_743 = lean_ctor_get(x_737, 1);
lean_inc(x_743);
lean_dec(x_737);
x_744 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_701, x_7, x_8, x_9, x_10, x_743);
x_745 = lean_ctor_get(x_744, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_744, 1);
lean_inc(x_746);
lean_dec(x_744);
x_747 = lean_unbox(x_745);
lean_dec(x_745);
x_702 = x_747;
x_703 = x_746;
goto block_736;
}
block_736:
{
if (x_702 == 0)
{
lean_object* x_704; lean_object* x_705; 
x_704 = lean_box(0);
x_705 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_699, x_701, x_1, x_682, x_704, x_7, x_8, x_9, x_10, x_703);
if (lean_obj_tag(x_705) == 0)
{
return x_705;
}
else
{
uint8_t x_706; 
x_706 = !lean_is_exclusive(x_705);
if (x_706 == 0)
{
lean_object* x_707; lean_object* x_708; 
x_707 = lean_ctor_get(x_705, 0);
lean_dec(x_707);
x_708 = lean_box(0);
lean_ctor_set_tag(x_705, 0);
lean_ctor_set(x_705, 0, x_708);
return x_705;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_705, 1);
lean_inc(x_709);
lean_dec(x_705);
x_710 = lean_box(0);
x_711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_711, 0, x_710);
lean_ctor_set(x_711, 1, x_709);
return x_711;
}
}
}
else
{
lean_object* x_712; lean_object* x_713; 
lean_inc(x_699);
x_712 = l_Lean_Expr_mvarId_x21(x_699);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_713 = l_Lean_Meta_ppGoal(x_712, x_7, x_8, x_9, x_10, x_703);
if (lean_obj_tag(x_713) == 0)
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_714 = lean_ctor_get(x_713, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec(x_713);
x_716 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_716, 0, x_714);
x_717 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_718 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_716);
x_719 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_717);
x_720 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_701, x_719, x_7, x_8, x_9, x_10, x_715);
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec(x_720);
x_723 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_699, x_701, x_1, x_682, x_721, x_7, x_8, x_9, x_10, x_722);
if (lean_obj_tag(x_723) == 0)
{
return x_723;
}
else
{
uint8_t x_724; 
x_724 = !lean_is_exclusive(x_723);
if (x_724 == 0)
{
lean_object* x_725; lean_object* x_726; 
x_725 = lean_ctor_get(x_723, 0);
lean_dec(x_725);
x_726 = lean_box(0);
lean_ctor_set_tag(x_723, 0);
lean_ctor_set(x_723, 0, x_726);
return x_723;
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_727 = lean_ctor_get(x_723, 1);
lean_inc(x_727);
lean_dec(x_723);
x_728 = lean_box(0);
x_729 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_729, 0, x_728);
lean_ctor_set(x_729, 1, x_727);
return x_729;
}
}
}
else
{
uint8_t x_730; 
lean_dec(x_699);
lean_dec(x_682);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_730 = !lean_is_exclusive(x_713);
if (x_730 == 0)
{
lean_object* x_731; lean_object* x_732; 
x_731 = lean_ctor_get(x_713, 0);
lean_dec(x_731);
x_732 = lean_box(0);
lean_ctor_set_tag(x_713, 0);
lean_ctor_set(x_713, 0, x_732);
return x_713;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_733 = lean_ctor_get(x_713, 1);
lean_inc(x_733);
lean_dec(x_713);
x_734 = lean_box(0);
x_735 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set(x_735, 1, x_733);
return x_735;
}
}
}
}
}
else
{
uint8_t x_748; 
lean_dec(x_682);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_748 = !lean_is_exclusive(x_693);
if (x_748 == 0)
{
return x_693;
}
else
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_749 = lean_ctor_get(x_693, 0);
x_750 = lean_ctor_get(x_693, 1);
lean_inc(x_750);
lean_inc(x_749);
lean_dec(x_693);
x_751 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
return x_751;
}
}
}
}
else
{
uint8_t x_752; 
lean_dec(x_682);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_752 = !lean_is_exclusive(x_683);
if (x_752 == 0)
{
return x_683;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_683, 0);
x_754 = lean_ctor_get(x_683, 1);
lean_inc(x_754);
lean_inc(x_753);
lean_dec(x_683);
x_755 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
return x_755;
}
}
}
}
}
case 10:
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
lean_dec(x_6);
lean_dec(x_5);
x_756 = lean_unsigned_to_nat(0u);
x_757 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_756);
x_758 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_758) == 0)
{
lean_object* x_759; lean_object* x_760; 
lean_dec(x_757);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_759 = lean_box(0);
x_760 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_11);
return x_760;
}
else
{
if (lean_obj_tag(x_757) == 0)
{
lean_object* x_761; lean_object* x_762; 
lean_dec(x_758);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_761 = lean_box(0);
x_762 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set(x_762, 1, x_11);
return x_762;
}
else
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_763 = lean_ctor_get(x_758, 0);
lean_inc(x_763);
lean_dec(x_758);
x_764 = lean_ctor_get(x_757, 0);
lean_inc(x_764);
lean_dec(x_757);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_765 = l_Lean_Meta_isInductivePredicate(x_763, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; uint8_t x_767; 
x_766 = lean_ctor_get(x_765, 0);
lean_inc(x_766);
x_767 = lean_unbox(x_766);
lean_dec(x_766);
if (x_767 == 0)
{
uint8_t x_768; 
lean_dec(x_764);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_768 = !lean_is_exclusive(x_765);
if (x_768 == 0)
{
lean_object* x_769; lean_object* x_770; 
x_769 = lean_ctor_get(x_765, 0);
lean_dec(x_769);
x_770 = lean_box(0);
lean_ctor_set(x_765, 0, x_770);
return x_765;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_765, 1);
lean_inc(x_771);
lean_dec(x_765);
x_772 = lean_box(0);
x_773 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_773, 0, x_772);
lean_ctor_set(x_773, 1, x_771);
return x_773;
}
}
else
{
lean_object* x_774; lean_object* x_775; 
x_774 = lean_ctor_get(x_765, 1);
lean_inc(x_774);
lean_dec(x_765);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_764);
lean_inc(x_1);
x_775 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_764, x_7, x_8, x_9, x_10, x_774);
if (lean_obj_tag(x_775) == 0)
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; uint8_t x_784; lean_object* x_785; lean_object* x_819; lean_object* x_820; lean_object* x_821; uint8_t x_822; 
x_776 = lean_ctor_get(x_775, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_775, 1);
lean_inc(x_777);
lean_dec(x_775);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
lean_dec(x_776);
x_779 = lean_box(0);
lean_inc(x_7);
x_780 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_778, x_779, x_7, x_8, x_9, x_10, x_777);
x_781 = lean_ctor_get(x_780, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_780, 1);
lean_inc(x_782);
lean_dec(x_780);
x_783 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_819 = lean_st_ref_get(x_10, x_782);
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_ctor_get(x_820, 3);
lean_inc(x_821);
lean_dec(x_820);
x_822 = lean_ctor_get_uint8(x_821, sizeof(void*)*1);
lean_dec(x_821);
if (x_822 == 0)
{
lean_object* x_823; uint8_t x_824; 
x_823 = lean_ctor_get(x_819, 1);
lean_inc(x_823);
lean_dec(x_819);
x_824 = 0;
x_784 = x_824;
x_785 = x_823;
goto block_818;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; uint8_t x_829; 
x_825 = lean_ctor_get(x_819, 1);
lean_inc(x_825);
lean_dec(x_819);
x_826 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_783, x_7, x_8, x_9, x_10, x_825);
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
lean_dec(x_826);
x_829 = lean_unbox(x_827);
lean_dec(x_827);
x_784 = x_829;
x_785 = x_828;
goto block_818;
}
block_818:
{
if (x_784 == 0)
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_box(0);
x_787 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_781, x_783, x_1, x_764, x_786, x_7, x_8, x_9, x_10, x_785);
if (lean_obj_tag(x_787) == 0)
{
return x_787;
}
else
{
uint8_t x_788; 
x_788 = !lean_is_exclusive(x_787);
if (x_788 == 0)
{
lean_object* x_789; lean_object* x_790; 
x_789 = lean_ctor_get(x_787, 0);
lean_dec(x_789);
x_790 = lean_box(0);
lean_ctor_set_tag(x_787, 0);
lean_ctor_set(x_787, 0, x_790);
return x_787;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_787, 1);
lean_inc(x_791);
lean_dec(x_787);
x_792 = lean_box(0);
x_793 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set(x_793, 1, x_791);
return x_793;
}
}
}
else
{
lean_object* x_794; lean_object* x_795; 
lean_inc(x_781);
x_794 = l_Lean_Expr_mvarId_x21(x_781);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_795 = l_Lean_Meta_ppGoal(x_794, x_7, x_8, x_9, x_10, x_785);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; 
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
lean_dec(x_795);
x_798 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_798, 0, x_796);
x_799 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_800 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_798);
x_801 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_799);
x_802 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_783, x_801, x_7, x_8, x_9, x_10, x_797);
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_802, 1);
lean_inc(x_804);
lean_dec(x_802);
x_805 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_781, x_783, x_1, x_764, x_803, x_7, x_8, x_9, x_10, x_804);
if (lean_obj_tag(x_805) == 0)
{
return x_805;
}
else
{
uint8_t x_806; 
x_806 = !lean_is_exclusive(x_805);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; 
x_807 = lean_ctor_get(x_805, 0);
lean_dec(x_807);
x_808 = lean_box(0);
lean_ctor_set_tag(x_805, 0);
lean_ctor_set(x_805, 0, x_808);
return x_805;
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_805, 1);
lean_inc(x_809);
lean_dec(x_805);
x_810 = lean_box(0);
x_811 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_809);
return x_811;
}
}
}
else
{
uint8_t x_812; 
lean_dec(x_781);
lean_dec(x_764);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_812 = !lean_is_exclusive(x_795);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; 
x_813 = lean_ctor_get(x_795, 0);
lean_dec(x_813);
x_814 = lean_box(0);
lean_ctor_set_tag(x_795, 0);
lean_ctor_set(x_795, 0, x_814);
return x_795;
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_815 = lean_ctor_get(x_795, 1);
lean_inc(x_815);
lean_dec(x_795);
x_816 = lean_box(0);
x_817 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_817, 0, x_816);
lean_ctor_set(x_817, 1, x_815);
return x_817;
}
}
}
}
}
else
{
uint8_t x_830; 
lean_dec(x_764);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_830 = !lean_is_exclusive(x_775);
if (x_830 == 0)
{
return x_775;
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_831 = lean_ctor_get(x_775, 0);
x_832 = lean_ctor_get(x_775, 1);
lean_inc(x_832);
lean_inc(x_831);
lean_dec(x_775);
x_833 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_833, 0, x_831);
lean_ctor_set(x_833, 1, x_832);
return x_833;
}
}
}
}
else
{
uint8_t x_834; 
lean_dec(x_764);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_834 = !lean_is_exclusive(x_765);
if (x_834 == 0)
{
return x_765;
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_835 = lean_ctor_get(x_765, 0);
x_836 = lean_ctor_get(x_765, 1);
lean_inc(x_836);
lean_inc(x_835);
lean_dec(x_765);
x_837 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_837, 0, x_835);
lean_ctor_set(x_837, 1, x_836);
return x_837;
}
}
}
}
}
default: 
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; 
lean_dec(x_6);
lean_dec(x_5);
x_838 = lean_unsigned_to_nat(0u);
x_839 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_3, x_838);
x_840 = l_Lean_Expr_constName_x3f(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_840) == 0)
{
lean_object* x_841; lean_object* x_842; 
lean_dec(x_839);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_841 = lean_box(0);
x_842 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_842, 0, x_841);
lean_ctor_set(x_842, 1, x_11);
return x_842;
}
else
{
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_843; lean_object* x_844; 
lean_dec(x_840);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_843 = lean_box(0);
x_844 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_844, 0, x_843);
lean_ctor_set(x_844, 1, x_11);
return x_844;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_845 = lean_ctor_get(x_840, 0);
lean_inc(x_845);
lean_dec(x_840);
x_846 = lean_ctor_get(x_839, 0);
lean_inc(x_846);
lean_dec(x_839);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_847 = l_Lean_Meta_isInductivePredicate(x_845, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; uint8_t x_849; 
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
x_849 = lean_unbox(x_848);
lean_dec(x_848);
if (x_849 == 0)
{
uint8_t x_850; 
lean_dec(x_846);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_850 = !lean_is_exclusive(x_847);
if (x_850 == 0)
{
lean_object* x_851; lean_object* x_852; 
x_851 = lean_ctor_get(x_847, 0);
lean_dec(x_851);
x_852 = lean_box(0);
lean_ctor_set(x_847, 0, x_852);
return x_847;
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_853 = lean_ctor_get(x_847, 1);
lean_inc(x_853);
lean_dec(x_847);
x_854 = lean_box(0);
x_855 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_855, 0, x_854);
lean_ctor_set(x_855, 1, x_853);
return x_855;
}
}
else
{
lean_object* x_856; lean_object* x_857; 
x_856 = lean_ctor_get(x_847, 1);
lean_inc(x_856);
lean_dec(x_847);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_846);
lean_inc(x_1);
x_857 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_846, x_7, x_8, x_9, x_10, x_856);
if (lean_obj_tag(x_857) == 0)
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; uint8_t x_866; lean_object* x_867; lean_object* x_901; lean_object* x_902; lean_object* x_903; uint8_t x_904; 
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
lean_dec(x_857);
x_860 = lean_ctor_get(x_858, 1);
lean_inc(x_860);
lean_dec(x_858);
x_861 = lean_box(0);
lean_inc(x_7);
x_862 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_860, x_861, x_7, x_8, x_9, x_10, x_859);
x_863 = lean_ctor_get(x_862, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_862, 1);
lean_inc(x_864);
lean_dec(x_862);
x_865 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_901 = lean_st_ref_get(x_10, x_864);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_902, 3);
lean_inc(x_903);
lean_dec(x_902);
x_904 = lean_ctor_get_uint8(x_903, sizeof(void*)*1);
lean_dec(x_903);
if (x_904 == 0)
{
lean_object* x_905; uint8_t x_906; 
x_905 = lean_ctor_get(x_901, 1);
lean_inc(x_905);
lean_dec(x_901);
x_906 = 0;
x_866 = x_906;
x_867 = x_905;
goto block_900;
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; uint8_t x_911; 
x_907 = lean_ctor_get(x_901, 1);
lean_inc(x_907);
lean_dec(x_901);
x_908 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_865, x_7, x_8, x_9, x_10, x_907);
x_909 = lean_ctor_get(x_908, 0);
lean_inc(x_909);
x_910 = lean_ctor_get(x_908, 1);
lean_inc(x_910);
lean_dec(x_908);
x_911 = lean_unbox(x_909);
lean_dec(x_909);
x_866 = x_911;
x_867 = x_910;
goto block_900;
}
block_900:
{
if (x_866 == 0)
{
lean_object* x_868; lean_object* x_869; 
x_868 = lean_box(0);
x_869 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_863, x_865, x_1, x_846, x_868, x_7, x_8, x_9, x_10, x_867);
if (lean_obj_tag(x_869) == 0)
{
return x_869;
}
else
{
uint8_t x_870; 
x_870 = !lean_is_exclusive(x_869);
if (x_870 == 0)
{
lean_object* x_871; lean_object* x_872; 
x_871 = lean_ctor_get(x_869, 0);
lean_dec(x_871);
x_872 = lean_box(0);
lean_ctor_set_tag(x_869, 0);
lean_ctor_set(x_869, 0, x_872);
return x_869;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_869, 1);
lean_inc(x_873);
lean_dec(x_869);
x_874 = lean_box(0);
x_875 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_875, 0, x_874);
lean_ctor_set(x_875, 1, x_873);
return x_875;
}
}
}
else
{
lean_object* x_876; lean_object* x_877; 
lean_inc(x_863);
x_876 = l_Lean_Expr_mvarId_x21(x_863);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_877 = l_Lean_Meta_ppGoal(x_876, x_7, x_8, x_9, x_10, x_867);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_878 = lean_ctor_get(x_877, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_877, 1);
lean_inc(x_879);
lean_dec(x_877);
x_880 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_880, 0, x_878);
x_881 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_882 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_880);
x_883 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_883, 0, x_882);
lean_ctor_set(x_883, 1, x_881);
x_884 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_865, x_883, x_7, x_8, x_9, x_10, x_879);
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
x_887 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3(x_863, x_865, x_1, x_846, x_885, x_7, x_8, x_9, x_10, x_886);
if (lean_obj_tag(x_887) == 0)
{
return x_887;
}
else
{
uint8_t x_888; 
x_888 = !lean_is_exclusive(x_887);
if (x_888 == 0)
{
lean_object* x_889; lean_object* x_890; 
x_889 = lean_ctor_get(x_887, 0);
lean_dec(x_889);
x_890 = lean_box(0);
lean_ctor_set_tag(x_887, 0);
lean_ctor_set(x_887, 0, x_890);
return x_887;
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_891 = lean_ctor_get(x_887, 1);
lean_inc(x_891);
lean_dec(x_887);
x_892 = lean_box(0);
x_893 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_893, 0, x_892);
lean_ctor_set(x_893, 1, x_891);
return x_893;
}
}
}
else
{
uint8_t x_894; 
lean_dec(x_863);
lean_dec(x_846);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_894 = !lean_is_exclusive(x_877);
if (x_894 == 0)
{
lean_object* x_895; lean_object* x_896; 
x_895 = lean_ctor_get(x_877, 0);
lean_dec(x_895);
x_896 = lean_box(0);
lean_ctor_set_tag(x_877, 0);
lean_ctor_set(x_877, 0, x_896);
return x_877;
}
else
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; 
x_897 = lean_ctor_get(x_877, 1);
lean_inc(x_897);
lean_dec(x_877);
x_898 = lean_box(0);
x_899 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_899, 0, x_898);
lean_ctor_set(x_899, 1, x_897);
return x_899;
}
}
}
}
}
else
{
uint8_t x_912; 
lean_dec(x_846);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_912 = !lean_is_exclusive(x_857);
if (x_912 == 0)
{
return x_857;
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_913 = lean_ctor_get(x_857, 0);
x_914 = lean_ctor_get(x_857, 1);
lean_inc(x_914);
lean_inc(x_913);
lean_dec(x_857);
x_915 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_915, 0, x_913);
lean_ctor_set(x_915, 1, x_914);
return x_915;
}
}
}
}
else
{
uint8_t x_916; 
lean_dec(x_846);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_916 = !lean_is_exclusive(x_847);
if (x_916 == 0)
{
return x_847;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_917 = lean_ctor_get(x_847, 0);
x_918 = lean_ctor_get(x_847, 1);
lean_inc(x_918);
lean_inc(x_917);
lean_dec(x_847);
x_919 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_919, 0, x_917);
lean_ctor_set(x_919, 1, x_918);
return x_919;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = lean_array_uget(x_4, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_15);
x_16 = lean_infer_type(x_15, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_17, x_19);
x_21 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_20);
x_22 = lean_mk_array(x_20, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_20, x_23);
lean_dec(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1, x_2, x_15, x_17, x_22, x_24, x_8, x_9, x_10, x_11, x_18);
lean_dec(x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; size_t x_28; size_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 1;
x_29 = lean_usize_add(x_6, x_28);
lean_inc(x_3);
{
size_t _tmp_5 = x_29;
lean_object* _tmp_6 = x_3;
lean_object* _tmp_11 = x_27;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_25, 0);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_26);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_26);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_25, 0, x_36);
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_25, 0, x_41);
return x_25;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_25, 1);
lean_inc(x_42);
lean_dec(x_25);
x_43 = lean_ctor_get(x_26, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 x_44 = x_26;
} else {
 lean_dec_ref(x_26);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_42);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_25);
if (x_50 == 0)
{
return x_25;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_25, 0);
x_52 = lean_ctor_get(x_25, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_25);
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
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_16);
if (x_54 == 0)
{
return x_16;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_16, 0);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_16);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3;
lean_inc(x_1);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3(x_1, x_2, x_12, x_1, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_8);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_15;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_InfoCacheKey_instHashableInfoCacheKey___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instBEqExpr;
x_2 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_instHashableExpr;
x_2 = lean_alloc_closure((void*)(l_instHashableProd___rarg___boxed), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__5;
x_2 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__7;
x_3 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__8;
x_4 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__11;
x_5 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_mk_cases_on(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_throwKernelException___at_Lean_Meta_evalExprCore___spec__3(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_4);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_st_ref_take(x_5, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_16, 4);
lean_dec(x_19);
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__4;
lean_ctor_set(x_16, 4, x_21);
lean_ctor_set(x_16, 0, x_14);
x_22 = lean_st_ref_set(x_5, x_16, x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_st_ref_get(x_5, x_23);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_take(x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
x_31 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12;
lean_ctor_set(x_27, 1, x_31);
x_32 = lean_st_ref_set(x_3, x_27, x_28);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 2);
x_41 = lean_ctor_get(x_27, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_27);
x_42 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12;
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_40);
lean_ctor_set(x_43, 3, x_41);
x_44 = lean_st_ref_set(x_3, x_43, x_28);
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
x_47 = lean_box(0);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_49 = lean_ctor_get(x_16, 1);
x_50 = lean_ctor_get(x_16, 2);
x_51 = lean_ctor_get(x_16, 3);
x_52 = lean_ctor_get(x_16, 5);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_16);
x_53 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__4;
x_54 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_54, 0, x_14);
lean_ctor_set(x_54, 1, x_49);
lean_ctor_set(x_54, 2, x_50);
lean_ctor_set(x_54, 3, x_51);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_54, 5, x_52);
x_55 = lean_st_ref_set(x_5, x_54, x_17);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_st_ref_get(x_5, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_st_ref_take(x_3, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 2);
lean_inc(x_63);
x_64 = lean_ctor_get(x_60, 3);
lean_inc(x_64);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 lean_ctor_release(x_60, 2);
 lean_ctor_release(x_60, 3);
 x_65 = x_60;
} else {
 lean_dec_ref(x_60);
 x_65 = lean_box(0);
}
x_66 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12;
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 4, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_63);
lean_ctor_set(x_67, 3, x_64);
x_68 = lean_st_ref_set(x_3, x_67, x_61);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_KernelException_toMessageData(x_1, x_7);
x_9 = l_Lean_throwError___at___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_st_ref_take(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_8, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__4;
lean_ctor_set(x_8, 4, x_13);
lean_ctor_set(x_8, 0, x_1);
x_14 = lean_st_ref_set(x_5, x_8, x_9);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_get(x_5, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_take(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_dec(x_22);
x_23 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12;
lean_ctor_set(x_19, 1, x_23);
x_24 = lean_st_ref_set(x_3, x_19, x_20);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 2);
x_33 = lean_ctor_get(x_19, 3);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_34 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12;
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_33);
x_36 = lean_st_ref_set(x_3, x_35, x_20);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_38 = x_36;
} else {
 lean_dec_ref(x_36);
 x_38 = lean_box(0);
}
x_39 = lean_box(0);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_41 = lean_ctor_get(x_8, 1);
x_42 = lean_ctor_get(x_8, 2);
x_43 = lean_ctor_get(x_8, 3);
x_44 = lean_ctor_get(x_8, 5);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_8);
x_45 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__4;
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_43);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_44);
x_47 = lean_st_ref_set(x_5, x_46, x_9);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_st_ref_get(x_5, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_take(x_3, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_52, 3);
lean_inc(x_56);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 x_57 = x_52;
} else {
 lean_dec_ref(x_52);
 x_57 = lean_box(0);
}
x_58 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12;
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 4, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_55);
lean_ctor_set(x_59, 3, x_56);
x_60 = lean_st_ref_set(x_3, x_59, x_53);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_62 = x_60;
} else {
 lean_dec_ref(x_60);
 x_62 = lean_box(0);
}
x_63 = lean_box(0);
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
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_IndPredBelow_mkBelow___spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_252; uint8_t x_253; 
x_252 = 2;
x_253 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_101_(x_3, x_252);
if (x_253 == 0)
{
lean_object* x_254; 
x_254 = lean_box(0);
x_9 = x_254;
goto block_251;
}
else
{
uint8_t x_255; 
lean_inc(x_2);
x_255 = l_Lean_MessageData_hasSyntheticSorry(x_2);
if (x_255 == 0)
{
lean_object* x_256; 
x_256 = lean_box(0);
x_9 = x_256;
goto block_251;
}
else
{
lean_object* x_257; lean_object* x_258; 
lean_dec(x_2);
x_257 = lean_box(0);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_8);
return x_258;
}
}
block_251:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_6, 5);
x_13 = lean_ctor_get(x_6, 6);
x_14 = lean_ctor_get(x_6, 7);
x_15 = l_Lean_replaceRef(x_1, x_12);
x_16 = 0;
x_17 = l_Lean_Syntax_getPos_x3f(x_15, x_16);
x_18 = l_Lean_Syntax_getTailPos_x3f(x_15, x_16);
if (lean_obj_tag(x_17) == 0)
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_19 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_FileMap_toPosition(x_11, x_22);
lean_inc(x_23);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_inc(x_14);
lean_inc(x_13);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_14);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
x_27 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
lean_inc(x_10);
x_28 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_28, 0, x_10);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set(x_28, 4, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*5, x_3);
x_29 = lean_st_ref_take(x_7, x_21);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_30, 5);
x_34 = l_Std_PersistentArray_push___rarg(x_33, x_28);
lean_ctor_set(x_30, 5, x_34);
x_35 = lean_st_ref_set(x_7, x_30, x_31);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
x_44 = lean_ctor_get(x_30, 2);
x_45 = lean_ctor_get(x_30, 3);
x_46 = lean_ctor_get(x_30, 4);
x_47 = lean_ctor_get(x_30, 5);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_48 = l_Std_PersistentArray_push___rarg(x_47, x_28);
x_49 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_43);
lean_ctor_set(x_49, 2, x_44);
lean_ctor_set(x_49, 3, x_45);
lean_ctor_set(x_49, 4, x_46);
lean_ctor_set(x_49, 5, x_48);
x_50 = lean_st_ref_set(x_7, x_49, x_31);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_box(0);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_18);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_56 = lean_ctor_get(x_18, 0);
x_57 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Lean_FileMap_toPosition(x_11, x_60);
x_62 = l_Lean_FileMap_toPosition(x_11, x_56);
lean_dec(x_56);
lean_ctor_set(x_18, 0, x_62);
lean_inc(x_14);
lean_inc(x_13);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_13);
lean_ctor_set(x_63, 1, x_14);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
x_65 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
lean_inc(x_10);
x_66 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_66, 0, x_10);
lean_ctor_set(x_66, 1, x_61);
lean_ctor_set(x_66, 2, x_18);
lean_ctor_set(x_66, 3, x_65);
lean_ctor_set(x_66, 4, x_64);
lean_ctor_set_uint8(x_66, sizeof(void*)*5, x_3);
x_67 = lean_st_ref_take(x_7, x_59);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_68, 5);
x_72 = l_Std_PersistentArray_push___rarg(x_71, x_66);
lean_ctor_set(x_68, 5, x_72);
x_73 = lean_st_ref_set(x_7, x_68, x_69);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_80 = lean_ctor_get(x_68, 0);
x_81 = lean_ctor_get(x_68, 1);
x_82 = lean_ctor_get(x_68, 2);
x_83 = lean_ctor_get(x_68, 3);
x_84 = lean_ctor_get(x_68, 4);
x_85 = lean_ctor_get(x_68, 5);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_68);
x_86 = l_Std_PersistentArray_push___rarg(x_85, x_66);
x_87 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_87, 0, x_80);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_82);
lean_ctor_set(x_87, 3, x_83);
lean_ctor_set(x_87, 4, x_84);
lean_ctor_set(x_87, 5, x_86);
x_88 = lean_st_ref_set(x_7, x_87, x_69);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_93 = lean_ctor_get(x_18, 0);
lean_inc(x_93);
lean_dec(x_18);
x_94 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_FileMap_toPosition(x_11, x_97);
x_99 = l_Lean_FileMap_toPosition(x_11, x_93);
lean_dec(x_93);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_inc(x_14);
lean_inc(x_13);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_13);
lean_ctor_set(x_101, 1, x_14);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_95);
x_103 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
lean_inc(x_10);
x_104 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_104, 0, x_10);
lean_ctor_set(x_104, 1, x_98);
lean_ctor_set(x_104, 2, x_100);
lean_ctor_set(x_104, 3, x_103);
lean_ctor_set(x_104, 4, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*5, x_3);
x_105 = lean_st_ref_take(x_7, x_96);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 3);
lean_inc(x_111);
x_112 = lean_ctor_get(x_106, 4);
lean_inc(x_112);
x_113 = lean_ctor_get(x_106, 5);
lean_inc(x_113);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 lean_ctor_release(x_106, 4);
 lean_ctor_release(x_106, 5);
 x_114 = x_106;
} else {
 lean_dec_ref(x_106);
 x_114 = lean_box(0);
}
x_115 = l_Std_PersistentArray_push___rarg(x_113, x_104);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 6, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_108);
lean_ctor_set(x_116, 1, x_109);
lean_ctor_set(x_116, 2, x_110);
lean_ctor_set(x_116, 3, x_111);
lean_ctor_set(x_116, 4, x_112);
lean_ctor_set(x_116, 5, x_115);
x_117 = lean_st_ref_set(x_7, x_116, x_107);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
x_120 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_118);
return x_121;
}
}
}
else
{
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_17);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_123 = lean_ctor_get(x_17, 0);
x_124 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_FileMap_toPosition(x_11, x_123);
lean_dec(x_123);
lean_inc(x_127);
lean_ctor_set(x_17, 0, x_127);
lean_inc(x_14);
lean_inc(x_13);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_13);
lean_ctor_set(x_128, 1, x_14);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
x_130 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
lean_inc(x_10);
x_131 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_131, 0, x_10);
lean_ctor_set(x_131, 1, x_127);
lean_ctor_set(x_131, 2, x_17);
lean_ctor_set(x_131, 3, x_130);
lean_ctor_set(x_131, 4, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*5, x_3);
x_132 = lean_st_ref_take(x_7, x_126);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = !lean_is_exclusive(x_133);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_136 = lean_ctor_get(x_133, 5);
x_137 = l_Std_PersistentArray_push___rarg(x_136, x_131);
lean_ctor_set(x_133, 5, x_137);
x_138 = lean_st_ref_set(x_7, x_133, x_134);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_138, 0);
lean_dec(x_140);
x_141 = lean_box(0);
lean_ctor_set(x_138, 0, x_141);
return x_138;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
lean_dec(x_138);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_145 = lean_ctor_get(x_133, 0);
x_146 = lean_ctor_get(x_133, 1);
x_147 = lean_ctor_get(x_133, 2);
x_148 = lean_ctor_get(x_133, 3);
x_149 = lean_ctor_get(x_133, 4);
x_150 = lean_ctor_get(x_133, 5);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_133);
x_151 = l_Std_PersistentArray_push___rarg(x_150, x_131);
x_152 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_146);
lean_ctor_set(x_152, 2, x_147);
lean_ctor_set(x_152, 3, x_148);
lean_ctor_set(x_152, 4, x_149);
lean_ctor_set(x_152, 5, x_151);
x_153 = lean_st_ref_set(x_7, x_152, x_134);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = lean_box(0);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_158 = lean_ctor_get(x_17, 0);
lean_inc(x_158);
lean_dec(x_17);
x_159 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Lean_FileMap_toPosition(x_11, x_158);
lean_dec(x_158);
lean_inc(x_162);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
lean_inc(x_14);
lean_inc(x_13);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_13);
lean_ctor_set(x_164, 1, x_14);
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_160);
x_166 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
lean_inc(x_10);
x_167 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_167, 0, x_10);
lean_ctor_set(x_167, 1, x_162);
lean_ctor_set(x_167, 2, x_163);
lean_ctor_set(x_167, 3, x_166);
lean_ctor_set(x_167, 4, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*5, x_3);
x_168 = lean_st_ref_take(x_7, x_161);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_169, 3);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 4);
lean_inc(x_175);
x_176 = lean_ctor_get(x_169, 5);
lean_inc(x_176);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 lean_ctor_release(x_169, 2);
 lean_ctor_release(x_169, 3);
 lean_ctor_release(x_169, 4);
 lean_ctor_release(x_169, 5);
 x_177 = x_169;
} else {
 lean_dec_ref(x_169);
 x_177 = lean_box(0);
}
x_178 = l_Std_PersistentArray_push___rarg(x_176, x_167);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 6, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_171);
lean_ctor_set(x_179, 1, x_172);
lean_ctor_set(x_179, 2, x_173);
lean_ctor_set(x_179, 3, x_174);
lean_ctor_set(x_179, 4, x_175);
lean_ctor_set(x_179, 5, x_178);
x_180 = lean_st_ref_set(x_7, x_179, x_170);
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_182 = x_180;
} else {
 lean_dec_ref(x_180);
 x_182 = lean_box(0);
}
x_183 = lean_box(0);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
return x_184;
}
}
else
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_ctor_get(x_17, 0);
lean_inc(x_185);
lean_dec(x_17);
x_186 = !lean_is_exclusive(x_18);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_187 = lean_ctor_get(x_18, 0);
x_188 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_FileMap_toPosition(x_11, x_185);
lean_dec(x_185);
x_192 = l_Lean_FileMap_toPosition(x_11, x_187);
lean_dec(x_187);
lean_ctor_set(x_18, 0, x_192);
lean_inc(x_14);
lean_inc(x_13);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_13);
lean_ctor_set(x_193, 1, x_14);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_189);
x_195 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
lean_inc(x_10);
x_196 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_196, 0, x_10);
lean_ctor_set(x_196, 1, x_191);
lean_ctor_set(x_196, 2, x_18);
lean_ctor_set(x_196, 3, x_195);
lean_ctor_set(x_196, 4, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*5, x_3);
x_197 = lean_st_ref_take(x_7, x_190);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
lean_dec(x_197);
x_200 = !lean_is_exclusive(x_198);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_201 = lean_ctor_get(x_198, 5);
x_202 = l_Std_PersistentArray_push___rarg(x_201, x_196);
lean_ctor_set(x_198, 5, x_202);
x_203 = lean_st_ref_set(x_7, x_198, x_199);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_203, 0);
lean_dec(x_205);
x_206 = lean_box(0);
lean_ctor_set(x_203, 0, x_206);
return x_203;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
lean_dec(x_203);
x_208 = lean_box(0);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_210 = lean_ctor_get(x_198, 0);
x_211 = lean_ctor_get(x_198, 1);
x_212 = lean_ctor_get(x_198, 2);
x_213 = lean_ctor_get(x_198, 3);
x_214 = lean_ctor_get(x_198, 4);
x_215 = lean_ctor_get(x_198, 5);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_198);
x_216 = l_Std_PersistentArray_push___rarg(x_215, x_196);
x_217 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_217, 0, x_210);
lean_ctor_set(x_217, 1, x_211);
lean_ctor_set(x_217, 2, x_212);
lean_ctor_set(x_217, 3, x_213);
lean_ctor_set(x_217, 4, x_214);
lean_ctor_set(x_217, 5, x_216);
x_218 = lean_st_ref_set(x_7, x_217, x_199);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
x_221 = lean_box(0);
if (lean_is_scalar(x_220)) {
 x_222 = lean_alloc_ctor(0, 2, 0);
} else {
 x_222 = x_220;
}
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_219);
return x_222;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_223 = lean_ctor_get(x_18, 0);
lean_inc(x_223);
lean_dec(x_18);
x_224 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_2, x_4, x_5, x_6, x_7, x_8);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_227 = l_Lean_FileMap_toPosition(x_11, x_185);
lean_dec(x_185);
x_228 = l_Lean_FileMap_toPosition(x_11, x_223);
lean_dec(x_223);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_228);
lean_inc(x_14);
lean_inc(x_13);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_13);
lean_ctor_set(x_230, 1, x_14);
x_231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_225);
x_232 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3;
lean_inc(x_10);
x_233 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_233, 0, x_10);
lean_ctor_set(x_233, 1, x_227);
lean_ctor_set(x_233, 2, x_229);
lean_ctor_set(x_233, 3, x_232);
lean_ctor_set(x_233, 4, x_231);
lean_ctor_set_uint8(x_233, sizeof(void*)*5, x_3);
x_234 = lean_st_ref_take(x_7, x_226);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_235, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
x_239 = lean_ctor_get(x_235, 2);
lean_inc(x_239);
x_240 = lean_ctor_get(x_235, 3);
lean_inc(x_240);
x_241 = lean_ctor_get(x_235, 4);
lean_inc(x_241);
x_242 = lean_ctor_get(x_235, 5);
lean_inc(x_242);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 lean_ctor_release(x_235, 2);
 lean_ctor_release(x_235, 3);
 lean_ctor_release(x_235, 4);
 lean_ctor_release(x_235, 5);
 x_243 = x_235;
} else {
 lean_dec_ref(x_235);
 x_243 = lean_box(0);
}
x_244 = l_Std_PersistentArray_push___rarg(x_242, x_233);
if (lean_is_scalar(x_243)) {
 x_245 = lean_alloc_ctor(0, 6, 0);
} else {
 x_245 = x_243;
}
lean_ctor_set(x_245, 0, x_237);
lean_ctor_set(x_245, 1, x_238);
lean_ctor_set(x_245, 2, x_239);
lean_ctor_set(x_245, 3, x_240);
lean_ctor_set(x_245, 4, x_241);
lean_ctor_set(x_245, 5, x_244);
x_246 = lean_st_ref_set(x_7, x_245, x_236);
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_248 = x_246;
} else {
 lean_dec_ref(x_246);
 x_248 = lean_box(0);
}
x_249 = lean_box(0);
if (lean_is_scalar(x_248)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_248;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_247);
return x_250;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_IndPredBelow_mkBelow___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 5);
lean_inc(x_8);
x_9 = l_Lean_logAt___at_Lean_Meta_IndPredBelow_mkBelow___spec__6(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_add_decl(x_11, x_1);
lean_dec(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_throwKernelException___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_setEnv___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(x_15, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_16;
}
}
}
static lean_object* _init_l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declaration uses 'sorry'", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 5);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Std_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; 
x_12 = 0;
lean_inc(x_1);
x_13 = l_Lean_Declaration_foldExprM___at_Lean_Declaration_hasSorry___spec__1(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___lambda__1(x_1, x_14, x_2, x_3, x_4, x_5, x_9);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3;
x_17 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_log___at_Lean_Meta_IndPredBelow_mkBelow___spec__5(x_16, x_17, x_2, x_3, x_4, x_5, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___lambda__1(x_1, x_19, x_2, x_3, x_4, x_5, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___lambda__1(x_1, x_22, x_2, x_3, x_4, x_5, x_9);
return x_23;
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("failed to prove brecOn for ", 27);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("\n", 1);
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_5, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_71; 
lean_dec(x_9);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_5, x_18);
lean_dec(x_5);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
lean_inc(x_1);
x_71 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl(x_1, x_6, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_74 = l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(x_72, x_10, x_11, x_12, x_13, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_77 = lean_box(0);
x_5 = x_19;
x_6 = x_76;
x_9 = x_77;
x_14 = x_75;
goto _start;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_20 = x_79;
x_21 = x_80;
goto block_70;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
lean_dec(x_71);
x_20 = x_81;
x_21 = x_82;
goto block_70;
}
block_70:
{
uint8_t x_22; lean_object* x_23; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_st_ref_get(x_13, x_21);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 3);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get_uint8(x_61, sizeof(void*)*1);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = 0;
x_22 = x_64;
x_23 = x_63;
goto block_58;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_dec(x_59);
lean_inc(x_2);
x_66 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_2, x_10, x_11, x_12, x_13, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unbox(x_67);
lean_dec(x_67);
x_22 = x_69;
x_23 = x_68;
goto block_58;
}
block_58:
{
if (x_22 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
x_24 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_25 = lean_box(0);
x_5 = x_19;
x_6 = x_24;
x_9 = x_25;
x_14 = x_23;
goto _start;
}
else
{
uint8_t x_27; lean_object* x_28; 
x_27 = lean_nat_dec_lt(x_6, x_4);
x_28 = l_Lean_Exception_toMessageData(x_20);
if (x_27 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4;
x_30 = l_panic___at___private_Init_Prelude_0__Lean_assembleParts___spec__1(x_29);
x_31 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__2;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__4;
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_28);
x_37 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_38 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_2);
x_39 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(x_2, x_38, x_10, x_11, x_12, x_13, x_23);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_42 = lean_box(0);
x_5 = x_19;
x_6 = x_41;
x_9 = x_42;
x_14 = x_40;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_array_fget(x_3, x_6);
x_45 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__2;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__4;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_28);
x_51 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_52 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_2);
x_53 = l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(x_2, x_52, x_10, x_11, x_12, x_13, x_23);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_56 = lean_box(0);
x_5 = x_19;
x_6 = x_55;
x_9 = x_56;
x_14 = x_54;
goto _start;
}
}
}
}
}
else
{
lean_object* x_83; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_9);
lean_ctor_set(x_83, 1, x_14);
return x_83;
}
}
else
{
lean_object* x_84; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_9);
lean_ctor_set(x_84, 1, x_14);
return x_84;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_7);
x_12 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = 1;
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_13;
x_9 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
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
else
{
lean_object* x_22; 
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_array_get_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
x_13 = x_8;
goto block_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_10, x_10);
if (x_24 == 0)
{
x_13 = x_8;
goto block_23;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_10);
x_27 = lean_box(0);
lean_inc(x_6);
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__8(x_9, x_25, x_26, x_27, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_13 = x_29;
goto block_23;
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_28, 0);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_28);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
block_23:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_array_get_size(x_14);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_box(0);
lean_inc(x_15);
x_18 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7(x_1, x_2, x_9, x_10, x_15, x_11, x_15, x_16, x_17, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Not inductive predicate", 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelow___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Not recursive", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelow___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("added ", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelow___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isInductivePredicate(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_12 = lean_st_ref_get(x_5, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_11, x_2, x_3, x_4, x_5, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_Meta_IndPredBelow_mkBelow___closed__2;
x_34 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_11, x_33, x_2, x_3, x_4, x_5, x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_7, 1);
lean_inc(x_35);
lean_dec(x_7);
lean_inc(x_1);
x_36 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_1, x_2, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*5);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_1);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_41 = lean_st_ref_get(x_5, x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_41, 0, x_47);
return x_41;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_41, 1);
lean_inc(x_51);
lean_dec(x_41);
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_40, x_2, x_3, x_4, x_5, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_52, 0, x_57);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_dec(x_52);
x_62 = l_Lean_Meta_IndPredBelow_mkBelow___closed__4;
x_63 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_40, x_62, x_2, x_3, x_4, x_5, x_61);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_36, 1);
lean_inc(x_64);
lean_dec(x_36);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_65 = l_Lean_Meta_IndPredBelow_mkContext(x_1, x_2, x_3, x_4, x_5, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_66);
x_68 = l_Lean_Meta_IndPredBelow_mkBelowDecl(x_66, x_2, x_3, x_4, x_5, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_71 = l_Lean_addDecl___at_Lean_Meta_evalExprCore___spec__2(x_69, x_2, x_3, x_4, x_5, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_92 = lean_st_ref_get(x_5, x_72);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 3);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_ctor_get_uint8(x_94, sizeof(void*)*1);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = 0;
x_74 = x_97;
x_75 = x_96;
goto block_91;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = lean_ctor_get(x_92, 1);
lean_inc(x_98);
lean_dec(x_92);
x_99 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_73, x_2, x_3, x_4, x_5, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_unbox(x_100);
lean_dec(x_100);
x_74 = x_102;
x_75 = x_101;
goto block_91;
}
block_91:
{
if (x_74 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_box(0);
x_77 = l_Lean_Meta_IndPredBelow_mkBelow___lambda__1(x_66, x_73, x_76, x_2, x_3, x_4, x_5, x_75);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_78 = lean_ctor_get(x_66, 2);
lean_inc(x_78);
x_79 = lean_array_to_list(lean_box(0), x_78);
x_80 = lean_box(0);
x_81 = l_List_mapTRAux___at_Lean_Meta_substCore___spec__6(x_79, x_80);
x_82 = l_Lean_MessageData_ofList(x_81);
lean_dec(x_81);
x_83 = l_Lean_Meta_IndPredBelow_mkBelow___closed__6;
x_84 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_86 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_73, x_86, x_2, x_3, x_4, x_5, x_75);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Meta_IndPredBelow_mkBelow___lambda__1(x_66, x_73, x_88, x_2, x_3, x_4, x_5, x_89);
lean_dec(x_88);
return x_90;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_71);
if (x_103 == 0)
{
return x_71;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_71, 0);
x_105 = lean_ctor_get(x_71, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_71);
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
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_68);
if (x_107 == 0)
{
return x_68;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_68, 0);
x_109 = lean_ctor_get(x_68, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_68);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_65);
if (x_111 == 0)
{
return x_65;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_65, 0);
x_113 = lean_ctor_get(x_65, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_65);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_36);
if (x_115 == 0)
{
return x_36;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_36, 0);
x_117 = lean_ctor_get(x_36, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_36);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_7);
if (x_119 == 0)
{
return x_7;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_7, 0);
x_121 = lean_ctor_get(x_7, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_7);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at_Lean_Meta_IndPredBelow_mkBelow___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwKernelException___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at_Lean_Meta_IndPredBelow_mkBelow___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_setEnv___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at_Lean_Meta_IndPredBelow_mkBelow___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_logAt___at_Lean_Meta_IndPredBelow_mkBelow___spec__6(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at_Lean_Meta_IndPredBelow_mkBelow___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_log___at_Lean_Meta_IndPredBelow_mkBelow___spec__5(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__8(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_mkBelow___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkBelow___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7044_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6;
x_6 = l_Lean_registerTraceClass(x_5, x_4);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Constructions(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_Match(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Reduce(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_IndPredBelow(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_Match(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Reduce(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__1 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__1);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__2 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__2);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__3);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__4 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__4();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__4);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__5 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__5();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7____closed__5);
if (builtin) {res = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth);
lean_dec_ref(res);
}l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1 = _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1);
l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2 = _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2);
l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3 = _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3);
l_Lean_Meta_IndPredBelow_instInhabitedVariables = _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_instInhabitedVariables);
l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1);
l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__2);
l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__3 = _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__3);
l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2);
l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__1);
l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__2);
l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__3 = _init_l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__3);
l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4 = _init_l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__1);
l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__14___rarg___closed__2);
l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1 = _init_l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1);
l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__2 = _init_l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__2);
l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1);
l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2);
l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3 = _init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3);
l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___closed__1);
l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1);
l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2);
l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3);
l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__1 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__1);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__2 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__2);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__3 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__3);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__4 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__4();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__4);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__5 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__5();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__5);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__6 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__6();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__6);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__7 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__7();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__7);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__8 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__8();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__8);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__9 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__9();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__9);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__10 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__10();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__10);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__11 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__11();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__11);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__12 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__12();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__12);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__13 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__13();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__13);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__14 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__14();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__14);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__15 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__15();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__15);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__16 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__16();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___closed__16);
l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1);
l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2);
l_Lean_Meta_IndPredBelow_proveBrecOn___closed__3 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn___closed__3);
l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1);
l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2);
l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3 = _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3);
l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1);
l_Lean_Meta_IndPredBelow_getBelowIndices_loop___closed__1 = _init_l_Lean_Meta_IndPredBelow_getBelowIndices_loop___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_getBelowIndices_loop___closed__1);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__1);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___closed__2);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__5);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__6);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__1);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__2);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__1 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__1);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__2 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__2();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__2);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__3 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__3();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__3);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__4 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__4();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__1___closed__4);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__1 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__1);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__2 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__2);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__3 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__3);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__4 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__4);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__5 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__5();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__5);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__6 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__6();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__6);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__7 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__7();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__7);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__8 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__8();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___lambda__2___closed__8);
l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__1 = _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__1();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__1);
l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__2 = _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__2();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__2);
l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__3 = _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__3();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__3);
l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__4 = _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__4();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__4);
l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__5 = _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__5();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__5);
l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__6 = _init_l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__6();
lean_mark_persistent(l_Lean_addTrace___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___closed__6);
l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__4);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__5 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___lambda__3___closed__5);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__3 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__3();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__3);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__4 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__4();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__4);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__5 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__5();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__5);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__6 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__6();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__6);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__7 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__7();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__7);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__8 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__8();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__8);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__9 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__9();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__9);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__10 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__10();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__10);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__11 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__11();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__11);
l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12 = _init_l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12();
lean_mark_persistent(l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__12);
l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1 = _init_l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1();
lean_mark_persistent(l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1);
l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2 = _init_l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2();
lean_mark_persistent(l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2);
l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3 = _init_l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3();
lean_mark_persistent(l_Lean_addDecl___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3);
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__1);
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__2);
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__3);
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__7___closed__4);
l_Lean_Meta_IndPredBelow_mkBelow___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__1);
l_Lean_Meta_IndPredBelow_mkBelow___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__2);
l_Lean_Meta_IndPredBelow_mkBelow___closed__3 = _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__3);
l_Lean_Meta_IndPredBelow_mkBelow___closed__4 = _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__4();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__4);
l_Lean_Meta_IndPredBelow_mkBelow___closed__5 = _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__5();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__5);
l_Lean_Meta_IndPredBelow_mkBelow___closed__6 = _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__6();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__6);
res = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_7044_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
