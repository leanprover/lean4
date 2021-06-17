// Lean compiler output
// Module: Lean.Meta.IndPredBelow
// Imports: Init Lean.Util.Constructions Lean.Meta.Transform Lean.Meta.Tactic Lean.Meta.Match Lean.Meta.Reduce
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
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_introNPRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__2(lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__14;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkConstructor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_whnf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__15;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__4;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5;
lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1;
lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth___closed__1;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
lean_object* l_instInhabitedDepArrow___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__1(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__2(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx_match__1(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_updatePrefix(lean_object*, lean_object*);
lean_object* l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_zipWith___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_instInhabitedVariables;
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__2(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkConstructor___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_mkMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__12;
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__3;
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__5;
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__3;
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3;
static uint64_t l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__3;
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__1(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__1(lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible_match__1(lean_object*);
lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_671____at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3;
lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__3___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__1;
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_zip___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3;
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___boxed(lean_object**);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__2(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3;
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10;
lean_object* l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__2(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12;
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2;
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9;
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__6;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
lean_object* l_List_map___at_Lean_Meta_Match_Alt_toMessageData___spec__2(lean_object*);
lean_object* l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2;
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_isInductivePredicate_visit(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__5(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__1(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5(size_t, size_t, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___boxed(lean_object*, lean_object*);
lean_object* l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining_match__1(lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_671____at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1;
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkInductiveType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4;
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3;
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__13;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1654____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2;
lean_object* l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__1(lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3;
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__5;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_instInhabitedBinderInfo;
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___boxed(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__3(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__4;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4;
lean_object* l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedPattern;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6;
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5254_(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5_(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__4;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__2;
lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1___boxed(lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_rebuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8;
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives_match__1___rarg(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1___closed__1;
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__4;
lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3;
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5;
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives_match__1(lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__1;
static lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2;
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1;
extern lean_object* l_Lean_instInhabitedInductiveVal;
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2;
extern lean_object* l_Lean_brecOnSuffix;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_match__1___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__1;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_match__1(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__2;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__1(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_mkConstWithLevelParams___spec__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__3(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_rebuild___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__3;
static lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__16;
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1;
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__2;
static lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__2;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2___boxed(lean_object**);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2;
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1;
lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1;
lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkInductiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__2(lean_object*);
static lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1;
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___boxed(lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("maxBackwardChainingDepth");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("The maximum search depth used in the backwards chaining part of the proof of `brecOn` for inductive predicates.");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3;
x_3 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2;
x_3 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__5;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
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
static uint64_t _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3() {
_start:
{
lean_object* x_1; uint64_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2;
x_3 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint64(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_2 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3;
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
x_1 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__4;
return x_1;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkContext_addMotives_match__1___rarg), 2, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive_");
return x_1;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_17 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_box(0);
x_20 = lean_name_mk_string(x_19, x_18);
x_21 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_20, x_5, x_6, x_7);
return x_21;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = l_Array_insertAt___rarg(x_1, x_2, x_4);
x_11 = 0;
x_12 = 1;
x_13 = l_Lean_Meta_mkForallFVars(x_10, x_3, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
lean_inc(x_4);
x_12 = l_Array_toSubarray___rarg(x_4, x_11, x_1);
x_13 = l_Array_ofSubarray___rarg(x_12);
lean_dec(x_12);
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
x_19 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_3, x_18, x_15, x_17, x_6, x_7, x_8, x_9, x_16);
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
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = 1;
x_13 = x_3 - x_12;
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
x_18 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_5, x_17, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = x_3 == x_4;
if (x_11 == 0)
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = 1;
x_13 = x_3 - x_12;
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
x_18 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_5, x_17, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
return x_22;
}
}
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkContext_addMotives(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_4);
x_6 = l_Lean_mkConst(x_3, x_5);
return x_6;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = 1;
x_15 = x_2 + x_14;
x_16 = x_13;
x_17 = lean_array_uset(x_8, x_2, x_16);
x_2 = x_15;
x_3 = x_17;
goto _start;
}
}
}
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(x_1);
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
x_17 = x_2;
x_18 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1(x_15, x_16, x_17);
x_19 = x_18;
x_20 = 0;
x_21 = 1;
x_22 = lean_box(x_20);
x_23 = lean_box(x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 9, 4);
lean_closure_set(x_24, 0, x_2);
lean_closure_set(x_24, 1, x_12);
lean_closure_set(x_24, 2, x_22);
lean_closure_set(x_24, 3, x_23);
x_25 = l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(x_19, x_24, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_19);
return x_25;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkContext_mkHeader(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_9 = l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(x_1);
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
x_17 = l_Lean_Meta_mkForallFVars(x_2, x_13, x_15, x_16, x_4, x_5, x_6, x_7, x_14);
return x_17;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_10 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_8, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_2 < x_1;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = x_3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = x_12;
x_16 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = x_2 + x_19;
x_21 = x_17;
x_22 = lean_array_uset(x_14, x_2, x_21);
x_2 = x_20;
x_3 = x_22;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
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
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_2 < x_1;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = x_3;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = x_12;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_IndPredBelow_mkContext_motiveType(x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 1;
x_20 = x_2 + x_19;
x_21 = x_17;
x_22 = lean_array_uset(x_14, x_2, x_21);
x_2 = x_20;
x_3 = x_22;
x_8 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = x_4 < x_3;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = x_5;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_array_uget(x_5, x_4);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_5, x_4, x_16);
x_18 = x_15;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_IndPredBelow_mkContext_mkHeader(x_2, x_11, x_18, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_4 + x_22;
x_24 = x_20;
x_25 = lean_array_uset(x_17, x_4, x_24);
x_4 = x_23;
x_5 = x_25;
x_10 = x_21;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("below");
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
x_11 = l_Lean_Name_append(x_9, x_10);
lean_dec(x_9);
x_12 = 1;
x_13 = x_2 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_8, x_2, x_14);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
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
x_17 = x_13;
x_18 = lean_box_usize(x_15);
x_19 = l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1;
lean_inc(x_17);
x_20 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1___boxed), 8, 3);
lean_closure_set(x_20, 0, x_18);
lean_closure_set(x_20, 1, x_19);
lean_closure_set(x_20, 2, x_17);
x_21 = x_20;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = lean_apply_5(x_21, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_array_get_size(x_23);
x_26 = lean_usize_of_nat(x_25);
lean_dec(x_25);
lean_inc(x_23);
x_27 = x_23;
x_28 = lean_box_usize(x_26);
x_29 = l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1;
lean_inc(x_27);
x_30 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2___boxed), 8, 3);
lean_closure_set(x_30, 0, x_28);
lean_closure_set(x_30, 1, x_29);
lean_closure_set(x_30, 2, x_27);
x_31 = x_30;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_32 = lean_apply_5(x_31, x_2, x_3, x_4, x_5, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_array_get_size(x_33);
x_36 = lean_mk_empty_array_with_capacity(x_35);
x_37 = lean_unsigned_to_nat(0u);
x_38 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3(x_33, x_33, x_35, x_37, lean_box(0), x_36, x_2, x_3, x_4, x_5, x_34);
lean_dec(x_33);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
x_42 = lean_box_usize(x_26);
x_43 = l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1;
lean_inc(x_39);
x_44 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4___boxed), 10, 5);
lean_closure_set(x_44, 0, x_8);
lean_closure_set(x_44, 1, x_39);
lean_closure_set(x_44, 2, x_42);
lean_closure_set(x_44, 3, x_43);
lean_closure_set(x_44, 4, x_27);
x_45 = x_44;
x_46 = lean_apply_5(x_45, x_2, x_3, x_4, x_5, x_40);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5(x_15, x_16, x_17);
x_50 = x_49;
x_51 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_23);
lean_ctor_set(x_51, 2, x_50);
lean_ctor_set(x_51, 3, x_48);
lean_ctor_set(x_51, 4, x_41);
lean_ctor_set(x_46, 0, x_51);
return x_46;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_46, 0);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_46);
x_54 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5(x_15, x_16, x_17);
x_55 = x_54;
x_56 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_56, 0, x_39);
lean_ctor_set(x_56, 1, x_23);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_52);
lean_ctor_set(x_56, 4, x_41);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_17);
x_58 = !lean_is_exclusive(x_46);
if (x_58 == 0)
{
return x_46;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_46, 0);
x_60 = lean_ctor_get(x_46, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_46);
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
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_32);
if (x_62 == 0)
{
return x_32;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_32, 0);
x_64 = lean_ctor_get(x_32, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_32);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_22);
if (x_66 == 0)
{
return x_22;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_22, 0);
x_68 = lean_ctor_get(x_22, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_22);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_7);
if (x_70 == 0)
{
return x_7;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_7, 0);
x_72 = lean_ctor_get(x_7, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_7);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
lean_inc(x_1);
x_11 = l_Lean_mkConst(x_10, x_1);
x_12 = 1;
x_13 = x_3 + x_12;
x_14 = x_11;
x_15 = lean_array_uset(x_9, x_3, x_14);
x_3 = x_13;
x_4 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_instInhabitedInductiveVal;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_4, x_6);
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_9);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_15 = 0;
x_16 = x_12;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_10, x_14, x_15, x_16);
x_18 = x_17;
x_19 = l_Lean_Expr_replaceFVars(x_3, x_11, x_18);
lean_dec(x_18);
return x_19;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_set(x_6, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_5 = x_13;
x_6 = x_15;
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; 
lean_dec(x_7);
lean_dec(x_5);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = l_Lean_instInhabitedInductiveVal;
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get(x_22, x_21, x_23);
lean_dec(x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_26);
x_28 = l_Lean_mkConst(x_20, x_27);
x_29 = lean_ctor_get(x_4, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_4, 3);
lean_inc(x_30);
lean_inc(x_29);
x_31 = l_Array_append___rarg(x_29, x_30);
lean_dec(x_30);
x_32 = l_Lean_mkAppN(x_28, x_31);
lean_dec(x_31);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
x_34 = l_Lean_instInhabitedExpr;
x_35 = lean_array_get(x_34, x_33, x_2);
lean_dec(x_33);
x_36 = lean_ctor_get(x_4, 4);
lean_inc(x_36);
x_37 = l_Array_append___rarg(x_29, x_36);
lean_dec(x_36);
x_38 = lean_ctor_get(x_1, 4);
lean_inc(x_38);
x_39 = lean_array_get_size(x_6);
x_40 = l_Array_toSubarray___rarg(x_6, x_38, x_39);
x_41 = l_Array_ofSubarray___rarg(x_40);
lean_dec(x_40);
x_42 = l_Array_append___rarg(x_37, x_41);
lean_dec(x_41);
x_43 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_44 = lean_array_push(x_43, x_32);
x_45 = l_Array_append___rarg(x_42, x_44);
lean_dec(x_44);
x_46 = l_Lean_mkAppN(x_35, x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_4, 0);
lean_inc(x_47);
x_48 = 0;
x_49 = 1;
x_50 = l_Lean_Meta_mkForallFVars(x_47, x_46, x_48, x_49, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_52);
lean_dec(x_52);
lean_dec(x_4);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(x_1, x_4, x_54);
lean_dec(x_54);
lean_dec(x_4);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_4);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_50);
if (x_58 == 0)
{
return x_50;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_50, 0);
x_60 = lean_ctor_get(x_50, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_50);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_rebuild(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_4, 5);
lean_inc(x_10);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Expr_getAppNumArgsAux(x_10, x_11);
x_13 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_12);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_12, x_15);
lean_dec(x_12);
x_17 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1(x_1, x_2, x_3, x_4, x_10, x_14, x_16, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_rebuild___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_IndPredBelow_mkCtorType_rebuild(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_8);
lean_inc(x_4);
x_22 = l_Lean_mkAppN(x_4, x_7);
x_23 = lean_ctor_get(x_2, 4);
x_24 = l_Lean_instInhabitedExpr;
x_25 = lean_array_get(x_24, x_23, x_3);
x_26 = lean_ctor_get(x_1, 4);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_array_get_size(x_9);
x_28 = l_Array_toSubarray___rarg(x_9, x_26, x_27);
x_29 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_30 = lean_array_push(x_29, x_22);
x_31 = l_Array_ofSubarray___rarg(x_28);
lean_dec(x_28);
x_32 = l_Array_append___rarg(x_31, x_30);
lean_dec(x_30);
x_33 = l_Lean_mkAppN(x_25, x_32);
lean_dec(x_32);
x_34 = 0;
x_35 = 1;
lean_inc(x_11);
x_36 = l_Lean_Meta_mkForallFVars(x_7, x_33, x_34, x_35, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_fvarId_x21(x_4);
lean_inc(x_11);
x_40 = l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(x_39, x_11, x_12, x_13, x_14, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Expr_binderInfo(x_4);
lean_dec(x_4);
x_44 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_41, x_43, x_37, x_6, x_11, x_12, x_13, x_14, x_42);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_40, 0);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_40);
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
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_36);
if (x_49 == 0)
{
return x_36;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_36, 0);
x_51 = lean_ctor_get(x_36, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_36);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux(x_7, x_13);
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1___boxed), 12, 5);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_3);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_7);
x_14 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_5, x_13, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
uint8_t l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1(lean_object* x_1, lean_object* x_2) {
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
x_1 = lean_mk_string("only trivial inductive applications supported in premises:");
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
x_1 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; 
lean_dec(x_7);
x_41 = lean_ctor_get(x_34, 0);
lean_inc(x_41);
lean_dec(x_34);
lean_inc(x_3);
x_42 = l_Lean_mkAppN(x_3, x_6);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
x_44 = l_Lean_instInhabitedExpr;
x_45 = lean_array_get(x_44, x_43, x_41);
lean_dec(x_43);
x_46 = lean_ctor_get(x_2, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 4);
lean_inc(x_47);
lean_dec(x_2);
x_48 = l_Array_append___rarg(x_46, x_47);
lean_dec(x_47);
x_49 = lean_ctor_get(x_1, 4);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_array_get_size(x_9);
x_51 = l_Array_toSubarray___rarg(x_9, x_49, x_50);
x_52 = l_Array_ofSubarray___rarg(x_51);
lean_dec(x_51);
x_53 = l_Array_append___rarg(x_48, x_52);
lean_dec(x_52);
x_54 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_55 = lean_array_push(x_54, x_42);
x_56 = l_Array_append___rarg(x_53, x_55);
lean_dec(x_55);
x_57 = l_Lean_mkAppN(x_45, x_56);
lean_dec(x_56);
x_58 = 0;
x_59 = 1;
lean_inc(x_11);
x_60 = l_Lean_Meta_mkForallFVars(x_6, x_57, x_58, x_59, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_Expr_fvarId_x21(x_3);
lean_inc(x_11);
x_64 = l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(x_63, x_11, x_12, x_13, x_14, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Expr_binderInfo(x_3);
lean_dec(x_3);
x_68 = lean_apply_1(x_5, x_41);
x_69 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_65, x_67, x_61, x_68, x_11, x_12, x_13, x_14, x_66);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec(x_61);
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_64);
if (x_70 == 0)
{
return x_64;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_64, 0);
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_64);
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
lean_dec(x_41);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_3);
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
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Expr_getAppNumArgsAux(x_6, x_12);
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___lambda__1), 11, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_6);
x_13 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_4, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = lean_apply_7(x_2, x_5, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = lean_apply_8(x_1, x_4, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___boxed), 11, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_push(x_1, x_7);
x_16 = l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(x_2, x_3, x_4, x_5, x_15, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 6)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_18 = lean_expr_instantiate_rev(x_15, x_5);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = (uint8_t)((x_17 << 24) >> 61);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4___lambda__1), 14, 6);
lean_closure_set(x_23, 0, x_5);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_16);
x_24 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg(x_14, x_22, x_20, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_29; lean_object* x_30; 
x_29 = lean_expr_instantiate_rev(x_6, x_5);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 0;
x_34 = 1;
lean_inc(x_9);
x_35 = l_Lean_Meta_mkLambdaFVars(x_5, x_31, x_33, x_34, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
return x_38;
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg___boxed), 11, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_push(x_1, x_7);
x_16 = l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(x_2, x_3, x_4, x_5, x_15, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 7)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint64(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_18 = lean_expr_instantiate_rev(x_15, x_5);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = (uint8_t)((x_17 << 24) >> 61);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1), 14, 6);
lean_closure_set(x_23, 0, x_5);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_3);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_16);
x_24 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg(x_14, x_22, x_20, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_29; lean_object* x_30; 
x_29 = lean_expr_instantiate_rev(x_6, x_5);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_30 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_29, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 0;
x_34 = 1;
lean_inc(x_9);
x_35 = l_Lean_Meta_mkForallFVars(x_5, x_31, x_33, x_34, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_37);
return x_38;
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___rarg), 11, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_push(x_1, x_7);
x_16 = l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(x_2, x_3, x_4, x_5, x_15, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_6) == 8)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 3);
lean_inc(x_17);
lean_dec(x_6);
x_18 = lean_expr_instantiate_rev(x_15, x_5);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_19 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_expr_instantiate_rev(x_16, x_5);
lean_dec(x_16);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1), 14, 6);
lean_closure_set(x_26, 0, x_5);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_2);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_4);
lean_closure_set(x_26, 5, x_17);
x_27 = l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___rarg(x_14, x_20, x_24, x_26, x_7, x_8, x_9, x_10, x_11, x_12, x_25);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_19);
if (x_32 == 0)
{
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_expr_instantiate_rev(x_6, x_5);
lean_dec(x_6);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_37 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_36, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = 0;
x_41 = 1;
lean_inc(x_9);
x_42 = l_Lean_Meta_mkLambdaFVars(x_5, x_38, x_40, x_41, x_9, x_10, x_11, x_12, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_43, x_7, x_8, x_9, x_10, x_11, x_12, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_37);
if (x_50 == 0)
{
return x_37;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_37, 0);
x_52 = lean_ctor_get(x_37, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = x_6 < x_5;
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = x_7;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_array_uget(x_7, x_6);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_uset(x_7, x_6, x_19);
x_21 = x_18;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = x_6 + x_25;
x_27 = x_23;
x_28 = lean_array_uset(x_20, x_6, x_27);
x_6 = x_26;
x_7 = x_28;
x_14 = x_24;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_array_set(x_6, x_7, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_7, x_18);
lean_dec(x_7);
x_5 = x_15;
x_6 = x_17;
x_7 = x_19;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_7);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_6);
x_25 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_26 = x_6;
x_27 = lean_box_usize(x_25);
x_28 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1;
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_29 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10___boxed), 14, 7);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_27);
lean_closure_set(x_29, 5, x_28);
lean_closure_set(x_29, 6, x_26);
x_30 = x_29;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_31 = lean_apply_7(x_30, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_mkAppN(x_22, x_32);
lean_dec(x_32);
x_35 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_34, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_31);
if (x_36 == 0)
{
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
lean_object* l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg), 9, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_8, 1);
lean_dec(x_14);
lean_ctor_set(x_8, 1, x_12);
x_15 = lean_apply_7(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 2);
x_18 = lean_ctor_get(x_8, 3);
x_19 = lean_ctor_get(x_8, 4);
x_20 = lean_ctor_get(x_8, 5);
x_21 = lean_ctor_get(x_8, 6);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_12);
lean_ctor_set(x_23, 2, x_17);
lean_ctor_set(x_23, 3, x_18);
lean_ctor_set(x_23, 4, x_19);
lean_ctor_set(x_23, 5, x_20);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_23, 7, x_22);
x_24 = lean_apply_7(x_2, x_3, x_4, x_6, x_7, x_23, x_9, x_10);
return x_24;
}
}
}
static lean_object* _init_l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 2);
lean_inc(x_10);
x_11 = lean_nat_dec_eq(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___lambda__1(x_9, x_1, x_2, x_3, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
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
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__2;
x_23 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_22, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg), 8, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
switch (lean_obj_tag(x_15)) {
case 5:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Expr_getAppNumArgsAux(x_15, x_16);
x_18 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_17);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_22 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11(x_1, x_2, x_3, x_4, x_15, x_19, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
case 6:
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_24 = l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(x_1, x_2, x_3, x_4, x_23, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_26 = l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(x_1, x_2, x_3, x_4, x_25, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_26;
}
case 8:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_28 = l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(x_1, x_2, x_3, x_4, x_27, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_28;
}
case 10:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_31);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_32 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_31, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_expr_update_mdata(x_15, x_33);
x_36 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_34);
return x_36;
}
else
{
uint8_t x_37; 
lean_free_object(x_15);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint64_t x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_15, 0);
x_42 = lean_ctor_get(x_15, 1);
x_43 = lean_ctor_get_uint64(x_15, sizeof(void*)*2);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_42);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_42, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set_uint64(x_47, sizeof(void*)*2, x_43);
x_48 = lean_expr_update_mdata(x_47, x_45);
x_49 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_48, x_6, x_7, x_8, x_9, x_10, x_11, x_46);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_52 = x_44;
} else {
 lean_dec_ref(x_44);
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
case 11:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_15);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_15, 0);
x_56 = lean_ctor_get(x_15, 1);
x_57 = lean_ctor_get(x_15, 2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_57);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_58 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_57, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_expr_update_proj(x_15, x_59);
x_62 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_61, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
return x_62;
}
else
{
uint8_t x_63; 
lean_free_object(x_15);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_58);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint64_t x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_15, 0);
x_68 = lean_ctor_get(x_15, 1);
x_69 = lean_ctor_get(x_15, 2);
x_70 = lean_ctor_get_uint64(x_15, sizeof(void*)*3);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_69);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_71 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_1, x_2, x_3, x_4, x_69, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_74, 0, x_67);
lean_ctor_set(x_74, 1, x_68);
lean_ctor_set(x_74, 2, x_69);
lean_ctor_set_uint64(x_74, sizeof(void*)*3, x_70);
x_75 = lean_expr_update_proj(x_74, x_72);
x_76 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_75, x_6, x_7, x_8, x_9, x_10, x_11, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
default: 
{
lean_object* x_81; 
x_81 = l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_81;
}
}
}
}
}
lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Std_HashMapImp_insert___at_Lean_MetavarContext_instantiateExprMVars___spec__3(x_3, x_1, x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_13, 0, lean_box(0));
lean_closure_set(x_13, 1, lean_box(0));
lean_closure_set(x_13, 2, x_6);
lean_inc(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = lean_apply_8(x_4, lean_box(0), x_13, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_16, x_5);
lean_dec(x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_14);
lean_inc(x_1);
lean_inc(x_5);
x_19 = lean_apply_1(x_1, x_5);
x_20 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_20, 0, x_19);
lean_inc(x_4);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1), 12, 4);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_3);
lean_closure_set(x_21, 3, x_4);
x_22 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg), 9, 2);
lean_closure_set(x_22, 0, x_20);
lean_closure_set(x_22, 1, x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg(x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__2), 3, 2);
lean_closure_set(x_26, 0, x_5);
lean_closure_set(x_26, 1, x_24);
x_27 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_26);
x_28 = lean_apply_8(x_4, lean_box(0), x_27, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_24);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_41; 
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
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_41);
return x_14;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_14, 0);
x_43 = lean_ctor_get(x_14, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_14);
x_44 = l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(x_42, x_5);
lean_dec(x_42);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_inc(x_1);
lean_inc(x_5);
x_45 = lean_apply_1(x_1, x_5);
x_46 = lean_alloc_closure((void*)(l_StateRefT_x27_lift___rarg___boxed), 2, 1);
lean_closure_set(x_46, 0, x_45);
lean_inc(x_4);
x_47 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1), 12, 4);
lean_closure_set(x_47, 0, x_1);
lean_closure_set(x_47, 1, x_2);
lean_closure_set(x_47, 2, x_3);
lean_closure_set(x_47, 3, x_4);
x_48 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12___rarg), 9, 2);
lean_closure_set(x_48, 0, x_46);
lean_closure_set(x_48, 1, x_47);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_49 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg(x_48, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_50);
x_52 = lean_alloc_closure((void*)(l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__2), 3, 2);
lean_closure_set(x_52, 0, x_5);
lean_closure_set(x_52, 1, x_50);
x_53 = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed), 3, 2);
lean_closure_set(x_53, 0, x_6);
lean_closure_set(x_53, 1, x_52);
x_54 = lean_apply_8(x_4, lean_box(0), x_53, x_7, x_8, x_9, x_10, x_11, x_51);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_50);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_50);
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_60 = x_54;
} else {
 lean_dec_ref(x_54);
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
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = lean_ctor_get(x_49, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_49, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_64 = x_49;
} else {
 lean_dec_ref(x_49);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
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
x_66 = lean_ctor_get(x_44, 0);
lean_inc(x_66);
lean_dec(x_44);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_43);
return x_67;
}
}
}
else
{
uint8_t x_68; 
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
x_68 = !lean_is_exclusive(x_14);
if (x_68 == 0)
{
return x_14;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_14, 0);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_14);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_1 = lean_unsigned_to_nat(8u);
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
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_box(0);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1;
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__2;
lean_inc(x_8);
lean_inc(x_15);
x_18 = l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(x_2, x_3, x_10, x_17, x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_8, x_20);
lean_dec(x_8);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_get(x_15, x_22);
lean_dec(x_15);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_19);
return x_23;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_19);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_15);
lean_dec(x_8);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_constName_x3f(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
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
x_14 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1___boxed), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_array_get_size(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_findIdx_x3f_loop___rarg(x_13, x_14, x_15, x_16, lean_box(0));
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
x_19 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(x_2, x_18, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_17);
x_20 = lean_st_ref_get(x_7, x_8);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_get(x_3, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_23, x_25);
lean_dec(x_23);
x_27 = lean_st_ref_get(x_7, x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_st_ref_set(x_3, x_26, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1(x_2, x_30, x_3, x_4, x_5, x_6, x_7, x_31);
lean_dec(x_30);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_1 = lean_mk_string("only arrows are allowed as premises. Multiple recursive occurrences detected:");
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
lean_inc(x_2);
x_16 = l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1(x_2, x_8, x_15, x_13, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_6, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_dec_lt(x_23, x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_2);
x_25 = lean_box(0);
x_26 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4(x_21, x_25, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_21);
x_27 = l_Lean_indentExpr(x_2);
x_28 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3;
x_29 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
x_30 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_Meta_whnf___spec__1(x_31, x_3, x_4, x_5, x_6, x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10(x_1, x_2, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
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
lean_dec(x_28);
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_array_get(x_20, x_14, x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_21);
x_22 = l_Lean_Meta_inferType(x_21, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_23);
lean_inc(x_1);
x_25 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount(x_1, x_23, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_23);
x_28 = !lean_is_exclusive(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_4, 5);
lean_dec(x_29);
x_30 = lean_ctor_get(x_4, 4);
lean_dec(x_30);
x_31 = lean_ctor_get(x_4, 3);
lean_dec(x_31);
x_32 = lean_ctor_get(x_4, 2);
lean_dec(x_32);
x_33 = lean_ctor_get(x_4, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_array_push(x_11, x_21);
lean_ctor_set(x_4, 0, x_36);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_5, x_37);
lean_dec(x_5);
x_5 = x_38;
x_10 = x_35;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_4);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_41 = lean_array_push(x_11, x_21);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_12);
lean_ctor_set(x_42, 2, x_13);
lean_ctor_set(x_42, 3, x_14);
lean_ctor_set(x_42, 4, x_15);
lean_ctor_set(x_42, 5, x_16);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_5, x_43);
lean_dec(x_5);
x_4 = x_42;
x_5 = x_44;
x_10 = x_40;
goto _start;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_dec(x_25);
lean_inc(x_23);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_21);
x_47 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2___boxed), 20, 13);
lean_closure_set(x_47, 0, x_21);
lean_closure_set(x_47, 1, x_11);
lean_closure_set(x_47, 2, x_12);
lean_closure_set(x_47, 3, x_13);
lean_closure_set(x_47, 4, x_14);
lean_closure_set(x_47, 5, x_15);
lean_closure_set(x_47, 6, x_16);
lean_closure_set(x_47, 7, x_5);
lean_closure_set(x_47, 8, x_1);
lean_closure_set(x_47, 9, x_2);
lean_closure_set(x_47, 10, x_3);
lean_closure_set(x_47, 11, x_4);
lean_closure_set(x_47, 12, x_23);
x_48 = l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder(x_1, x_4, x_21, x_23, lean_box(0), x_47, x_6, x_7, x_8, x_9, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_23);
lean_dec(x_21);
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
x_49 = !lean_is_exclusive(x_25);
if (x_49 == 0)
{
return x_25;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
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
lean_dec(x_21);
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
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
return x_22;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_22, 0);
x_55 = lean_ctor_get(x_22, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_22);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___boxed(lean_object** _args) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2___boxed(lean_object** _args) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_9, x_10, x_2, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_3 < x_2;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_11 = x_4;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
x_16 = x_13;
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_1);
x_20 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1___boxed), 8, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_19);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_16, 1, x_20);
lean_ctor_set(x_16, 0, x_22);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_16);
x_24 = 1;
x_25 = x_3 + x_24;
x_26 = x_23;
x_27 = lean_array_uset(x_15, x_3, x_26);
x_3 = x_25;
x_4 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_16);
lean_inc(x_1);
x_31 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1___boxed), 8, 2);
lean_closure_set(x_31, 0, x_1);
lean_closure_set(x_31, 1, x_30);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
x_36 = 1;
x_37 = x_3 + x_36;
x_38 = x_35;
x_39 = lean_array_uset(x_15, x_3, x_38);
x_3 = x_37;
x_4 = x_39;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = l_Lean_instInhabitedExpr;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1___closed__1;
return x_2;
}
}
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_push(x_1, x_4);
x_11 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1;
x_2 = lean_alloc_closure((void*)(l_instInhabitedDepArrow___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_instInhabitedBinderInfo;
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2;
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_instInhabitedName;
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_array_get_size(x_3);
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_2);
x_12 = lean_apply_6(x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4;
x_14 = lean_array_get(x_13, x_2, x_9);
lean_dec(x_9);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = lean_apply_6(x_18, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__2), 9, 3);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_1);
lean_closure_set(x_22, 2, x_2);
x_23 = lean_unbox(x_17);
lean_dec(x_17);
x_24 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_16, x_23, x_20, x_22, x_4, x_5, x_6, x_7, x_21);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_16);
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
lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_9 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3(x_2, x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = x_10;
x_14 = lean_box_usize(x_12);
x_15 = l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1;
lean_inc(x_4);
x_16 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___boxed), 9, 4);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_13);
x_17 = x_16;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_18 = lean_apply_5(x_17, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___lambda__1), 10, 4);
lean_closure_set(x_21, 0, x_4);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
x_22 = l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2(x_19, x_21, x_5, x_6, x_7, x_8, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_16 = lean_array_fget(x_2, x_4);
x_17 = lean_ctor_get(x_1, 2);
x_18 = l_Lean_instInhabitedName;
x_19 = lean_array_get(x_18, x_17, x_4);
x_20 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1___boxed), 7, 1);
lean_closure_set(x_20, 0, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_23 = lean_array_push(x_6, x_21);
x_3 = x_15;
x_4 = x_22;
x_5 = lean_box(0);
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; uint8_t x_12; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = 1;
x_11 = x_2 + x_10;
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = 0;
x_15 = lean_box(x_14);
lean_ctor_set(x_9, 0, x_15);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_9);
x_17 = x_16;
x_18 = lean_array_uset(x_8, x_2, x_17);
x_2 = x_11;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = x_25;
x_27 = lean_array_uset(x_8, x_2, x_26);
x_2 = x_11;
x_3 = x_27;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = x_1;
x_12 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3(x_9, x_10, x_11);
x_13 = x_12;
x_14 = l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2(x_13, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
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
x_18 = l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2(x_15, x_17, x_5, x_6, x_7, x_8, x_16);
return x_18;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_dec(x_13);
x_15 = lean_array_get_size(x_4);
x_16 = l_Array_toSubarray___rarg(x_4, x_11, x_15);
x_17 = l_Array_ofSubarray___rarg(x_16);
lean_dec(x_16);
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
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_12 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkConstructor___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("'");
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' is not a constructor");
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 6)
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = l_Lean_mkConst(x_1, x_16);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__2;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__4;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkConstructor___spec__2(x_22, x_2, x_3, x_4, x_5, x_15);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkConstructor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_3);
x_9 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = l_Lean_instInhabitedName;
x_14 = lean_array_get(x_13, x_12, x_2);
lean_dec(x_12);
x_15 = l_Lean_Name_updatePrefix(x_3, x_14);
x_16 = l_Lean_Meta_IndPredBelow_mkCtorType(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
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
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_15);
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
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkConstructor___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkConstructor___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkInductiveType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkInductiveType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = l_Lean_instInhabitedName;
x_15 = lean_array_get(x_14, x_13, x_2);
lean_dec(x_13);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_array_get(x_17, x_16, x_2);
lean_dec(x_2);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_10, 0, x_19);
return x_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_10);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = l_Lean_instInhabitedName;
x_24 = lean_array_get(x_23, x_22, x_2);
lean_dec(x_22);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_instInhabitedExpr;
x_27 = lean_array_get(x_26, x_25, x_2);
lean_dec(x_2);
lean_dec(x_25);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_20);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_instInhabitedInductiveVal;
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get(x_8, x_7, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_mk_empty_array_with_capacity(x_13);
lean_inc(x_1);
x_15 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1(x_1, x_7, x_13, x_9, lean_box(0), x_14, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_nat_add(x_18, x_20);
lean_dec(x_20);
lean_dec(x_18);
x_22 = lean_array_to_list(lean_box(0), x_17);
x_23 = lean_ctor_get_uint8(x_10, sizeof(void*)*5 + 1);
lean_dec(x_10);
x_24 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*3, x_23);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_ctor_get(x_1, 4);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_array_get_size(x_28);
lean_dec(x_28);
x_30 = lean_nat_add(x_27, x_29);
lean_dec(x_29);
lean_dec(x_27);
x_31 = lean_array_to_list(lean_box(0), x_25);
x_32 = lean_ctor_get_uint8(x_10, sizeof(void*)*5 + 1);
lean_dec(x_10);
x_33 = lean_alloc_ctor(6, 3, 1);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*3, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
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
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_backwardsChaining_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_3 == x_4;
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_uget(x_2, x_3);
x_12 = l_Lean_Expr_mvarId_x21(x_11);
lean_dec(x_11);
x_13 = l_Lean_Meta_isExprMVarAssigned(x_12, x_5, x_6, x_7, x_8, x_9);
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
x_32 = x_3 + x_31;
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
x_40 = x_3 + x_39;
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
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 == x_6;
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
lean_dec(x_13);
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
x_19 = x_5 + x_18;
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
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_31 = l_Lean_mkAppN(x_30, x_16);
x_32 = l_Lean_Meta_assignExprMVar(x_4, x_31, x_6, x_7, x_8, x_9, x_29);
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
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 == x_6;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = x_5 + x_14;
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
x_21 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3(x_20, x_7, x_8, x_9, x_10, x_11);
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
x_26 = x_5 + x_25;
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
x_41 = x_5 + x_40;
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
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
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
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_4, 0);
x_25 = lean_array_get_size(x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
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
return x_37;
}
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 == x_6;
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_13) == 0)
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = x_5 + x_14;
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
x_21 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3(x_20, x_7, x_8, x_9, x_10, x_11);
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
x_26 = x_5 + x_25;
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
x_41 = x_5 + x_40;
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
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 0);
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
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_18);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec(x_18);
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
x_31 = lean_array_get_size(x_30);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
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
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_1);
x_9 = l_Lean_Meta_getMVarType(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_dec(x_12);
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
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_11 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
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
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_proveBrecOn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_proveBrecOn_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_proveBrecOn_intros(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 < x_4;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = l_Lean_mkFVar(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_16 = l_Lean_Meta_apply(x_1, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
else
{
lean_object* x_28; size_t x_29; size_t x_30; 
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_dec(x_16);
x_29 = 1;
x_30 = x_5 + x_29;
lean_inc(x_2);
{
size_t _tmp_4 = x_30;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_28;
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
x_1 = lean_mk_string("cannot apply induction hypothesis: ");
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
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_25 = l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__2(x_1, x_24, x_19, x_22, x_23, x_24, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
x_8 = x_27;
x_9 = x_29;
goto block_18;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_8 = x_32;
x_9 = x_29;
goto block_18;
}
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
x_15 = l_Lean_throwError___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1(x_14, x_3, x_4, x_5, x_6, x_9);
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
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_1, 2);
x_14 = l_Lean_instInhabitedName;
x_15 = lean_array_get(x_14, x_13, x_2);
x_16 = l_Lean_mkConst(x_15, x_3);
x_17 = l_Array_append___rarg(x_4, x_5);
x_18 = l_Array_append___rarg(x_17, x_6);
x_19 = l_Lean_mkAppN(x_16, x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = 1;
x_22 = l_Lean_Meta_mkLambdaFVars(x_6, x_19, x_20, x_21, x_8, x_9, x_10, x_11, x_12);
return x_22;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
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
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_1);
x_24 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1___boxed), 12, 5);
lean_closure_set(x_24, 0, x_1);
lean_closure_set(x_24, 1, x_7);
lean_closure_set(x_24, 2, x_4);
lean_closure_set(x_24, 3, x_2);
lean_closure_set(x_24, 4, x_3);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_25 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_22, x_24, x_10, x_11, x_12, x_13, x_23);
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
x_1 = lean_mk_string("rec");
return x_1;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_induction(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_array_get_size(x_10);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = x_10;
x_15 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_12, x_13, x_14);
x_16 = x_15;
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_array_get_size(x_17);
x_19 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_20 = x_17;
x_21 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_19, x_13, x_20);
x_22 = x_21;
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_24);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_array_get_size(x_26);
x_28 = lean_mk_empty_array_with_capacity(x_27);
x_29 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_25);
lean_inc(x_16);
x_30 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1(x_1, x_16, x_22, x_25, x_26, x_27, x_29, lean_box(0), x_28, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_23, 0);
lean_inc(x_33);
lean_dec(x_23);
x_34 = l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1;
x_35 = lean_name_mk_string(x_33, x_34);
x_36 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_35, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_List_lengthAux___rarg(x_25, x_29);
x_40 = l_Lean_ConstantInfo_numLevelParams(x_37);
x_41 = lean_nat_dec_lt(x_39, x_40);
lean_dec(x_40);
lean_dec(x_39);
x_42 = l_Lean_ConstantInfo_name(x_37);
lean_dec(x_37);
x_43 = l_Array_append___rarg(x_16, x_31);
lean_dec(x_31);
if (x_41 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = l_Lean_mkConst(x_42, x_25);
x_45 = l_Lean_mkAppN(x_44, x_43);
lean_dec(x_43);
x_46 = l_Lean_Meta_apply(x_3, x_45, x_5, x_6, x_7, x_8, x_38);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_47 = l_Lean_levelZero;
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_25);
x_49 = l_Lean_mkConst(x_42, x_48);
x_50 = l_Lean_mkAppN(x_49, x_43);
lean_dec(x_43);
x_51 = l_Lean_Meta_apply(x_3, x_50, x_5, x_6, x_7, x_8, x_38);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
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
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_30);
if (x_56 == 0)
{
return x_30;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_30, 0);
x_58 = lean_ctor_get(x_30, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_30);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_15;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_introNPRec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarType(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_21 = l_Lean_mkConst(x_19, x_20);
x_22 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(x_19, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_mkAppN(x_21, x_31);
lean_dec(x_31);
x_33 = l_Lean_Meta_apply(x_1, x_32, x_6, x_7, x_8, x_9, x_30);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
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
uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_22);
if (x_38 == 0)
{
return x_22;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_22, 0);
x_40 = lean_ctor_get(x_22, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_22);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_4);
x_16 = l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1(x_3);
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_Expr_getAppNumArgsAux(x_16, x_17);
x_19 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_18);
x_20 = lean_mk_array(x_18, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_18, x_21);
lean_dec(x_18);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1___boxed), 10, 5);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_16);
lean_closure_set(x_23, 3, x_20);
lean_closure_set(x_23, 4, x_22);
x_24 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(x_1, x_23, x_5, x_6, x_7, x_8, x_9);
return x_24;
}
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_20 = l_Lean_Meta_getMVarType(x_18, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_getAppNumArgsAux(x_21, x_12);
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
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = 1;
x_7 = x_2 - x_6;
x_8 = lean_array_uget(x_1, x_7);
x_9 = l_List_append___rarg(x_8, x_4);
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
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("couldn't solve by backwards chaining (");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("IndPredBelow");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8;
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" = ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__13;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("): ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Meta_isExprMVarAssigned(x_2, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(x_1);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__14;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__16;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_13);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_13);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1___boxed), 6, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(x_13, x_29, x_3, x_4, x_5, x_6, x_18);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_15, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_15, 0, x_33);
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_15);
if (x_37 == 0)
{
return x_15;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_15, 0);
x_39 = lean_ctor_get(x_15, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_15);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_12);
if (x_41 == 0)
{
return x_12;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_12, 0);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_12);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_8);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_8, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_8, 0, x_47);
return x_8;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
lean_dec(x_8);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth;
x_15 = l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(x_13, x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg(x_15, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_3 = x_12;
x_8 = x_17;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("applying the induction hypothesis should only return one goal");
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
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_23 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1654____spec__1(x_22, x_4, x_5, x_6, x_7, x_21);
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
lean_inc(x_18);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_6);
x_33 = l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1(x_6, x_18, x_31, x_4, x_5, x_6, x_7, x_32);
lean_dec(x_18);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_instantiateMVars(x_11, x_4, x_5, x_6, x_7, x_34);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_30);
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
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_27);
if (x_44 == 0)
{
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_27, 0);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_27);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_19, 1);
lean_inc(x_48);
lean_dec(x_19);
x_49 = l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2;
x_50 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1654____spec__1(x_49, x_4, x_5, x_6, x_7, x_48);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
return x_14;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_14, 0);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_14);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
lean_object* l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = l_Lean_instInhabitedInductiveVal;
x_14 = lean_array_get(x_13, x_12, x_2);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_List_map___at_Lean_mkConstWithLevelParams___spec__1(x_16);
x_18 = l_Array_append___rarg(x_3, x_4);
x_19 = l_Array_append___rarg(x_18, x_5);
x_20 = lean_ctor_get(x_1, 2);
x_21 = l_Lean_instInhabitedName;
x_22 = lean_array_get(x_21, x_20, x_2);
x_23 = l_Lean_mkConst(x_22, x_17);
x_24 = l_Lean_mkAppN(x_23, x_19);
lean_dec(x_19);
x_25 = l_Lean_instInhabitedExpr;
x_26 = lean_array_get(x_25, x_4, x_2);
x_27 = l_Lean_mkAppN(x_26, x_5);
x_28 = l_Lean_Meta_mkArrow(x_24, x_27, x_7, x_8, x_9, x_10, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 0;
x_32 = 1;
x_33 = l_Lean_Meta_mkForallFVars(x_5, x_29, x_31, x_32, x_7, x_8, x_9, x_10, x_30);
return x_33;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1___boxed), 11, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
x_13 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ih");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ih_");
return x_1;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_34 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3;
x_35 = lean_string_append(x_33, x_34);
x_36 = lean_box(0);
x_37 = lean_name_mk_string(x_36, x_35);
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
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_4, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_4, x_15);
lean_dec(x_4);
x_17 = lean_ctor_get(x_1, 4);
lean_inc(x_17);
lean_inc(x_17);
lean_inc(x_2);
x_18 = l_Array_toSubarray___rarg(x_2, x_13, x_17);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_array_get_size(x_19);
lean_dec(x_19);
x_21 = lean_nat_add(x_17, x_20);
lean_dec(x_20);
lean_inc(x_2);
x_22 = l_Array_toSubarray___rarg(x_2, x_17, x_21);
x_23 = l_Array_ofSubarray___rarg(x_22);
lean_dec(x_22);
x_24 = l_Array_ofSubarray___rarg(x_18);
lean_dec(x_18);
x_25 = lean_array_fget(x_3, x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_1);
x_26 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH(x_1, x_24, x_23, x_5, x_25, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_30 = lean_array_push(x_7, x_27);
x_4 = x_16;
x_5 = x_29;
x_6 = lean_box(0);
x_7 = x_30;
x_12 = x_28;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
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
lean_object* x_36; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_12);
return x_36;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_11 = l_Array_append___rarg(x_1, x_5);
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_array_get(x_12, x_2, x_3);
x_14 = l_Array_ofSubarray___rarg(x_4);
x_15 = l_Lean_mkAppN(x_13, x_14);
lean_dec(x_14);
x_16 = 0;
x_17 = 1;
x_18 = l_Lean_Meta_mkForallFVars(x_11, x_15, x_16, x_17, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_add(x_10, x_12);
lean_inc(x_13);
lean_inc(x_3);
x_14 = l_Array_toSubarray___rarg(x_3, x_10, x_13);
x_15 = l_Array_ofSubarray___rarg(x_14);
lean_dec(x_14);
x_16 = lean_array_get_size(x_3);
lean_inc(x_3);
x_17 = l_Array_toSubarray___rarg(x_3, x_13, x_16);
x_18 = lean_mk_empty_array_with_capacity(x_12);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_20 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1(x_1, x_3, x_11, x_12, x_19, lean_box(0), x_18, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1___boxed), 10, 4);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_15);
lean_closure_set(x_23, 2, x_2);
lean_closure_set(x_23, 3, x_17);
x_24 = l_Lean_Meta_withLocalDeclsD___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__2(x_21, x_23, x_5, x_6, x_7, x_8, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_array_get(x_9, x_8, x_2);
lean_dec(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2___boxed), 9, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
x_12 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_10, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = l_Lean_instInhabitedInductiveVal;
x_13 = lean_array_get(x_12, x_11, x_2);
lean_dec(x_2);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 2);
lean_dec(x_18);
x_19 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1;
x_20 = l_Lean_Name_append(x_16, x_19);
lean_dec(x_16);
lean_inc(x_9);
x_21 = l_Lean_Meta_IndPredBelow_proveBrecOn(x_1, x_13, x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 0, x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 0, x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_20);
lean_free_object(x_14);
lean_dec(x_17);
lean_dec(x_9);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1;
x_38 = l_Lean_Name_append(x_35, x_37);
lean_dec(x_35);
lean_inc(x_9);
x_39 = l_Lean_Meta_IndPredBelow_proveBrecOn(x_1, x_13, x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
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
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_43, 2, x_9);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_40);
x_45 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_45, 0, x_44);
if (lean_is_scalar(x_42)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_42;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_9);
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_49 = x_39;
} else {
 lean_dec_ref(x_39);
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
uint8_t x_51; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_8);
if (x_51 == 0)
{
return x_8;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_8, 0);
x_53 = lean_ctor_get(x_8, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_8);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
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
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_nat_dec_le(x_11, x_4);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_array_get(x_13, x_1, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_15 = l_Lean_Meta_inferType(x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Expr_bindingDomain_x21(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_isExprDefEq(x_16, x_18, x_6, x_7, x_8, x_9, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1___boxed), 11, 4);
lean_closure_set(x_23, 0, x_5);
lean_closure_set(x_23, 1, x_1);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
x_24 = l_Lean_Meta_IndPredBelow_getBelowIndices_loop___closed__1;
x_25 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(x_2, x_24, x_23, x_6, x_7, x_8, x_9, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_28 = lean_array_push(x_27, x_14);
x_29 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_28, x_29, x_2, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_5);
x_33 = lean_array_push(x_3, x_5);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_4, x_34);
lean_dec(x_4);
x_36 = lean_nat_add(x_5, x_34);
lean_dec(x_5);
x_2 = x_31;
x_3 = x_33;
x_4 = x_35;
x_5 = x_36;
x_10 = x_32;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_30);
if (x_38 == 0)
{
return x_30;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_30, 0);
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_30);
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
uint8_t x_42; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
return x_19;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = lean_ctor_get(x_19, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_19);
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
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_15);
if (x_46 == 0)
{
return x_15;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_10);
return x_50;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_14 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(x_13, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(x_17, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_8, 0);
lean_inc(x_20);
lean_dec(x_8);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1___boxed), 8, 1);
lean_closure_set(x_22, 0, x_15);
x_23 = l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(x_21, x_22, x_2, x_3, x_4, x_5, x_19);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_15);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_14);
if (x_28 == 0)
{
return x_14;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_14, 0);
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_14);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_24 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_25 = lean_array_push(x_24, x_1);
x_26 = l_Array_ofSubarray___rarg(x_23);
lean_dec(x_23);
x_27 = l_Array_append___rarg(x_26, x_25);
lean_dec(x_25);
x_28 = lean_array_get_size(x_4);
x_29 = l_Array_toSubarray___rarg(x_4, x_21, x_28);
x_30 = l_Array_ofSubarray___rarg(x_29);
lean_dec(x_29);
x_31 = l_Array_append___rarg(x_27, x_30);
lean_dec(x_30);
x_32 = lean_array_push(x_24, x_2);
x_33 = l_Array_append___rarg(x_31, x_32);
lean_dec(x_32);
x_34 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
x_35 = l_Lean_Name_append(x_17, x_34);
x_36 = l_Lean_Expr_constLevels_x21(x_3);
lean_dec(x_3);
x_37 = l_Lean_mkConst(x_35, x_36);
x_38 = l_Lean_mkAppN(x_37, x_33);
lean_dec(x_33);
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
x_45 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_46 = lean_array_push(x_45, x_1);
x_47 = l_Array_ofSubarray___rarg(x_44);
lean_dec(x_44);
x_48 = l_Array_append___rarg(x_47, x_46);
lean_dec(x_46);
x_49 = lean_array_get_size(x_4);
x_50 = l_Array_toSubarray___rarg(x_4, x_42, x_49);
x_51 = l_Array_ofSubarray___rarg(x_50);
lean_dec(x_50);
x_52 = l_Array_append___rarg(x_48, x_51);
lean_dec(x_51);
x_53 = lean_array_push(x_45, x_2);
x_54 = l_Array_append___rarg(x_52, x_53);
lean_dec(x_53);
x_55 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
x_56 = l_Lean_Name_append(x_17, x_55);
x_57 = l_Lean_Expr_constLevels_x21(x_3);
lean_dec(x_3);
x_58 = l_Lean_mkConst(x_56, x_57);
x_59 = l_Lean_mkAppN(x_58, x_54);
lean_dec(x_54);
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
lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_array_get(x_9, x_2, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_11 = l_Lean_Meta_inferType(x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_getAppNumArgsAux(x_12, x_14);
x_16 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1(x_1, x_10, x_12, x_17, x_19, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_4(x_2, x_8, x_9, x_10, x_11);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_apply_2(x_3, x_13, x_14);
return x_15;
}
default: 
{
lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_apply_1(x_5, x_1);
return x_16;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__1___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_4, x_5, x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_1(x_4, x_1);
return x_9;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_1, x_2);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_1);
x_8 = lean_nat_dec_eq(x_2, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_dec(x_2);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_apply_2(x_4, x_5, x_5);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_apply_3(x_2, x_5, x_6, x_4);
return x_7;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_4(x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___lambda__1___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_18 = lean_array_push(x_17, x_2);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_1, x_18, x_19, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__2;
x_25 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_24, x_8, x_9, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__3;
x_30 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_26, x_28, x_23, x_29, x_6, x_7, x_8, x_9, x_27);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
return x_20;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_20, 0);
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_20);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 < x_2;
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = x_4;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_uset(x_4, x_3, x_8);
x_10 = x_7;
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = 1;
x_14 = x_3 + x_13;
x_15 = x_12;
x_16 = lean_array_uset(x_9, x_3, x_15);
x_3 = x_14;
x_4 = x_16;
goto _start;
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_nat_dec_le(x_12, x_5);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_4, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_4, x_16);
lean_dec(x_4);
x_18 = l_instInhabitedNat;
x_19 = lean_array_get(x_18, x_1, x_5);
x_20 = l_Lean_Meta_Match_instInhabitedPattern;
x_21 = lean_array_get(x_20, x_2, x_5);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_array_set(x_6, x_19, x_22);
lean_dec(x_19);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_4 = x_17;
x_5 = x_25;
x_6 = x_23;
goto _start;
}
else
{
lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_4);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_11);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" ↦ ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_st_ref_get(x_8, x_9);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 3);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = 0;
x_10 = x_35;
x_11 = x_34;
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
lean_inc(x_4);
x_37 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_4, x_5, x_6, x_7, x_8, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_unbox(x_38);
lean_dec(x_38);
x_10 = x_40;
x_11 = x_39;
goto block_29;
}
block_29:
{
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = l_Lean_Meta_Match_Pattern_toMessageData(x_3);
x_15 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__2;
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
x_22 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_4, x_21, x_5, x_6, x_7, x_8, x_11);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_2);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_2);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("match");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_mkFVar(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_11 = l_Lean_Meta_inferType(x_10, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_getAppNumArgsAux(x_12, x_14);
x_16 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_15);
x_17 = lean_mk_array(x_15, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_15, x_18);
lean_dec(x_15);
x_20 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1(x_1, x_10, x_12, x_17, x_19, x_4, x_5, x_6, x_7, x_13);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_3, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 3);
lean_inc(x_28);
lean_inc(x_25);
x_29 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(x_25, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
x_33 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
x_34 = l_Lean_Name_append(x_32, x_33);
lean_dec(x_32);
lean_inc(x_25);
x_35 = l_Lean_Name_updatePrefix(x_25, x_34);
x_36 = l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(x_35, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_39 = l_Lean_Meta_IndPredBelow_getBelowIndices(x_25, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_30, 3);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_array_get_size(x_40);
x_44 = l_Array_toSubarray___rarg(x_40, x_42, x_43);
x_45 = l_Array_ofSubarray___rarg(x_44);
lean_dec(x_44);
x_46 = lean_array_get_size(x_45);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = 0;
x_49 = x_45;
x_50 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(x_37, x_47, x_48, x_49);
x_51 = x_50;
x_52 = lean_ctor_get(x_37, 4);
lean_inc(x_52);
x_53 = lean_box(0);
x_54 = lean_mk_array(x_52, x_53);
x_55 = l_List_redLength___rarg(x_28);
x_56 = lean_mk_empty_array_with_capacity(x_55);
lean_dec(x_55);
x_57 = l_List_toArrayAux___rarg(x_28, x_56);
x_58 = lean_array_get_size(x_57);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_unsigned_to_nat(1u);
lean_inc(x_58);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_58);
lean_ctor_set(x_61, 2, x_60);
x_62 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3(x_51, x_57, x_61, x_58, x_59, x_54, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_61);
lean_dec(x_57);
lean_dec(x_51);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_List_redLength___rarg(x_27);
x_66 = lean_mk_empty_array_with_capacity(x_65);
lean_dec(x_65);
x_67 = l_List_toArrayAux___rarg(x_27, x_66);
lean_inc(x_1);
x_68 = lean_array_push(x_67, x_1);
x_69 = lean_ctor_get(x_37, 0);
lean_inc(x_69);
lean_dec(x_37);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
lean_inc(x_26);
lean_inc(x_70);
x_71 = l_Lean_mkConst(x_70, x_26);
x_72 = l_Lean_mkAppN(x_71, x_68);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_73 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields(x_1, x_72, x_2, x_63, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
lean_inc(x_76);
x_78 = lean_array_to_list(lean_box(0), x_76);
x_79 = lean_array_to_list(lean_box(0), x_68);
x_80 = lean_array_to_list(lean_box(0), x_77);
x_81 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_81, 0, x_70);
lean_ctor_set(x_81, 1, x_26);
lean_ctor_set(x_81, 2, x_79);
lean_ctor_set(x_81, 3, x_80);
x_82 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___boxed), 9, 4);
lean_closure_set(x_83, 0, x_76);
lean_closure_set(x_83, 1, x_81);
lean_closure_set(x_83, 2, x_3);
lean_closure_set(x_83, 3, x_82);
x_84 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_78, x_83, x_4, x_5, x_6, x_7, x_75);
return x_84;
}
else
{
uint8_t x_85; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = !lean_is_exclusive(x_73);
if (x_85 == 0)
{
return x_73;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_73, 0);
x_87 = lean_ctor_get(x_73, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_73);
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
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_39);
if (x_89 == 0)
{
return x_39;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_39, 0);
x_91 = lean_ctor_get(x_39, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_39);
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
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_36);
if (x_93 == 0)
{
return x_36;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_36, 0);
x_95 = lean_ctor_get(x_36, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_36);
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
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_29);
if (x_97 == 0)
{
return x_29;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_29, 0);
x_99 = lean_ctor_get(x_29, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_29);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
case 5:
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_3);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_3, 0);
x_103 = lean_ctor_get(x_3, 1);
x_104 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_103, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_106, 1);
lean_ctor_set(x_3, 1, x_108);
lean_ctor_set(x_106, 1, x_3);
return x_104;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_106, 0);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_106);
lean_ctor_set(x_3, 1, x_110);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_3);
lean_ctor_set(x_104, 0, x_111);
return x_104;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_104, 0);
x_113 = lean_ctor_get(x_104, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_104);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
lean_ctor_set(x_3, 1, x_115);
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_3);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_113);
return x_118;
}
}
else
{
uint8_t x_119; 
lean_free_object(x_3);
lean_dec(x_102);
x_119 = !lean_is_exclusive(x_104);
if (x_119 == 0)
{
return x_104;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_104, 0);
x_121 = lean_ctor_get(x_104, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_104);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_3, 0);
x_124 = lean_ctor_get(x_3, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_3);
x_125 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_124, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_131 = x_126;
} else {
 lean_dec_ref(x_126);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_123);
lean_ctor_set(x_132, 1, x_130);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_128)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_128;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_127);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_123);
x_135 = lean_ctor_get(x_125, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_125, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_137 = x_125;
} else {
 lean_dec_ref(x_125);
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
default: 
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_139 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_3);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_8);
return x_141;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
x_11 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop(x_1, x_3, x_2, x_4, x_10, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_671____at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
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
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_name_eq(x_6, x_7);
return x_8;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
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
x_26 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_671____at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1(x_24, x_25);
lean_dec(x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_8);
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
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_33);
x_38 = lean_array_set(x_3, x_36, x_37);
lean_dec(x_36);
x_39 = l_Array_append___rarg(x_5, x_32);
lean_dec(x_32);
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_8);
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
x_16 = l_Lean_mkApp(x_1, x_7);
x_17 = l_Lean_Expr_fvarId_x21(x_7);
lean_dec(x_7);
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
x_1 = lean_mk_string("a");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_array_get_size(x_4);
x_13 = lean_array_get_size(x_5);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = lean_array_get(x_15, x_4, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_17 = l_Lean_Meta_inferType(x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___closed__2;
x_21 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_20, x_9, x_10, x_19);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_bindingDomain_x21(x_18);
lean_dec(x_18);
x_25 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___lambda__1), 12, 6);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_5);
lean_closure_set(x_25, 2, x_6);
lean_closure_set(x_25, 3, x_1);
lean_closure_set(x_25, 4, x_2);
lean_closure_set(x_25, 5, x_4);
x_26 = 0;
x_27 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_22, x_26, x_24, x_25, x_7, x_8, x_9, x_10, x_23);
return x_27;
}
else
{
uint8_t x_28; 
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
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
lean_inc(x_32);
lean_dec(x_16);
x_33 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_32);
x_34 = l_Lean_Meta_Match_Pattern_toExpr_visit(x_33, x_32, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_35);
x_37 = l_Lean_mkApp(x_3, x_35);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_35);
x_38 = l_Lean_Meta_inferType(x_35, x_7, x_8, x_9, x_10, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Expr_getAppNumArgsAux(x_39, x_41);
x_43 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_42);
x_44 = lean_mk_array(x_42, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_42, x_45);
lean_dec(x_42);
x_47 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2(x_1, x_2, x_4, x_5, x_6, x_13, x_32, x_35, x_37, x_39, x_44, x_46, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_13);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
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
lean_dec(x_32);
lean_dec(x_13);
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
x_52 = !lean_is_exclusive(x_34);
if (x_52 == 0)
{
return x_34;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_34, 0);
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_34);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_5);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_11);
return x_57;
}
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_671____at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_671____at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2___boxed(lean_object** _args) {
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
x_18 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
return x_18;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_array_set(x_2, x_3, x_14);
x_16 = lean_ctor_get(x_4, 0);
x_17 = l_List_append___rarg(x_5, x_6);
x_18 = lean_array_to_list(lean_box(0), x_15);
lean_inc(x_16);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_array_set(x_2, x_3, x_20);
x_23 = lean_ctor_get(x_4, 0);
x_24 = l_List_append___rarg(x_5, x_6);
x_25 = lean_array_to_list(lean_box(0), x_22);
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
return x_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_12, 0);
x_30 = lean_ctor_get(x_12, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_12);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
lean_closure_set(x_20, 4, x_7);
lean_closure_set(x_20, 5, x_18);
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 2);
lean_inc(x_11);
x_12 = l_List_redLength___rarg(x_11);
x_13 = lean_mk_empty_array_with_capacity(x_12);
lean_dec(x_12);
x_14 = l_List_toArrayAux___rarg(x_11, x_13);
x_15 = l_Lean_Meta_Match_instInhabitedPattern;
x_16 = lean_array_get(x_15, x_14, x_2);
lean_inc(x_10);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__2), 12, 7);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_16);
lean_closure_set(x_17, 3, x_14);
lean_closure_set(x_17, 4, x_2);
lean_closure_set(x_17, 5, x_4);
lean_closure_set(x_17, 6, x_10);
x_18 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_10, x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("motive := ");
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Array_toSubarray___rarg(x_1, x_10, x_2);
x_12 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1;
x_13 = lean_array_push(x_12, x_4);
x_14 = l_Array_ofSubarray___rarg(x_11);
lean_dec(x_11);
x_15 = l_Array_append___rarg(x_14, x_13);
lean_dec(x_13);
x_16 = lean_array_get_size(x_1);
x_17 = l_Array_toSubarray___rarg(x_1, x_2, x_16);
x_18 = l_Array_ofSubarray___rarg(x_17);
lean_dec(x_17);
x_19 = l_Array_append___rarg(x_15, x_18);
lean_dec(x_18);
x_20 = 0;
x_21 = 1;
lean_inc(x_5);
x_22 = l_Lean_Meta_mkLambdaFVars(x_19, x_3, x_20, x_21, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_8, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*1);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_25, 0);
lean_dec(x_30);
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_33 = lean_ctor_get(x_25, 1);
lean_inc(x_33);
lean_dec(x_25);
x_34 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_35 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_34, x_5, x_6, x_7, x_8, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_5);
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_35, 0);
lean_dec(x_39);
lean_ctor_set(x_35, 0, x_23);
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_23);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_dec(x_35);
lean_inc(x_23);
x_43 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_43, 0, x_23);
x_44 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2;
x_45 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_47 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_34, x_47, x_5, x_6, x_7, x_8, x_42);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_23);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_23);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_22);
if (x_53 == 0)
{
return x_22;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_22, 0);
x_55 = lean_ctor_get(x_22, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_22);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("h_below");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_20 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_15, x_19, x_17, x_18, x_6, x_7, x_8, x_9, x_16);
return x_20;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___boxed), 10, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
x_11 = l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_10;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_LocalDecl_toExpr(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Nat_repr(x_1);
x_3 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___rarg), 1, 0);
return x_4;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("alt ");
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(":\n");
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("xs = ");
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("; oldFVars = ");
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("; fvars = ");
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("; new = ");
return x_1;
}
}
static lean_object* _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_15 = l_List_redLength___rarg(x_1);
x_16 = lean_mk_empty_array_with_capacity(x_15);
lean_dec(x_15);
x_17 = l_List_toArrayAux___rarg(x_1, x_16);
x_18 = l_List_redLength___rarg(x_2);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_dec(x_18);
x_20 = l_List_toArrayAux___rarg(x_2, x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_23 = 0;
x_24 = x_20;
x_25 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(x_22, x_23, x_24);
x_26 = x_25;
x_27 = lean_array_get_size(x_17);
x_28 = lean_array_get_size(x_26);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_nat_dec_eq(x_27, x_29);
lean_inc(x_27);
lean_inc(x_26);
x_31 = l_Array_toSubarray___rarg(x_26, x_29, x_27);
x_32 = l_Array_ofSubarray___rarg(x_31);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_13, x_14);
if (x_30 == 0)
{
lean_dec(x_28);
x_34 = x_8;
goto block_147;
}
else
{
uint8_t x_148; 
x_148 = lean_nat_dec_eq(x_28, x_29);
lean_dec(x_28);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_array_get_size(x_8);
x_150 = lean_unsigned_to_nat(1u);
x_151 = l_Array_toSubarray___rarg(x_8, x_150, x_149);
x_152 = l_Array_ofSubarray___rarg(x_151);
lean_dec(x_151);
x_34 = x_152;
goto block_147;
}
else
{
x_34 = x_8;
goto block_147;
}
}
block_147:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_93; lean_object* x_94; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_inc(x_27);
lean_inc(x_34);
x_35 = l_Array_toSubarray___rarg(x_34, x_29, x_27);
x_36 = l_Array_ofSubarray___rarg(x_35);
lean_dec(x_35);
x_37 = l_Lean_Expr_replaceFVars(x_9, x_36, x_32);
lean_dec(x_36);
x_136 = lean_ctor_get(x_33, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 3);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_ctor_get_uint8(x_137, sizeof(void*)*1);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_33, 1);
lean_inc(x_139);
lean_dec(x_33);
x_140 = 0;
x_93 = x_140;
x_94 = x_139;
goto block_135;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_141 = lean_ctor_get(x_33, 1);
lean_inc(x_141);
lean_dec(x_33);
x_142 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_143 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_142, x_10, x_11, x_12, x_13, x_141);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_unbox(x_144);
lean_dec(x_144);
x_93 = x_146;
x_94 = x_145;
goto block_135;
}
block_92:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; 
x_39 = lean_array_get_size(x_34);
lean_inc(x_27);
x_40 = l_Array_toSubarray___rarg(x_34, x_27, x_39);
x_41 = l_Array_ofSubarray___rarg(x_40);
lean_dec(x_40);
x_42 = l_Array_append___rarg(x_32, x_41);
lean_dec(x_41);
x_43 = lean_array_get_size(x_26);
x_44 = l_Array_toSubarray___rarg(x_26, x_27, x_43);
x_45 = l_Array_ofSubarray___rarg(x_44);
lean_dec(x_44);
x_46 = l_Array_append___rarg(x_42, x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = 1;
lean_inc(x_10);
x_49 = l_Lean_Meta_mkLambdaFVars(x_46, x_37, x_47, x_48, x_10, x_11, x_12, x_13, x_38);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
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
x_77 = lean_st_ref_get(x_13, x_51);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 3);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_ctor_get_uint8(x_79, sizeof(void*)*1);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_53 = x_47;
x_54 = x_81;
goto block_76;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_dec(x_77);
x_83 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_84 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_83, x_10, x_11, x_12, x_13, x_82);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_unbox(x_85);
lean_dec(x_85);
x_53 = x_87;
x_54 = x_86;
goto block_76;
}
block_76:
{
if (x_53 == 0)
{
lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_52);
x_56 = l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___rarg(x_6);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2;
x_59 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_7);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__2;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_50);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_50);
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_71 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_70, x_69, x_10, x_11, x_12, x_13, x_54);
lean_dec(x_10);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_50);
return x_71;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_50);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
x_88 = !lean_is_exclusive(x_49);
if (x_88 == 0)
{
return x_49;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_49, 0);
x_90 = lean_ctor_get(x_49, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_49);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
block_135:
{
if (x_93 == 0)
{
lean_dec(x_17);
x_38 = x_94;
goto block_92;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_inc(x_34);
x_95 = lean_array_to_list(lean_box(0), x_34);
x_96 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_95);
x_97 = l_Lean_MessageData_ofList(x_96);
lean_dec(x_96);
x_98 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8;
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_usize_of_nat(x_27);
x_103 = x_17;
x_104 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(x_102, x_23, x_103);
x_105 = x_104;
x_106 = lean_array_to_list(lean_box(0), x_105);
x_107 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_106);
x_108 = l_Lean_MessageData_ofList(x_107);
lean_dec(x_107);
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_101);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10;
x_111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
lean_inc(x_26);
x_112 = lean_array_to_list(lean_box(0), x_26);
x_113 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_112);
x_114 = l_Lean_MessageData_ofList(x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__12;
x_117 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_array_get_size(x_34);
lean_inc(x_27);
lean_inc(x_34);
x_119 = l_Array_toSubarray___rarg(x_34, x_27, x_118);
x_120 = l_Array_ofSubarray___rarg(x_119);
lean_dec(x_119);
lean_inc(x_32);
x_121 = l_Array_append___rarg(x_32, x_120);
lean_dec(x_120);
x_122 = lean_array_get_size(x_26);
lean_inc(x_27);
lean_inc(x_26);
x_123 = l_Array_toSubarray___rarg(x_26, x_27, x_122);
x_124 = l_Array_ofSubarray___rarg(x_123);
lean_dec(x_123);
x_125 = l_Array_append___rarg(x_121, x_124);
lean_dec(x_124);
x_126 = lean_array_to_list(lean_box(0), x_125);
x_127 = l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(x_126);
x_128 = l_Lean_MessageData_ofList(x_127);
lean_dec(x_127);
x_129 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_129, 0, x_117);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_133 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_132, x_131, x_10, x_11, x_12, x_13, x_94);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_38 = x_134;
goto block_92;
}
}
}
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_25 = l_List_append___rarg(x_23, x_24);
lean_inc(x_20);
lean_inc(x_6);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_26 = lean_alloc_closure((void*)(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___boxed), 14, 7);
lean_closure_set(x_26, 0, x_23);
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_1);
lean_closure_set(x_26, 3, x_2);
lean_closure_set(x_26, 4, x_3);
lean_closure_set(x_26, 5, x_6);
lean_closure_set(x_26, 6, x_20);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg), 7, 2);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_8);
lean_ctor_set(x_38, 1, x_13);
return x_38;
}
}
}
lean_object* l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_List_append___rarg(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_Meta_Match_Pattern_toMessageData(x_10);
x_13 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(x_11, x_2, x_3, x_4, x_5, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_12);
lean_ctor_set(x_13, 0, x_1);
return x_13;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l_Lean_Meta_Match_Pattern_toMessageData(x_19);
x_22 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(x_20, x_2, x_3, x_4, x_5, x_6);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 2);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(x_11, x_3, x_4, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_6, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_1 = x_10;
x_2 = x_20;
x_7 = x_19;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_24 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_23, x_3, x_4, x_5, x_6, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_13);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_1 = x_10;
x_2 = x_28;
x_7 = x_27;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l_List_map___at_Lean_Meta_Match_Alt_toMessageData___spec__2(x_13);
x_32 = l_Lean_MessageData_ofList(x_31);
lean_dec(x_31);
x_33 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_34 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_23, x_35, x_3, x_4, x_5, x_6, x_30);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_box(0);
x_1 = x_10;
x_2 = x_38;
x_7 = x_37;
goto _start;
}
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_array_push(x_1, x_3);
x_10 = 0;
x_11 = 1;
x_12 = l_Lean_Meta_mkForallFVars(x_9, x_2, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
x_23 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_19, x_22, x_16, x_21, x_6, x_7, x_8, x_9, x_20);
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
x_56 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(x_52, x_55, x_49, x_54, x_6, x_7, x_8, x_9, x_53);
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_14 = lean_ctor_get(x_11, 2);
lean_inc(x_14);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_2);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2___boxed), 10, 3);
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
lean_inc(x_28);
lean_inc(x_11);
lean_inc(x_1);
x_40 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(x_1, x_11, x_28, x_36, x_37, x_39, lean_box(0), x_38, x_5, x_6, x_7, x_8, x_29);
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
x_48 = l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__5(x_47, x_28);
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
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_14, x_52);
lean_dec(x_14);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_25);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_55 = l_Lean_Meta_Match_mkMatcher(x_54, x_5, x_6, x_7, x_8, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 3);
lean_inc(x_58);
lean_inc(x_58);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = lean_apply_5(x_58, x_5, x_6, x_7, x_8, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
lean_inc(x_61);
x_62 = l_Lean_Meta_check(x_61, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
x_65 = lean_ctor_get(x_1, 5);
lean_inc(x_65);
lean_dec(x_1);
x_66 = lean_array_push(x_65, x_3);
x_67 = l_Lean_mkApp(x_61, x_24);
x_68 = l_Lean_mkAppN(x_67, x_66);
lean_dec(x_66);
x_69 = l_Lean_mkAppN(x_68, x_41);
lean_dec(x_41);
lean_ctor_set(x_20, 1, x_58);
lean_ctor_set(x_20, 0, x_69);
lean_ctor_set(x_62, 0, x_20);
return x_62;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_62, 1);
lean_inc(x_70);
lean_dec(x_62);
x_71 = lean_ctor_get(x_1, 5);
lean_inc(x_71);
lean_dec(x_1);
x_72 = lean_array_push(x_71, x_3);
x_73 = l_Lean_mkApp(x_61, x_24);
x_74 = l_Lean_mkAppN(x_73, x_72);
lean_dec(x_72);
x_75 = l_Lean_mkAppN(x_74, x_41);
lean_dec(x_41);
lean_ctor_set(x_20, 1, x_58);
lean_ctor_set(x_20, 0, x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_20);
lean_ctor_set(x_76, 1, x_70);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_62);
if (x_77 == 0)
{
return x_62;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_62, 0);
x_79 = lean_ctor_get(x_62, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_62);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_59);
if (x_81 == 0)
{
return x_59;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_59, 0);
x_83 = lean_ctor_get(x_59, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_59);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_55);
if (x_85 == 0)
{
return x_55;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_55, 0);
x_87 = lean_ctor_get(x_55, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_55);
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
x_89 = !lean_is_exclusive(x_50);
if (x_89 == 0)
{
return x_50;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_50, 0);
x_91 = lean_ctor_get(x_50, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_50);
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
x_93 = !lean_is_exclusive(x_40);
if (x_93 == 0)
{
return x_40;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_40, 0);
x_95 = lean_ctor_get(x_40, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_40);
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
x_97 = !lean_is_exclusive(x_27);
if (x_97 == 0)
{
return x_27;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_27, 0);
x_99 = lean_ctor_get(x_27, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_27);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_20, 0);
x_102 = lean_ctor_get(x_20, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_20);
x_103 = lean_ctor_get(x_11, 3);
lean_inc(x_103);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_103);
x_104 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(x_2, x_4, x_22, x_103, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1;
lean_inc(x_105);
x_108 = l_List_zipWith___rarg(x_107, x_103, x_105);
x_109 = l_List_redLength___rarg(x_108);
x_110 = lean_mk_empty_array_with_capacity(x_109);
lean_dec(x_109);
x_111 = l_List_toArrayAux___rarg(x_108, x_110);
x_112 = lean_ctor_get(x_1, 7);
lean_inc(x_112);
x_113 = l_Array_zip___rarg(x_111, x_112);
lean_dec(x_112);
lean_dec(x_111);
x_114 = lean_array_get_size(x_113);
x_115 = lean_mk_empty_array_with_capacity(x_114);
x_116 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_105);
lean_inc(x_11);
lean_inc(x_1);
x_117 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(x_1, x_11, x_105, x_113, x_114, x_116, lean_box(0), x_115, x_5, x_6, x_7, x_8, x_106);
lean_dec(x_113);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_11, 0);
lean_inc(x_120);
lean_dec(x_11);
x_121 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_120, x_7, x_8, x_119);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_box(0);
lean_inc(x_105);
x_125 = l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__5(x_124, x_105);
lean_inc(x_105);
x_126 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3___boxed), 6, 1);
lean_closure_set(x_126, 0, x_105);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_127 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_125, x_126, x_5, x_6, x_7, x_8, x_123);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_nat_add(x_14, x_129);
lean_dec(x_14);
x_131 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_131, 0, x_122);
lean_ctor_set(x_131, 1, x_102);
lean_ctor_set(x_131, 2, x_130);
lean_ctor_set(x_131, 3, x_105);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_132 = l_Lean_Meta_Match_mkMatcher(x_131, x_5, x_6, x_7, x_8, x_128);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_133, 3);
lean_inc(x_135);
lean_inc(x_135);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_136 = lean_apply_5(x_135, x_5, x_6, x_7, x_8, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
lean_dec(x_133);
lean_inc(x_138);
x_139 = l_Lean_Meta_check(x_138, x_5, x_6, x_7, x_8, x_137);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_141 = x_139;
} else {
 lean_dec_ref(x_139);
 x_141 = lean_box(0);
}
x_142 = lean_ctor_get(x_1, 5);
lean_inc(x_142);
lean_dec(x_1);
x_143 = lean_array_push(x_142, x_3);
x_144 = l_Lean_mkApp(x_138, x_101);
x_145 = l_Lean_mkAppN(x_144, x_143);
lean_dec(x_143);
x_146 = l_Lean_mkAppN(x_145, x_118);
lean_dec(x_118);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_135);
if (lean_is_scalar(x_141)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_141;
}
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_140);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_118);
lean_dec(x_101);
lean_dec(x_3);
lean_dec(x_1);
x_149 = lean_ctor_get(x_139, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_151 = x_139;
} else {
 lean_dec_ref(x_139);
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
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_118);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
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
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_118);
lean_dec(x_101);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_157 = lean_ctor_get(x_132, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_132, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_159 = x_132;
} else {
 lean_dec_ref(x_132);
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
lean_dec(x_122);
lean_dec(x_118);
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_161 = lean_ctor_get(x_127, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_127, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_163 = x_127;
} else {
 lean_dec_ref(x_127);
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
lean_dec(x_105);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_165 = lean_ctor_get(x_117, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_117, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_167 = x_117;
} else {
 lean_dec_ref(x_117);
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
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_169 = lean_ctor_get(x_104, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_104, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_171 = x_104;
} else {
 lean_dec_ref(x_104);
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
}
else
{
uint8_t x_173; 
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
x_173 = !lean_is_exclusive(x_17);
if (x_173 == 0)
{
return x_17;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_17, 0);
x_175 = lean_ctor_get(x_17, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_17);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_10);
if (x_177 == 0)
{
return x_10;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_10, 0);
x_179 = lean_ctor_get(x_10, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_10);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_14;
}
}
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_apply_2(x_4, x_1, x_2);
return x_5;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_apply_2(x_4, x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_findBelowIdx_match__1___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_IndPredBelow_findBelowIdx_match__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_environment_find(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; lean_object* x_13; 
x_12 = 0;
x_13 = lean_box(x_12);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 5)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_isInductivePredicate_visit(x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
uint8_t x_20; lean_object* x_21; 
lean_dec(x_14);
x_20 = 0;
x_21 = lean_box(x_20);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_environment_find(x_24, x_1);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
if (lean_obj_tag(x_29) == 5)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_isInductivePredicate_visit(x_32);
lean_dec(x_32);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
return x_35;
}
else
{
uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_29);
x_36 = 0;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_23);
return x_38;
}
}
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_3 == x_4;
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
x_17 = x_3 + x_16;
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
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("could not find below term in the local context");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Found below term in the local context: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
x_13 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_15, x_8, x_9, x_10, x_11, x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
lean_ctor_set(x_21, 0, x_3);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_19, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_72; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
lean_inc(x_8);
x_35 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_32, x_34, x_8, x_9, x_10, x_11, x_31);
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
x_39 = l_Lean_Expr_mvarId_x21(x_36);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_72 = l_Lean_Meta_ppGoal(x_39, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_130 = lean_st_ref_get(x_11, x_74);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 3);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_ctor_get_uint8(x_132, sizeof(void*)*1);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_73);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_dec(x_130);
x_75 = x_134;
goto block_129;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
lean_dec(x_130);
x_136 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_137 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_136, x_8, x_9, x_10, x_11, x_135);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_unbox(x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; 
lean_dec(x_73);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_dec(x_137);
x_75 = x_140;
goto block_129;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_137, 1);
lean_inc(x_141);
lean_dec(x_137);
x_142 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_142, 0, x_73);
x_143 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_144 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
x_146 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_136, x_145, x_8, x_9, x_10, x_11, x_141);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_75 = x_147;
goto block_129;
}
}
block_129:
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_77 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_39, x_76, x_8, x_9, x_10, x_11, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_st_ref_get(x_11, x_80);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_82, 3);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get_uint8(x_83, sizeof(void*)*1);
lean_dec(x_83);
if (x_84 == 0)
{
uint8_t x_85; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_85 = !lean_is_exclusive(x_81);
if (x_85 == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_81, 0);
lean_dec(x_86);
lean_ctor_set(x_81, 0, x_3);
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_3);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
lean_dec(x_81);
x_90 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_91 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_90, x_8, x_9, x_10, x_11, x_89);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
lean_ctor_set(x_91, 0, x_3);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_91, 1);
lean_inc(x_96);
lean_dec(x_91);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_3);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_98 = lean_ctor_get(x_91, 1);
lean_inc(x_98);
lean_dec(x_91);
x_99 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_100 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_90, x_99, x_8, x_9, x_10, x_11, x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_100, 0);
lean_dec(x_102);
lean_ctor_set(x_100, 0, x_3);
return x_100;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_3);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_105 = lean_ctor_get(x_77, 1);
lean_inc(x_105);
lean_dec(x_77);
x_106 = lean_st_ref_get(x_11, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_107, 3);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get_uint8(x_108, sizeof(void*)*1);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
lean_dec(x_106);
x_40 = x_110;
goto block_71;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_113 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_112, x_8, x_9, x_10, x_11, x_111);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_40 = x_116;
goto block_71;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
lean_dec(x_113);
lean_inc(x_36);
x_118 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_118, 0, x_36);
x_119 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_120 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
x_121 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_112, x_122, x_8, x_9, x_10, x_11, x_117);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_40 = x_124;
goto block_71;
}
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_125 = !lean_is_exclusive(x_77);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_77, 0);
lean_dec(x_126);
lean_ctor_set_tag(x_77, 0);
lean_ctor_set(x_77, 0, x_3);
return x_77;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_77, 1);
lean_inc(x_127);
lean_dec(x_77);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_3);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
}
else
{
uint8_t x_148; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_148 = !lean_is_exclusive(x_72);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_72, 0);
lean_dec(x_149);
lean_ctor_set_tag(x_72, 0);
lean_ctor_set(x_72, 0, x_3);
return x_72;
}
else
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_72, 1);
lean_inc(x_150);
lean_dec(x_72);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_3);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
block_71:
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_array_get_size(x_1);
x_42 = lean_nat_dec_lt(x_16, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_33)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_33;
}
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_19);
if (lean_is_scalar(x_20)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_20;
}
lean_ctor_set(x_44, 0, x_43);
if (lean_is_scalar(x_38)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_38;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_41, x_41);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_33)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_33;
}
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_19);
if (lean_is_scalar(x_20)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_20;
}
lean_ctor_set(x_48, 0, x_47);
if (lean_is_scalar(x_38)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_38;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
lean_dec(x_38);
x_50 = 0;
x_51 = lean_usize_of_nat(x_41);
lean_dec(x_41);
lean_inc(x_36);
x_52 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_36, x_1, x_50, x_51, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_52);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_52, 0);
lean_dec(x_56);
if (lean_is_scalar(x_33)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_33;
}
lean_ctor_set(x_57, 0, x_36);
lean_ctor_set(x_57, 1, x_19);
if (lean_is_scalar(x_20)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_20;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_52, 0, x_58);
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_52, 1);
lean_inc(x_59);
lean_dec(x_52);
if (lean_is_scalar(x_33)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_33;
}
lean_ctor_set(x_60, 0, x_36);
lean_ctor_set(x_60, 1, x_19);
if (lean_is_scalar(x_20)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_20;
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
x_63 = !lean_is_exclusive(x_52);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_52, 0);
lean_dec(x_64);
lean_ctor_set(x_52, 0, x_3);
return x_52;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_52, 1);
lean_inc(x_65);
lean_dec(x_52);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
x_67 = !lean_is_exclusive(x_52);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_52, 0);
lean_dec(x_68);
lean_ctor_set_tag(x_52, 0);
lean_ctor_set(x_52, 0, x_3);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_52, 1);
lean_inc(x_69);
lean_dec(x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_152 = !lean_is_exclusive(x_29);
if (x_152 == 0)
{
return x_29;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_29, 0);
x_154 = lean_ctor_get(x_29, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_29);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
}
}
case 1:
{
lean_object* x_156; 
lean_dec(x_7);
lean_dec(x_6);
x_156 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_3);
lean_ctor_set(x_157, 1, x_12);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_unsigned_to_nat(0u);
x_160 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
lean_dec(x_158);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_3);
lean_ctor_set(x_161, 1, x_12);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_163 = x_160;
} else {
 lean_dec_ref(x_160);
 x_163 = lean_box(0);
}
x_164 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_158, x_8, x_9, x_10, x_11, x_12);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_unbox(x_165);
lean_dec(x_165);
if (x_166 == 0)
{
uint8_t x_167; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_167 = !lean_is_exclusive(x_164);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_164, 0);
lean_dec(x_168);
lean_ctor_set(x_164, 0, x_3);
return x_164;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_164, 1);
lean_inc(x_169);
lean_dec(x_164);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_3);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_164, 1);
lean_inc(x_171);
lean_dec(x_164);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_172 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_162, x_8, x_9, x_10, x_11, x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_215; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_176 = x_173;
} else {
 lean_dec_ref(x_173);
 x_176 = lean_box(0);
}
x_177 = lean_box(0);
lean_inc(x_8);
x_178 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_175, x_177, x_8, x_9, x_10, x_11, x_174);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
x_182 = l_Lean_Expr_mvarId_x21(x_179);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_215 = l_Lean_Meta_ppGoal(x_182, x_8, x_9, x_10, x_11, x_180);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_273 = lean_st_ref_get(x_11, x_217);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_274, 3);
lean_inc(x_275);
lean_dec(x_274);
x_276 = lean_ctor_get_uint8(x_275, sizeof(void*)*1);
lean_dec(x_275);
if (x_276 == 0)
{
lean_object* x_277; 
lean_dec(x_216);
x_277 = lean_ctor_get(x_273, 1);
lean_inc(x_277);
lean_dec(x_273);
x_218 = x_277;
goto block_272;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_278 = lean_ctor_get(x_273, 1);
lean_inc(x_278);
lean_dec(x_273);
x_279 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_280 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_279, x_8, x_9, x_10, x_11, x_278);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_unbox(x_281);
lean_dec(x_281);
if (x_282 == 0)
{
lean_object* x_283; 
lean_dec(x_216);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_218 = x_283;
goto block_272;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_280, 1);
lean_inc(x_284);
lean_dec(x_280);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_216);
x_286 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_287 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_287, 0, x_286);
lean_ctor_set(x_287, 1, x_285);
x_288 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
x_289 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_279, x_288, x_8, x_9, x_10, x_11, x_284);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
x_218 = x_290;
goto block_272;
}
}
block_272:
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_220 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_182, x_219, x_8, x_9, x_10, x_11, x_218);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; uint8_t x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_163);
lean_dec(x_162);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_224 = lean_st_ref_get(x_11, x_223);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 3);
lean_inc(x_226);
lean_dec(x_225);
x_227 = lean_ctor_get_uint8(x_226, sizeof(void*)*1);
lean_dec(x_226);
if (x_227 == 0)
{
uint8_t x_228; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_228 = !lean_is_exclusive(x_224);
if (x_228 == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_224, 0);
lean_dec(x_229);
lean_ctor_set(x_224, 0, x_3);
return x_224;
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_224, 1);
lean_inc(x_230);
lean_dec(x_224);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_3);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_232 = lean_ctor_get(x_224, 1);
lean_inc(x_232);
lean_dec(x_224);
x_233 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_234 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_233, x_8, x_9, x_10, x_11, x_232);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
uint8_t x_237; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_237 = !lean_is_exclusive(x_234);
if (x_237 == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_234, 0);
lean_dec(x_238);
lean_ctor_set(x_234, 0, x_3);
return x_234;
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_234, 1);
lean_inc(x_239);
lean_dec(x_234);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_3);
lean_ctor_set(x_240, 1, x_239);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_241 = lean_ctor_get(x_234, 1);
lean_inc(x_241);
lean_dec(x_234);
x_242 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_243 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_233, x_242, x_8, x_9, x_10, x_11, x_241);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_244 = !lean_is_exclusive(x_243);
if (x_244 == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_243, 0);
lean_dec(x_245);
lean_ctor_set(x_243, 0, x_3);
return x_243;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_dec(x_243);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_3);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_248 = lean_ctor_get(x_220, 1);
lean_inc(x_248);
lean_dec(x_220);
x_249 = lean_st_ref_get(x_11, x_248);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_250, 3);
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_ctor_get_uint8(x_251, sizeof(void*)*1);
lean_dec(x_251);
if (x_252 == 0)
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_249, 1);
lean_inc(x_253);
lean_dec(x_249);
x_183 = x_253;
goto block_214;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_254 = lean_ctor_get(x_249, 1);
lean_inc(x_254);
lean_dec(x_249);
x_255 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_256 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_255, x_8, x_9, x_10, x_11, x_254);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_unbox(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
lean_dec(x_256);
x_183 = x_259;
goto block_214;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_260 = lean_ctor_get(x_256, 1);
lean_inc(x_260);
lean_dec(x_256);
lean_inc(x_179);
x_261 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_261, 0, x_179);
x_262 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_263 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_261);
x_264 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_265 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_255, x_265, x_8, x_9, x_10, x_11, x_260);
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_183 = x_267;
goto block_214;
}
}
}
}
else
{
uint8_t x_268; 
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_268 = !lean_is_exclusive(x_220);
if (x_268 == 0)
{
lean_object* x_269; 
x_269 = lean_ctor_get(x_220, 0);
lean_dec(x_269);
lean_ctor_set_tag(x_220, 0);
lean_ctor_set(x_220, 0, x_3);
return x_220;
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_220, 1);
lean_inc(x_270);
lean_dec(x_220);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_3);
lean_ctor_set(x_271, 1, x_270);
return x_271;
}
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_291 = !lean_is_exclusive(x_215);
if (x_291 == 0)
{
lean_object* x_292; 
x_292 = lean_ctor_get(x_215, 0);
lean_dec(x_292);
lean_ctor_set_tag(x_215, 0);
lean_ctor_set(x_215, 0, x_3);
return x_215;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_215, 1);
lean_inc(x_293);
lean_dec(x_215);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_3);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
block_214:
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_array_get_size(x_1);
x_185 = lean_nat_dec_lt(x_159, x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_184);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_176)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_176;
}
lean_ctor_set(x_186, 0, x_179);
lean_ctor_set(x_186, 1, x_162);
if (lean_is_scalar(x_163)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_163;
}
lean_ctor_set(x_187, 0, x_186);
if (lean_is_scalar(x_181)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_181;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_183);
return x_188;
}
else
{
uint8_t x_189; 
x_189 = lean_nat_dec_le(x_184, x_184);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_184);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_176)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_176;
}
lean_ctor_set(x_190, 0, x_179);
lean_ctor_set(x_190, 1, x_162);
if (lean_is_scalar(x_163)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_163;
}
lean_ctor_set(x_191, 0, x_190);
if (lean_is_scalar(x_181)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_181;
}
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_183);
return x_192;
}
else
{
size_t x_193; size_t x_194; lean_object* x_195; 
lean_dec(x_181);
x_193 = 0;
x_194 = lean_usize_of_nat(x_184);
lean_dec(x_184);
lean_inc(x_179);
x_195 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_179, x_1, x_193, x_194, x_8, x_9, x_10, x_11, x_183);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
uint8_t x_198; 
lean_dec(x_3);
x_198 = !lean_is_exclusive(x_195);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_195, 0);
lean_dec(x_199);
if (lean_is_scalar(x_176)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_176;
}
lean_ctor_set(x_200, 0, x_179);
lean_ctor_set(x_200, 1, x_162);
if (lean_is_scalar(x_163)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_163;
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_195, 0, x_201);
return x_195;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_202 = lean_ctor_get(x_195, 1);
lean_inc(x_202);
lean_dec(x_195);
if (lean_is_scalar(x_176)) {
 x_203 = lean_alloc_ctor(0, 2, 0);
} else {
 x_203 = x_176;
}
lean_ctor_set(x_203, 0, x_179);
lean_ctor_set(x_203, 1, x_162);
if (lean_is_scalar(x_163)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_163;
}
lean_ctor_set(x_204, 0, x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_202);
return x_205;
}
}
else
{
uint8_t x_206; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_163);
lean_dec(x_162);
x_206 = !lean_is_exclusive(x_195);
if (x_206 == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_195, 0);
lean_dec(x_207);
lean_ctor_set(x_195, 0, x_3);
return x_195;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_195, 1);
lean_inc(x_208);
lean_dec(x_195);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_3);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_163);
lean_dec(x_162);
x_210 = !lean_is_exclusive(x_195);
if (x_210 == 0)
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_195, 0);
lean_dec(x_211);
lean_ctor_set_tag(x_195, 0);
lean_ctor_set(x_195, 0, x_3);
return x_195;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_195, 1);
lean_inc(x_212);
lean_dec(x_195);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_3);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_295 = !lean_is_exclusive(x_172);
if (x_295 == 0)
{
return x_172;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_172, 0);
x_297 = lean_ctor_get(x_172, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_172);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
}
}
}
case 2:
{
lean_object* x_299; 
lean_dec(x_7);
lean_dec(x_6);
x_299 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_3);
lean_ctor_set(x_300, 1, x_12);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_299, 0);
lean_inc(x_301);
lean_dec(x_299);
x_302 = lean_unsigned_to_nat(0u);
x_303 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; 
lean_dec(x_301);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_3);
lean_ctor_set(x_304, 1, x_12);
return x_304;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 x_306 = x_303;
} else {
 lean_dec_ref(x_303);
 x_306 = lean_box(0);
}
x_307 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_301, x_8, x_9, x_10, x_11, x_12);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_unbox(x_308);
lean_dec(x_308);
if (x_309 == 0)
{
uint8_t x_310; 
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_310 = !lean_is_exclusive(x_307);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_ctor_get(x_307, 0);
lean_dec(x_311);
lean_ctor_set(x_307, 0, x_3);
return x_307;
}
else
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_307, 1);
lean_inc(x_312);
lean_dec(x_307);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_3);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_307, 1);
lean_inc(x_314);
lean_dec(x_307);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_315 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_305, x_8, x_9, x_10, x_11, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_358; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_319 = x_316;
} else {
 lean_dec_ref(x_316);
 x_319 = lean_box(0);
}
x_320 = lean_box(0);
lean_inc(x_8);
x_321 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_318, x_320, x_8, x_9, x_10, x_11, x_317);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_324 = x_321;
} else {
 lean_dec_ref(x_321);
 x_324 = lean_box(0);
}
x_325 = l_Lean_Expr_mvarId_x21(x_322);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_358 = l_Lean_Meta_ppGoal(x_325, x_8, x_9, x_10, x_11, x_323);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_416 = lean_st_ref_get(x_11, x_360);
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_417, 3);
lean_inc(x_418);
lean_dec(x_417);
x_419 = lean_ctor_get_uint8(x_418, sizeof(void*)*1);
lean_dec(x_418);
if (x_419 == 0)
{
lean_object* x_420; 
lean_dec(x_359);
x_420 = lean_ctor_get(x_416, 1);
lean_inc(x_420);
lean_dec(x_416);
x_361 = x_420;
goto block_415;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_421 = lean_ctor_get(x_416, 1);
lean_inc(x_421);
lean_dec(x_416);
x_422 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_423 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_422, x_8, x_9, x_10, x_11, x_421);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_unbox(x_424);
lean_dec(x_424);
if (x_425 == 0)
{
lean_object* x_426; 
lean_dec(x_359);
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
lean_dec(x_423);
x_361 = x_426;
goto block_415;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_427 = lean_ctor_get(x_423, 1);
lean_inc(x_427);
lean_dec(x_423);
x_428 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_428, 0, x_359);
x_429 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_430 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_428);
x_431 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_429);
x_432 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_422, x_431, x_8, x_9, x_10, x_11, x_427);
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
x_361 = x_433;
goto block_415;
}
}
block_415:
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_363 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_325, x_362, x_8, x_9, x_10, x_11, x_361);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; uint8_t x_365; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_unbox(x_364);
lean_dec(x_364);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; 
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_319);
lean_dec(x_306);
lean_dec(x_305);
x_366 = lean_ctor_get(x_363, 1);
lean_inc(x_366);
lean_dec(x_363);
x_367 = lean_st_ref_get(x_11, x_366);
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_368, 3);
lean_inc(x_369);
lean_dec(x_368);
x_370 = lean_ctor_get_uint8(x_369, sizeof(void*)*1);
lean_dec(x_369);
if (x_370 == 0)
{
uint8_t x_371; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_371 = !lean_is_exclusive(x_367);
if (x_371 == 0)
{
lean_object* x_372; 
x_372 = lean_ctor_get(x_367, 0);
lean_dec(x_372);
lean_ctor_set(x_367, 0, x_3);
return x_367;
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_367, 1);
lean_inc(x_373);
lean_dec(x_367);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_3);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; 
x_375 = lean_ctor_get(x_367, 1);
lean_inc(x_375);
lean_dec(x_367);
x_376 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_377 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_376, x_8, x_9, x_10, x_11, x_375);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_unbox(x_378);
lean_dec(x_378);
if (x_379 == 0)
{
uint8_t x_380; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_380 = !lean_is_exclusive(x_377);
if (x_380 == 0)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_377, 0);
lean_dec(x_381);
lean_ctor_set(x_377, 0, x_3);
return x_377;
}
else
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_377, 1);
lean_inc(x_382);
lean_dec(x_377);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_3);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_384 = lean_ctor_get(x_377, 1);
lean_inc(x_384);
lean_dec(x_377);
x_385 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_386 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_376, x_385, x_8, x_9, x_10, x_11, x_384);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_387 = !lean_is_exclusive(x_386);
if (x_387 == 0)
{
lean_object* x_388; 
x_388 = lean_ctor_get(x_386, 0);
lean_dec(x_388);
lean_ctor_set(x_386, 0, x_3);
return x_386;
}
else
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_386, 1);
lean_inc(x_389);
lean_dec(x_386);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_3);
lean_ctor_set(x_390, 1, x_389);
return x_390;
}
}
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; uint8_t x_395; 
x_391 = lean_ctor_get(x_363, 1);
lean_inc(x_391);
lean_dec(x_363);
x_392 = lean_st_ref_get(x_11, x_391);
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_393, 3);
lean_inc(x_394);
lean_dec(x_393);
x_395 = lean_ctor_get_uint8(x_394, sizeof(void*)*1);
lean_dec(x_394);
if (x_395 == 0)
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_392, 1);
lean_inc(x_396);
lean_dec(x_392);
x_326 = x_396;
goto block_357;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_397 = lean_ctor_get(x_392, 1);
lean_inc(x_397);
lean_dec(x_392);
x_398 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_399 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_398, x_8, x_9, x_10, x_11, x_397);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_unbox(x_400);
lean_dec(x_400);
if (x_401 == 0)
{
lean_object* x_402; 
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
lean_dec(x_399);
x_326 = x_402;
goto block_357;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_403 = lean_ctor_get(x_399, 1);
lean_inc(x_403);
lean_dec(x_399);
lean_inc(x_322);
x_404 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_404, 0, x_322);
x_405 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_406 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_404);
x_407 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_408 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
x_409 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_398, x_408, x_8, x_9, x_10, x_11, x_403);
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
lean_dec(x_409);
x_326 = x_410;
goto block_357;
}
}
}
}
else
{
uint8_t x_411; 
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_319);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_411 = !lean_is_exclusive(x_363);
if (x_411 == 0)
{
lean_object* x_412; 
x_412 = lean_ctor_get(x_363, 0);
lean_dec(x_412);
lean_ctor_set_tag(x_363, 0);
lean_ctor_set(x_363, 0, x_3);
return x_363;
}
else
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_363, 1);
lean_inc(x_413);
lean_dec(x_363);
x_414 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_414, 0, x_3);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_322);
lean_dec(x_319);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_434 = !lean_is_exclusive(x_358);
if (x_434 == 0)
{
lean_object* x_435; 
x_435 = lean_ctor_get(x_358, 0);
lean_dec(x_435);
lean_ctor_set_tag(x_358, 0);
lean_ctor_set(x_358, 0, x_3);
return x_358;
}
else
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_358, 1);
lean_inc(x_436);
lean_dec(x_358);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_3);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
block_357:
{
lean_object* x_327; uint8_t x_328; 
x_327 = lean_array_get_size(x_1);
x_328 = lean_nat_dec_lt(x_302, x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_327);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_319)) {
 x_329 = lean_alloc_ctor(0, 2, 0);
} else {
 x_329 = x_319;
}
lean_ctor_set(x_329, 0, x_322);
lean_ctor_set(x_329, 1, x_305);
if (lean_is_scalar(x_306)) {
 x_330 = lean_alloc_ctor(1, 1, 0);
} else {
 x_330 = x_306;
}
lean_ctor_set(x_330, 0, x_329);
if (lean_is_scalar(x_324)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_324;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_326);
return x_331;
}
else
{
uint8_t x_332; 
x_332 = lean_nat_dec_le(x_327, x_327);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_327);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_319)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_319;
}
lean_ctor_set(x_333, 0, x_322);
lean_ctor_set(x_333, 1, x_305);
if (lean_is_scalar(x_306)) {
 x_334 = lean_alloc_ctor(1, 1, 0);
} else {
 x_334 = x_306;
}
lean_ctor_set(x_334, 0, x_333);
if (lean_is_scalar(x_324)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_324;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_326);
return x_335;
}
else
{
size_t x_336; size_t x_337; lean_object* x_338; 
lean_dec(x_324);
x_336 = 0;
x_337 = lean_usize_of_nat(x_327);
lean_dec(x_327);
lean_inc(x_322);
x_338 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_322, x_1, x_336, x_337, x_8, x_9, x_10, x_11, x_326);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_unbox(x_339);
lean_dec(x_339);
if (x_340 == 0)
{
uint8_t x_341; 
lean_dec(x_3);
x_341 = !lean_is_exclusive(x_338);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_338, 0);
lean_dec(x_342);
if (lean_is_scalar(x_319)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_319;
}
lean_ctor_set(x_343, 0, x_322);
lean_ctor_set(x_343, 1, x_305);
if (lean_is_scalar(x_306)) {
 x_344 = lean_alloc_ctor(1, 1, 0);
} else {
 x_344 = x_306;
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_338, 0, x_344);
return x_338;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_345 = lean_ctor_get(x_338, 1);
lean_inc(x_345);
lean_dec(x_338);
if (lean_is_scalar(x_319)) {
 x_346 = lean_alloc_ctor(0, 2, 0);
} else {
 x_346 = x_319;
}
lean_ctor_set(x_346, 0, x_322);
lean_ctor_set(x_346, 1, x_305);
if (lean_is_scalar(x_306)) {
 x_347 = lean_alloc_ctor(1, 1, 0);
} else {
 x_347 = x_306;
}
lean_ctor_set(x_347, 0, x_346);
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_345);
return x_348;
}
}
else
{
uint8_t x_349; 
lean_dec(x_322);
lean_dec(x_319);
lean_dec(x_306);
lean_dec(x_305);
x_349 = !lean_is_exclusive(x_338);
if (x_349 == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_338, 0);
lean_dec(x_350);
lean_ctor_set(x_338, 0, x_3);
return x_338;
}
else
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_338, 1);
lean_inc(x_351);
lean_dec(x_338);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_3);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
else
{
uint8_t x_353; 
lean_dec(x_322);
lean_dec(x_319);
lean_dec(x_306);
lean_dec(x_305);
x_353 = !lean_is_exclusive(x_338);
if (x_353 == 0)
{
lean_object* x_354; 
x_354 = lean_ctor_get(x_338, 0);
lean_dec(x_354);
lean_ctor_set_tag(x_338, 0);
lean_ctor_set(x_338, 0, x_3);
return x_338;
}
else
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_338, 1);
lean_inc(x_355);
lean_dec(x_338);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_3);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
}
}
}
}
}
else
{
uint8_t x_438; 
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_438 = !lean_is_exclusive(x_315);
if (x_438 == 0)
{
return x_315;
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_439 = lean_ctor_get(x_315, 0);
x_440 = lean_ctor_get(x_315, 1);
lean_inc(x_440);
lean_inc(x_439);
lean_dec(x_315);
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
return x_441;
}
}
}
}
}
}
case 3:
{
lean_object* x_442; 
lean_dec(x_7);
lean_dec(x_6);
x_442 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_3);
lean_ctor_set(x_443, 1, x_12);
return x_443;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_444 = lean_ctor_get(x_442, 0);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_unsigned_to_nat(0u);
x_446 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_445);
if (lean_obj_tag(x_446) == 0)
{
lean_object* x_447; 
lean_dec(x_444);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_3);
lean_ctor_set(x_447, 1, x_12);
return x_447;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; 
x_448 = lean_ctor_get(x_446, 0);
lean_inc(x_448);
if (lean_is_exclusive(x_446)) {
 lean_ctor_release(x_446, 0);
 x_449 = x_446;
} else {
 lean_dec_ref(x_446);
 x_449 = lean_box(0);
}
x_450 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_444, x_8, x_9, x_10, x_11, x_12);
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_unbox(x_451);
lean_dec(x_451);
if (x_452 == 0)
{
uint8_t x_453; 
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_453 = !lean_is_exclusive(x_450);
if (x_453 == 0)
{
lean_object* x_454; 
x_454 = lean_ctor_get(x_450, 0);
lean_dec(x_454);
lean_ctor_set(x_450, 0, x_3);
return x_450;
}
else
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_450, 1);
lean_inc(x_455);
lean_dec(x_450);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_3);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; 
x_457 = lean_ctor_get(x_450, 1);
lean_inc(x_457);
lean_dec(x_450);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_458 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_448, x_8, x_9, x_10, x_11, x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_501; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_462 = x_459;
} else {
 lean_dec_ref(x_459);
 x_462 = lean_box(0);
}
x_463 = lean_box(0);
lean_inc(x_8);
x_464 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_461, x_463, x_8, x_9, x_10, x_11, x_460);
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_467 = x_464;
} else {
 lean_dec_ref(x_464);
 x_467 = lean_box(0);
}
x_468 = l_Lean_Expr_mvarId_x21(x_465);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_501 = l_Lean_Meta_ppGoal(x_468, x_8, x_9, x_10, x_11, x_466);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
x_559 = lean_st_ref_get(x_11, x_503);
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_560, 3);
lean_inc(x_561);
lean_dec(x_560);
x_562 = lean_ctor_get_uint8(x_561, sizeof(void*)*1);
lean_dec(x_561);
if (x_562 == 0)
{
lean_object* x_563; 
lean_dec(x_502);
x_563 = lean_ctor_get(x_559, 1);
lean_inc(x_563);
lean_dec(x_559);
x_504 = x_563;
goto block_558;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; 
x_564 = lean_ctor_get(x_559, 1);
lean_inc(x_564);
lean_dec(x_559);
x_565 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_566 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_565, x_8, x_9, x_10, x_11, x_564);
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
x_568 = lean_unbox(x_567);
lean_dec(x_567);
if (x_568 == 0)
{
lean_object* x_569; 
lean_dec(x_502);
x_569 = lean_ctor_get(x_566, 1);
lean_inc(x_569);
lean_dec(x_566);
x_504 = x_569;
goto block_558;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_570 = lean_ctor_get(x_566, 1);
lean_inc(x_570);
lean_dec(x_566);
x_571 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_571, 0, x_502);
x_572 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_573 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_573, 0, x_572);
lean_ctor_set(x_573, 1, x_571);
x_574 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_572);
x_575 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_565, x_574, x_8, x_9, x_10, x_11, x_570);
x_576 = lean_ctor_get(x_575, 1);
lean_inc(x_576);
lean_dec(x_575);
x_504 = x_576;
goto block_558;
}
}
block_558:
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_506 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_468, x_505, x_8, x_9, x_10, x_11, x_504);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; uint8_t x_508; 
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_unbox(x_507);
lean_dec(x_507);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; uint8_t x_513; 
lean_dec(x_467);
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_449);
lean_dec(x_448);
x_509 = lean_ctor_get(x_506, 1);
lean_inc(x_509);
lean_dec(x_506);
x_510 = lean_st_ref_get(x_11, x_509);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_511, 3);
lean_inc(x_512);
lean_dec(x_511);
x_513 = lean_ctor_get_uint8(x_512, sizeof(void*)*1);
lean_dec(x_512);
if (x_513 == 0)
{
uint8_t x_514; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_514 = !lean_is_exclusive(x_510);
if (x_514 == 0)
{
lean_object* x_515; 
x_515 = lean_ctor_get(x_510, 0);
lean_dec(x_515);
lean_ctor_set(x_510, 0, x_3);
return x_510;
}
else
{
lean_object* x_516; lean_object* x_517; 
x_516 = lean_ctor_get(x_510, 1);
lean_inc(x_516);
lean_dec(x_510);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_3);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; 
x_518 = lean_ctor_get(x_510, 1);
lean_inc(x_518);
lean_dec(x_510);
x_519 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_520 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_519, x_8, x_9, x_10, x_11, x_518);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_unbox(x_521);
lean_dec(x_521);
if (x_522 == 0)
{
uint8_t x_523; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_523 = !lean_is_exclusive(x_520);
if (x_523 == 0)
{
lean_object* x_524; 
x_524 = lean_ctor_get(x_520, 0);
lean_dec(x_524);
lean_ctor_set(x_520, 0, x_3);
return x_520;
}
else
{
lean_object* x_525; lean_object* x_526; 
x_525 = lean_ctor_get(x_520, 1);
lean_inc(x_525);
lean_dec(x_520);
x_526 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_526, 0, x_3);
lean_ctor_set(x_526, 1, x_525);
return x_526;
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; 
x_527 = lean_ctor_get(x_520, 1);
lean_inc(x_527);
lean_dec(x_520);
x_528 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_529 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_519, x_528, x_8, x_9, x_10, x_11, x_527);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_530 = !lean_is_exclusive(x_529);
if (x_530 == 0)
{
lean_object* x_531; 
x_531 = lean_ctor_get(x_529, 0);
lean_dec(x_531);
lean_ctor_set(x_529, 0, x_3);
return x_529;
}
else
{
lean_object* x_532; lean_object* x_533; 
x_532 = lean_ctor_get(x_529, 1);
lean_inc(x_532);
lean_dec(x_529);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_3);
lean_ctor_set(x_533, 1, x_532);
return x_533;
}
}
}
}
else
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_534 = lean_ctor_get(x_506, 1);
lean_inc(x_534);
lean_dec(x_506);
x_535 = lean_st_ref_get(x_11, x_534);
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_536, 3);
lean_inc(x_537);
lean_dec(x_536);
x_538 = lean_ctor_get_uint8(x_537, sizeof(void*)*1);
lean_dec(x_537);
if (x_538 == 0)
{
lean_object* x_539; 
x_539 = lean_ctor_get(x_535, 1);
lean_inc(x_539);
lean_dec(x_535);
x_469 = x_539;
goto block_500;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; 
x_540 = lean_ctor_get(x_535, 1);
lean_inc(x_540);
lean_dec(x_535);
x_541 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_542 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_541, x_8, x_9, x_10, x_11, x_540);
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_unbox(x_543);
lean_dec(x_543);
if (x_544 == 0)
{
lean_object* x_545; 
x_545 = lean_ctor_get(x_542, 1);
lean_inc(x_545);
lean_dec(x_542);
x_469 = x_545;
goto block_500;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_546 = lean_ctor_get(x_542, 1);
lean_inc(x_546);
lean_dec(x_542);
lean_inc(x_465);
x_547 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_547, 0, x_465);
x_548 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_549 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_547);
x_550 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_551 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
x_552 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_541, x_551, x_8, x_9, x_10, x_11, x_546);
x_553 = lean_ctor_get(x_552, 1);
lean_inc(x_553);
lean_dec(x_552);
x_469 = x_553;
goto block_500;
}
}
}
}
else
{
uint8_t x_554; 
lean_dec(x_467);
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_554 = !lean_is_exclusive(x_506);
if (x_554 == 0)
{
lean_object* x_555; 
x_555 = lean_ctor_get(x_506, 0);
lean_dec(x_555);
lean_ctor_set_tag(x_506, 0);
lean_ctor_set(x_506, 0, x_3);
return x_506;
}
else
{
lean_object* x_556; lean_object* x_557; 
x_556 = lean_ctor_get(x_506, 1);
lean_inc(x_556);
lean_dec(x_506);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_3);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
}
}
}
else
{
uint8_t x_577; 
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_577 = !lean_is_exclusive(x_501);
if (x_577 == 0)
{
lean_object* x_578; 
x_578 = lean_ctor_get(x_501, 0);
lean_dec(x_578);
lean_ctor_set_tag(x_501, 0);
lean_ctor_set(x_501, 0, x_3);
return x_501;
}
else
{
lean_object* x_579; lean_object* x_580; 
x_579 = lean_ctor_get(x_501, 1);
lean_inc(x_579);
lean_dec(x_501);
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_3);
lean_ctor_set(x_580, 1, x_579);
return x_580;
}
}
block_500:
{
lean_object* x_470; uint8_t x_471; 
x_470 = lean_array_get_size(x_1);
x_471 = lean_nat_dec_lt(x_445, x_470);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_470);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_462)) {
 x_472 = lean_alloc_ctor(0, 2, 0);
} else {
 x_472 = x_462;
}
lean_ctor_set(x_472, 0, x_465);
lean_ctor_set(x_472, 1, x_448);
if (lean_is_scalar(x_449)) {
 x_473 = lean_alloc_ctor(1, 1, 0);
} else {
 x_473 = x_449;
}
lean_ctor_set(x_473, 0, x_472);
if (lean_is_scalar(x_467)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_467;
}
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_469);
return x_474;
}
else
{
uint8_t x_475; 
x_475 = lean_nat_dec_le(x_470, x_470);
if (x_475 == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_470);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_462)) {
 x_476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_476 = x_462;
}
lean_ctor_set(x_476, 0, x_465);
lean_ctor_set(x_476, 1, x_448);
if (lean_is_scalar(x_449)) {
 x_477 = lean_alloc_ctor(1, 1, 0);
} else {
 x_477 = x_449;
}
lean_ctor_set(x_477, 0, x_476);
if (lean_is_scalar(x_467)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_467;
}
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_469);
return x_478;
}
else
{
size_t x_479; size_t x_480; lean_object* x_481; 
lean_dec(x_467);
x_479 = 0;
x_480 = lean_usize_of_nat(x_470);
lean_dec(x_470);
lean_inc(x_465);
x_481 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_465, x_1, x_479, x_480, x_8, x_9, x_10, x_11, x_469);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; uint8_t x_483; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_unbox(x_482);
lean_dec(x_482);
if (x_483 == 0)
{
uint8_t x_484; 
lean_dec(x_3);
x_484 = !lean_is_exclusive(x_481);
if (x_484 == 0)
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_481, 0);
lean_dec(x_485);
if (lean_is_scalar(x_462)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_462;
}
lean_ctor_set(x_486, 0, x_465);
lean_ctor_set(x_486, 1, x_448);
if (lean_is_scalar(x_449)) {
 x_487 = lean_alloc_ctor(1, 1, 0);
} else {
 x_487 = x_449;
}
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_481, 0, x_487);
return x_481;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_488 = lean_ctor_get(x_481, 1);
lean_inc(x_488);
lean_dec(x_481);
if (lean_is_scalar(x_462)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_462;
}
lean_ctor_set(x_489, 0, x_465);
lean_ctor_set(x_489, 1, x_448);
if (lean_is_scalar(x_449)) {
 x_490 = lean_alloc_ctor(1, 1, 0);
} else {
 x_490 = x_449;
}
lean_ctor_set(x_490, 0, x_489);
x_491 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_488);
return x_491;
}
}
else
{
uint8_t x_492; 
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_449);
lean_dec(x_448);
x_492 = !lean_is_exclusive(x_481);
if (x_492 == 0)
{
lean_object* x_493; 
x_493 = lean_ctor_get(x_481, 0);
lean_dec(x_493);
lean_ctor_set(x_481, 0, x_3);
return x_481;
}
else
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_ctor_get(x_481, 1);
lean_inc(x_494);
lean_dec(x_481);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_3);
lean_ctor_set(x_495, 1, x_494);
return x_495;
}
}
}
else
{
uint8_t x_496; 
lean_dec(x_465);
lean_dec(x_462);
lean_dec(x_449);
lean_dec(x_448);
x_496 = !lean_is_exclusive(x_481);
if (x_496 == 0)
{
lean_object* x_497; 
x_497 = lean_ctor_get(x_481, 0);
lean_dec(x_497);
lean_ctor_set_tag(x_481, 0);
lean_ctor_set(x_481, 0, x_3);
return x_481;
}
else
{
lean_object* x_498; lean_object* x_499; 
x_498 = lean_ctor_get(x_481, 1);
lean_inc(x_498);
lean_dec(x_481);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_3);
lean_ctor_set(x_499, 1, x_498);
return x_499;
}
}
}
}
}
}
else
{
uint8_t x_581; 
lean_dec(x_449);
lean_dec(x_448);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_581 = !lean_is_exclusive(x_458);
if (x_581 == 0)
{
return x_458;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_458, 0);
x_583 = lean_ctor_get(x_458, 1);
lean_inc(x_583);
lean_inc(x_582);
lean_dec(x_458);
x_584 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set(x_584, 1, x_583);
return x_584;
}
}
}
}
}
}
case 4:
{
lean_object* x_585; 
lean_dec(x_7);
lean_dec(x_6);
x_585 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_586 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_586, 0, x_3);
lean_ctor_set(x_586, 1, x_12);
return x_586;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_585, 0);
lean_inc(x_587);
lean_dec(x_585);
x_588 = lean_unsigned_to_nat(0u);
x_589 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_588);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; 
lean_dec(x_587);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_3);
lean_ctor_set(x_590, 1, x_12);
return x_590;
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; uint8_t x_595; 
x_591 = lean_ctor_get(x_589, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 x_592 = x_589;
} else {
 lean_dec_ref(x_589);
 x_592 = lean_box(0);
}
x_593 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_587, x_8, x_9, x_10, x_11, x_12);
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_unbox(x_594);
lean_dec(x_594);
if (x_595 == 0)
{
uint8_t x_596; 
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_596 = !lean_is_exclusive(x_593);
if (x_596 == 0)
{
lean_object* x_597; 
x_597 = lean_ctor_get(x_593, 0);
lean_dec(x_597);
lean_ctor_set(x_593, 0, x_3);
return x_593;
}
else
{
lean_object* x_598; lean_object* x_599; 
x_598 = lean_ctor_get(x_593, 1);
lean_inc(x_598);
lean_dec(x_593);
x_599 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_599, 0, x_3);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
else
{
lean_object* x_600; lean_object* x_601; 
x_600 = lean_ctor_get(x_593, 1);
lean_inc(x_600);
lean_dec(x_593);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_601 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_591, x_8, x_9, x_10, x_11, x_600);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_644; 
x_602 = lean_ctor_get(x_601, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_601, 1);
lean_inc(x_603);
lean_dec(x_601);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_605 = x_602;
} else {
 lean_dec_ref(x_602);
 x_605 = lean_box(0);
}
x_606 = lean_box(0);
lean_inc(x_8);
x_607 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_604, x_606, x_8, x_9, x_10, x_11, x_603);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_607, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_610 = x_607;
} else {
 lean_dec_ref(x_607);
 x_610 = lean_box(0);
}
x_611 = l_Lean_Expr_mvarId_x21(x_608);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_644 = l_Lean_Meta_ppGoal(x_611, x_8, x_9, x_10, x_11, x_609);
if (lean_obj_tag(x_644) == 0)
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_702; lean_object* x_703; lean_object* x_704; uint8_t x_705; 
x_645 = lean_ctor_get(x_644, 0);
lean_inc(x_645);
x_646 = lean_ctor_get(x_644, 1);
lean_inc(x_646);
lean_dec(x_644);
x_702 = lean_st_ref_get(x_11, x_646);
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_703, 3);
lean_inc(x_704);
lean_dec(x_703);
x_705 = lean_ctor_get_uint8(x_704, sizeof(void*)*1);
lean_dec(x_704);
if (x_705 == 0)
{
lean_object* x_706; 
lean_dec(x_645);
x_706 = lean_ctor_get(x_702, 1);
lean_inc(x_706);
lean_dec(x_702);
x_647 = x_706;
goto block_701;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; uint8_t x_711; 
x_707 = lean_ctor_get(x_702, 1);
lean_inc(x_707);
lean_dec(x_702);
x_708 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_709 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_708, x_8, x_9, x_10, x_11, x_707);
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_unbox(x_710);
lean_dec(x_710);
if (x_711 == 0)
{
lean_object* x_712; 
lean_dec(x_645);
x_712 = lean_ctor_get(x_709, 1);
lean_inc(x_712);
lean_dec(x_709);
x_647 = x_712;
goto block_701;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_713 = lean_ctor_get(x_709, 1);
lean_inc(x_713);
lean_dec(x_709);
x_714 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_714, 0, x_645);
x_715 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_716 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_714);
x_717 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_715);
x_718 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_708, x_717, x_8, x_9, x_10, x_11, x_713);
x_719 = lean_ctor_get(x_718, 1);
lean_inc(x_719);
lean_dec(x_718);
x_647 = x_719;
goto block_701;
}
}
block_701:
{
lean_object* x_648; lean_object* x_649; 
x_648 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_649 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_611, x_648, x_8, x_9, x_10, x_11, x_647);
if (lean_obj_tag(x_649) == 0)
{
lean_object* x_650; uint8_t x_651; 
x_650 = lean_ctor_get(x_649, 0);
lean_inc(x_650);
x_651 = lean_unbox(x_650);
lean_dec(x_650);
if (x_651 == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; 
lean_dec(x_610);
lean_dec(x_608);
lean_dec(x_605);
lean_dec(x_592);
lean_dec(x_591);
x_652 = lean_ctor_get(x_649, 1);
lean_inc(x_652);
lean_dec(x_649);
x_653 = lean_st_ref_get(x_11, x_652);
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_654, 3);
lean_inc(x_655);
lean_dec(x_654);
x_656 = lean_ctor_get_uint8(x_655, sizeof(void*)*1);
lean_dec(x_655);
if (x_656 == 0)
{
uint8_t x_657; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_657 = !lean_is_exclusive(x_653);
if (x_657 == 0)
{
lean_object* x_658; 
x_658 = lean_ctor_get(x_653, 0);
lean_dec(x_658);
lean_ctor_set(x_653, 0, x_3);
return x_653;
}
else
{
lean_object* x_659; lean_object* x_660; 
x_659 = lean_ctor_get(x_653, 1);
lean_inc(x_659);
lean_dec(x_653);
x_660 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_660, 0, x_3);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; 
x_661 = lean_ctor_get(x_653, 1);
lean_inc(x_661);
lean_dec(x_653);
x_662 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_663 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_662, x_8, x_9, x_10, x_11, x_661);
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_unbox(x_664);
lean_dec(x_664);
if (x_665 == 0)
{
uint8_t x_666; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_666 = !lean_is_exclusive(x_663);
if (x_666 == 0)
{
lean_object* x_667; 
x_667 = lean_ctor_get(x_663, 0);
lean_dec(x_667);
lean_ctor_set(x_663, 0, x_3);
return x_663;
}
else
{
lean_object* x_668; lean_object* x_669; 
x_668 = lean_ctor_get(x_663, 1);
lean_inc(x_668);
lean_dec(x_663);
x_669 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_669, 0, x_3);
lean_ctor_set(x_669, 1, x_668);
return x_669;
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; uint8_t x_673; 
x_670 = lean_ctor_get(x_663, 1);
lean_inc(x_670);
lean_dec(x_663);
x_671 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_672 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_662, x_671, x_8, x_9, x_10, x_11, x_670);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_673 = !lean_is_exclusive(x_672);
if (x_673 == 0)
{
lean_object* x_674; 
x_674 = lean_ctor_get(x_672, 0);
lean_dec(x_674);
lean_ctor_set(x_672, 0, x_3);
return x_672;
}
else
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_672, 1);
lean_inc(x_675);
lean_dec(x_672);
x_676 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_676, 0, x_3);
lean_ctor_set(x_676, 1, x_675);
return x_676;
}
}
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; uint8_t x_681; 
x_677 = lean_ctor_get(x_649, 1);
lean_inc(x_677);
lean_dec(x_649);
x_678 = lean_st_ref_get(x_11, x_677);
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_679, 3);
lean_inc(x_680);
lean_dec(x_679);
x_681 = lean_ctor_get_uint8(x_680, sizeof(void*)*1);
lean_dec(x_680);
if (x_681 == 0)
{
lean_object* x_682; 
x_682 = lean_ctor_get(x_678, 1);
lean_inc(x_682);
lean_dec(x_678);
x_612 = x_682;
goto block_643;
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; uint8_t x_687; 
x_683 = lean_ctor_get(x_678, 1);
lean_inc(x_683);
lean_dec(x_678);
x_684 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_685 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_684, x_8, x_9, x_10, x_11, x_683);
x_686 = lean_ctor_get(x_685, 0);
lean_inc(x_686);
x_687 = lean_unbox(x_686);
lean_dec(x_686);
if (x_687 == 0)
{
lean_object* x_688; 
x_688 = lean_ctor_get(x_685, 1);
lean_inc(x_688);
lean_dec(x_685);
x_612 = x_688;
goto block_643;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_689 = lean_ctor_get(x_685, 1);
lean_inc(x_689);
lean_dec(x_685);
lean_inc(x_608);
x_690 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_690, 0, x_608);
x_691 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_692 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_692, 0, x_691);
lean_ctor_set(x_692, 1, x_690);
x_693 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_694 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_694, 0, x_692);
lean_ctor_set(x_694, 1, x_693);
x_695 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_684, x_694, x_8, x_9, x_10, x_11, x_689);
x_696 = lean_ctor_get(x_695, 1);
lean_inc(x_696);
lean_dec(x_695);
x_612 = x_696;
goto block_643;
}
}
}
}
else
{
uint8_t x_697; 
lean_dec(x_610);
lean_dec(x_608);
lean_dec(x_605);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_697 = !lean_is_exclusive(x_649);
if (x_697 == 0)
{
lean_object* x_698; 
x_698 = lean_ctor_get(x_649, 0);
lean_dec(x_698);
lean_ctor_set_tag(x_649, 0);
lean_ctor_set(x_649, 0, x_3);
return x_649;
}
else
{
lean_object* x_699; lean_object* x_700; 
x_699 = lean_ctor_get(x_649, 1);
lean_inc(x_699);
lean_dec(x_649);
x_700 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_700, 0, x_3);
lean_ctor_set(x_700, 1, x_699);
return x_700;
}
}
}
}
else
{
uint8_t x_720; 
lean_dec(x_611);
lean_dec(x_610);
lean_dec(x_608);
lean_dec(x_605);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_720 = !lean_is_exclusive(x_644);
if (x_720 == 0)
{
lean_object* x_721; 
x_721 = lean_ctor_get(x_644, 0);
lean_dec(x_721);
lean_ctor_set_tag(x_644, 0);
lean_ctor_set(x_644, 0, x_3);
return x_644;
}
else
{
lean_object* x_722; lean_object* x_723; 
x_722 = lean_ctor_get(x_644, 1);
lean_inc(x_722);
lean_dec(x_644);
x_723 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_723, 0, x_3);
lean_ctor_set(x_723, 1, x_722);
return x_723;
}
}
block_643:
{
lean_object* x_613; uint8_t x_614; 
x_613 = lean_array_get_size(x_1);
x_614 = lean_nat_dec_lt(x_588, x_613);
if (x_614 == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_613);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_605)) {
 x_615 = lean_alloc_ctor(0, 2, 0);
} else {
 x_615 = x_605;
}
lean_ctor_set(x_615, 0, x_608);
lean_ctor_set(x_615, 1, x_591);
if (lean_is_scalar(x_592)) {
 x_616 = lean_alloc_ctor(1, 1, 0);
} else {
 x_616 = x_592;
}
lean_ctor_set(x_616, 0, x_615);
if (lean_is_scalar(x_610)) {
 x_617 = lean_alloc_ctor(0, 2, 0);
} else {
 x_617 = x_610;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_612);
return x_617;
}
else
{
uint8_t x_618; 
x_618 = lean_nat_dec_le(x_613, x_613);
if (x_618 == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_613);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_605)) {
 x_619 = lean_alloc_ctor(0, 2, 0);
} else {
 x_619 = x_605;
}
lean_ctor_set(x_619, 0, x_608);
lean_ctor_set(x_619, 1, x_591);
if (lean_is_scalar(x_592)) {
 x_620 = lean_alloc_ctor(1, 1, 0);
} else {
 x_620 = x_592;
}
lean_ctor_set(x_620, 0, x_619);
if (lean_is_scalar(x_610)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_610;
}
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_612);
return x_621;
}
else
{
size_t x_622; size_t x_623; lean_object* x_624; 
lean_dec(x_610);
x_622 = 0;
x_623 = lean_usize_of_nat(x_613);
lean_dec(x_613);
lean_inc(x_608);
x_624 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_608, x_1, x_622, x_623, x_8, x_9, x_10, x_11, x_612);
if (lean_obj_tag(x_624) == 0)
{
lean_object* x_625; uint8_t x_626; 
x_625 = lean_ctor_get(x_624, 0);
lean_inc(x_625);
x_626 = lean_unbox(x_625);
lean_dec(x_625);
if (x_626 == 0)
{
uint8_t x_627; 
lean_dec(x_3);
x_627 = !lean_is_exclusive(x_624);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_624, 0);
lean_dec(x_628);
if (lean_is_scalar(x_605)) {
 x_629 = lean_alloc_ctor(0, 2, 0);
} else {
 x_629 = x_605;
}
lean_ctor_set(x_629, 0, x_608);
lean_ctor_set(x_629, 1, x_591);
if (lean_is_scalar(x_592)) {
 x_630 = lean_alloc_ctor(1, 1, 0);
} else {
 x_630 = x_592;
}
lean_ctor_set(x_630, 0, x_629);
lean_ctor_set(x_624, 0, x_630);
return x_624;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_631 = lean_ctor_get(x_624, 1);
lean_inc(x_631);
lean_dec(x_624);
if (lean_is_scalar(x_605)) {
 x_632 = lean_alloc_ctor(0, 2, 0);
} else {
 x_632 = x_605;
}
lean_ctor_set(x_632, 0, x_608);
lean_ctor_set(x_632, 1, x_591);
if (lean_is_scalar(x_592)) {
 x_633 = lean_alloc_ctor(1, 1, 0);
} else {
 x_633 = x_592;
}
lean_ctor_set(x_633, 0, x_632);
x_634 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_631);
return x_634;
}
}
else
{
uint8_t x_635; 
lean_dec(x_608);
lean_dec(x_605);
lean_dec(x_592);
lean_dec(x_591);
x_635 = !lean_is_exclusive(x_624);
if (x_635 == 0)
{
lean_object* x_636; 
x_636 = lean_ctor_get(x_624, 0);
lean_dec(x_636);
lean_ctor_set(x_624, 0, x_3);
return x_624;
}
else
{
lean_object* x_637; lean_object* x_638; 
x_637 = lean_ctor_get(x_624, 1);
lean_inc(x_637);
lean_dec(x_624);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_3);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
}
else
{
uint8_t x_639; 
lean_dec(x_608);
lean_dec(x_605);
lean_dec(x_592);
lean_dec(x_591);
x_639 = !lean_is_exclusive(x_624);
if (x_639 == 0)
{
lean_object* x_640; 
x_640 = lean_ctor_get(x_624, 0);
lean_dec(x_640);
lean_ctor_set_tag(x_624, 0);
lean_ctor_set(x_624, 0, x_3);
return x_624;
}
else
{
lean_object* x_641; lean_object* x_642; 
x_641 = lean_ctor_get(x_624, 1);
lean_inc(x_641);
lean_dec(x_624);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_3);
lean_ctor_set(x_642, 1, x_641);
return x_642;
}
}
}
}
}
}
else
{
uint8_t x_724; 
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_724 = !lean_is_exclusive(x_601);
if (x_724 == 0)
{
return x_601;
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_601, 0);
x_726 = lean_ctor_get(x_601, 1);
lean_inc(x_726);
lean_inc(x_725);
lean_dec(x_601);
x_727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_727, 0, x_725);
lean_ctor_set(x_727, 1, x_726);
return x_727;
}
}
}
}
}
}
case 5:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
x_728 = lean_ctor_get(x_5, 0);
lean_inc(x_728);
x_729 = lean_ctor_get(x_5, 1);
lean_inc(x_729);
lean_dec(x_5);
x_730 = lean_array_set(x_6, x_7, x_729);
x_731 = lean_unsigned_to_nat(1u);
x_732 = lean_nat_sub(x_7, x_731);
lean_dec(x_7);
x_5 = x_728;
x_6 = x_730;
x_7 = x_732;
goto _start;
}
case 6:
{
lean_object* x_734; 
lean_dec(x_7);
lean_dec(x_6);
x_734 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_735 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_735, 0, x_3);
lean_ctor_set(x_735, 1, x_12);
return x_735;
}
else
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_736 = lean_ctor_get(x_734, 0);
lean_inc(x_736);
lean_dec(x_734);
x_737 = lean_unsigned_to_nat(0u);
x_738 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_737);
if (lean_obj_tag(x_738) == 0)
{
lean_object* x_739; 
lean_dec(x_736);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_739 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_739, 0, x_3);
lean_ctor_set(x_739, 1, x_12);
return x_739;
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; uint8_t x_744; 
x_740 = lean_ctor_get(x_738, 0);
lean_inc(x_740);
if (lean_is_exclusive(x_738)) {
 lean_ctor_release(x_738, 0);
 x_741 = x_738;
} else {
 lean_dec_ref(x_738);
 x_741 = lean_box(0);
}
x_742 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_736, x_8, x_9, x_10, x_11, x_12);
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_unbox(x_743);
lean_dec(x_743);
if (x_744 == 0)
{
uint8_t x_745; 
lean_dec(x_741);
lean_dec(x_740);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_745 = !lean_is_exclusive(x_742);
if (x_745 == 0)
{
lean_object* x_746; 
x_746 = lean_ctor_get(x_742, 0);
lean_dec(x_746);
lean_ctor_set(x_742, 0, x_3);
return x_742;
}
else
{
lean_object* x_747; lean_object* x_748; 
x_747 = lean_ctor_get(x_742, 1);
lean_inc(x_747);
lean_dec(x_742);
x_748 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_748, 0, x_3);
lean_ctor_set(x_748, 1, x_747);
return x_748;
}
}
else
{
lean_object* x_749; lean_object* x_750; 
x_749 = lean_ctor_get(x_742, 1);
lean_inc(x_749);
lean_dec(x_742);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_750 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_740, x_8, x_9, x_10, x_11, x_749);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_793; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
if (lean_is_exclusive(x_751)) {
 lean_ctor_release(x_751, 0);
 lean_ctor_release(x_751, 1);
 x_754 = x_751;
} else {
 lean_dec_ref(x_751);
 x_754 = lean_box(0);
}
x_755 = lean_box(0);
lean_inc(x_8);
x_756 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_753, x_755, x_8, x_9, x_10, x_11, x_752);
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_756, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 lean_ctor_release(x_756, 1);
 x_759 = x_756;
} else {
 lean_dec_ref(x_756);
 x_759 = lean_box(0);
}
x_760 = l_Lean_Expr_mvarId_x21(x_757);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_793 = l_Lean_Meta_ppGoal(x_760, x_8, x_9, x_10, x_11, x_758);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_851; lean_object* x_852; lean_object* x_853; uint8_t x_854; 
x_794 = lean_ctor_get(x_793, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_793, 1);
lean_inc(x_795);
lean_dec(x_793);
x_851 = lean_st_ref_get(x_11, x_795);
x_852 = lean_ctor_get(x_851, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_852, 3);
lean_inc(x_853);
lean_dec(x_852);
x_854 = lean_ctor_get_uint8(x_853, sizeof(void*)*1);
lean_dec(x_853);
if (x_854 == 0)
{
lean_object* x_855; 
lean_dec(x_794);
x_855 = lean_ctor_get(x_851, 1);
lean_inc(x_855);
lean_dec(x_851);
x_796 = x_855;
goto block_850;
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; uint8_t x_860; 
x_856 = lean_ctor_get(x_851, 1);
lean_inc(x_856);
lean_dec(x_851);
x_857 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_858 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_857, x_8, x_9, x_10, x_11, x_856);
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_unbox(x_859);
lean_dec(x_859);
if (x_860 == 0)
{
lean_object* x_861; 
lean_dec(x_794);
x_861 = lean_ctor_get(x_858, 1);
lean_inc(x_861);
lean_dec(x_858);
x_796 = x_861;
goto block_850;
}
else
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_862 = lean_ctor_get(x_858, 1);
lean_inc(x_862);
lean_dec(x_858);
x_863 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_863, 0, x_794);
x_864 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_865 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_863);
x_866 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_864);
x_867 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_857, x_866, x_8, x_9, x_10, x_11, x_862);
x_868 = lean_ctor_get(x_867, 1);
lean_inc(x_868);
lean_dec(x_867);
x_796 = x_868;
goto block_850;
}
}
block_850:
{
lean_object* x_797; lean_object* x_798; 
x_797 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_798 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_760, x_797, x_8, x_9, x_10, x_11, x_796);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; uint8_t x_800; 
x_799 = lean_ctor_get(x_798, 0);
lean_inc(x_799);
x_800 = lean_unbox(x_799);
lean_dec(x_799);
if (x_800 == 0)
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; uint8_t x_805; 
lean_dec(x_759);
lean_dec(x_757);
lean_dec(x_754);
lean_dec(x_741);
lean_dec(x_740);
x_801 = lean_ctor_get(x_798, 1);
lean_inc(x_801);
lean_dec(x_798);
x_802 = lean_st_ref_get(x_11, x_801);
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_803, 3);
lean_inc(x_804);
lean_dec(x_803);
x_805 = lean_ctor_get_uint8(x_804, sizeof(void*)*1);
lean_dec(x_804);
if (x_805 == 0)
{
uint8_t x_806; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_806 = !lean_is_exclusive(x_802);
if (x_806 == 0)
{
lean_object* x_807; 
x_807 = lean_ctor_get(x_802, 0);
lean_dec(x_807);
lean_ctor_set(x_802, 0, x_3);
return x_802;
}
else
{
lean_object* x_808; lean_object* x_809; 
x_808 = lean_ctor_get(x_802, 1);
lean_inc(x_808);
lean_dec(x_802);
x_809 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_809, 0, x_3);
lean_ctor_set(x_809, 1, x_808);
return x_809;
}
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; uint8_t x_814; 
x_810 = lean_ctor_get(x_802, 1);
lean_inc(x_810);
lean_dec(x_802);
x_811 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_812 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_811, x_8, x_9, x_10, x_11, x_810);
x_813 = lean_ctor_get(x_812, 0);
lean_inc(x_813);
x_814 = lean_unbox(x_813);
lean_dec(x_813);
if (x_814 == 0)
{
uint8_t x_815; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_815 = !lean_is_exclusive(x_812);
if (x_815 == 0)
{
lean_object* x_816; 
x_816 = lean_ctor_get(x_812, 0);
lean_dec(x_816);
lean_ctor_set(x_812, 0, x_3);
return x_812;
}
else
{
lean_object* x_817; lean_object* x_818; 
x_817 = lean_ctor_get(x_812, 1);
lean_inc(x_817);
lean_dec(x_812);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_3);
lean_ctor_set(x_818, 1, x_817);
return x_818;
}
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; uint8_t x_822; 
x_819 = lean_ctor_get(x_812, 1);
lean_inc(x_819);
lean_dec(x_812);
x_820 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_821 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_811, x_820, x_8, x_9, x_10, x_11, x_819);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_822 = !lean_is_exclusive(x_821);
if (x_822 == 0)
{
lean_object* x_823; 
x_823 = lean_ctor_get(x_821, 0);
lean_dec(x_823);
lean_ctor_set(x_821, 0, x_3);
return x_821;
}
else
{
lean_object* x_824; lean_object* x_825; 
x_824 = lean_ctor_get(x_821, 1);
lean_inc(x_824);
lean_dec(x_821);
x_825 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_825, 0, x_3);
lean_ctor_set(x_825, 1, x_824);
return x_825;
}
}
}
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; uint8_t x_830; 
x_826 = lean_ctor_get(x_798, 1);
lean_inc(x_826);
lean_dec(x_798);
x_827 = lean_st_ref_get(x_11, x_826);
x_828 = lean_ctor_get(x_827, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_828, 3);
lean_inc(x_829);
lean_dec(x_828);
x_830 = lean_ctor_get_uint8(x_829, sizeof(void*)*1);
lean_dec(x_829);
if (x_830 == 0)
{
lean_object* x_831; 
x_831 = lean_ctor_get(x_827, 1);
lean_inc(x_831);
lean_dec(x_827);
x_761 = x_831;
goto block_792;
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; uint8_t x_836; 
x_832 = lean_ctor_get(x_827, 1);
lean_inc(x_832);
lean_dec(x_827);
x_833 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_834 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_833, x_8, x_9, x_10, x_11, x_832);
x_835 = lean_ctor_get(x_834, 0);
lean_inc(x_835);
x_836 = lean_unbox(x_835);
lean_dec(x_835);
if (x_836 == 0)
{
lean_object* x_837; 
x_837 = lean_ctor_get(x_834, 1);
lean_inc(x_837);
lean_dec(x_834);
x_761 = x_837;
goto block_792;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; 
x_838 = lean_ctor_get(x_834, 1);
lean_inc(x_838);
lean_dec(x_834);
lean_inc(x_757);
x_839 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_839, 0, x_757);
x_840 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_841 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_841, 0, x_840);
lean_ctor_set(x_841, 1, x_839);
x_842 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_843 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_843, 0, x_841);
lean_ctor_set(x_843, 1, x_842);
x_844 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_833, x_843, x_8, x_9, x_10, x_11, x_838);
x_845 = lean_ctor_get(x_844, 1);
lean_inc(x_845);
lean_dec(x_844);
x_761 = x_845;
goto block_792;
}
}
}
}
else
{
uint8_t x_846; 
lean_dec(x_759);
lean_dec(x_757);
lean_dec(x_754);
lean_dec(x_741);
lean_dec(x_740);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_846 = !lean_is_exclusive(x_798);
if (x_846 == 0)
{
lean_object* x_847; 
x_847 = lean_ctor_get(x_798, 0);
lean_dec(x_847);
lean_ctor_set_tag(x_798, 0);
lean_ctor_set(x_798, 0, x_3);
return x_798;
}
else
{
lean_object* x_848; lean_object* x_849; 
x_848 = lean_ctor_get(x_798, 1);
lean_inc(x_848);
lean_dec(x_798);
x_849 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_849, 0, x_3);
lean_ctor_set(x_849, 1, x_848);
return x_849;
}
}
}
}
else
{
uint8_t x_869; 
lean_dec(x_760);
lean_dec(x_759);
lean_dec(x_757);
lean_dec(x_754);
lean_dec(x_741);
lean_dec(x_740);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_869 = !lean_is_exclusive(x_793);
if (x_869 == 0)
{
lean_object* x_870; 
x_870 = lean_ctor_get(x_793, 0);
lean_dec(x_870);
lean_ctor_set_tag(x_793, 0);
lean_ctor_set(x_793, 0, x_3);
return x_793;
}
else
{
lean_object* x_871; lean_object* x_872; 
x_871 = lean_ctor_get(x_793, 1);
lean_inc(x_871);
lean_dec(x_793);
x_872 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_872, 0, x_3);
lean_ctor_set(x_872, 1, x_871);
return x_872;
}
}
block_792:
{
lean_object* x_762; uint8_t x_763; 
x_762 = lean_array_get_size(x_1);
x_763 = lean_nat_dec_lt(x_737, x_762);
if (x_763 == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
lean_dec(x_762);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_754)) {
 x_764 = lean_alloc_ctor(0, 2, 0);
} else {
 x_764 = x_754;
}
lean_ctor_set(x_764, 0, x_757);
lean_ctor_set(x_764, 1, x_740);
if (lean_is_scalar(x_741)) {
 x_765 = lean_alloc_ctor(1, 1, 0);
} else {
 x_765 = x_741;
}
lean_ctor_set(x_765, 0, x_764);
if (lean_is_scalar(x_759)) {
 x_766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_766 = x_759;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_761);
return x_766;
}
else
{
uint8_t x_767; 
x_767 = lean_nat_dec_le(x_762, x_762);
if (x_767 == 0)
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; 
lean_dec(x_762);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_754)) {
 x_768 = lean_alloc_ctor(0, 2, 0);
} else {
 x_768 = x_754;
}
lean_ctor_set(x_768, 0, x_757);
lean_ctor_set(x_768, 1, x_740);
if (lean_is_scalar(x_741)) {
 x_769 = lean_alloc_ctor(1, 1, 0);
} else {
 x_769 = x_741;
}
lean_ctor_set(x_769, 0, x_768);
if (lean_is_scalar(x_759)) {
 x_770 = lean_alloc_ctor(0, 2, 0);
} else {
 x_770 = x_759;
}
lean_ctor_set(x_770, 0, x_769);
lean_ctor_set(x_770, 1, x_761);
return x_770;
}
else
{
size_t x_771; size_t x_772; lean_object* x_773; 
lean_dec(x_759);
x_771 = 0;
x_772 = lean_usize_of_nat(x_762);
lean_dec(x_762);
lean_inc(x_757);
x_773 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_757, x_1, x_771, x_772, x_8, x_9, x_10, x_11, x_761);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; uint8_t x_775; 
x_774 = lean_ctor_get(x_773, 0);
lean_inc(x_774);
x_775 = lean_unbox(x_774);
lean_dec(x_774);
if (x_775 == 0)
{
uint8_t x_776; 
lean_dec(x_3);
x_776 = !lean_is_exclusive(x_773);
if (x_776 == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_777 = lean_ctor_get(x_773, 0);
lean_dec(x_777);
if (lean_is_scalar(x_754)) {
 x_778 = lean_alloc_ctor(0, 2, 0);
} else {
 x_778 = x_754;
}
lean_ctor_set(x_778, 0, x_757);
lean_ctor_set(x_778, 1, x_740);
if (lean_is_scalar(x_741)) {
 x_779 = lean_alloc_ctor(1, 1, 0);
} else {
 x_779 = x_741;
}
lean_ctor_set(x_779, 0, x_778);
lean_ctor_set(x_773, 0, x_779);
return x_773;
}
else
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_780 = lean_ctor_get(x_773, 1);
lean_inc(x_780);
lean_dec(x_773);
if (lean_is_scalar(x_754)) {
 x_781 = lean_alloc_ctor(0, 2, 0);
} else {
 x_781 = x_754;
}
lean_ctor_set(x_781, 0, x_757);
lean_ctor_set(x_781, 1, x_740);
if (lean_is_scalar(x_741)) {
 x_782 = lean_alloc_ctor(1, 1, 0);
} else {
 x_782 = x_741;
}
lean_ctor_set(x_782, 0, x_781);
x_783 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_780);
return x_783;
}
}
else
{
uint8_t x_784; 
lean_dec(x_757);
lean_dec(x_754);
lean_dec(x_741);
lean_dec(x_740);
x_784 = !lean_is_exclusive(x_773);
if (x_784 == 0)
{
lean_object* x_785; 
x_785 = lean_ctor_get(x_773, 0);
lean_dec(x_785);
lean_ctor_set(x_773, 0, x_3);
return x_773;
}
else
{
lean_object* x_786; lean_object* x_787; 
x_786 = lean_ctor_get(x_773, 1);
lean_inc(x_786);
lean_dec(x_773);
x_787 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_787, 0, x_3);
lean_ctor_set(x_787, 1, x_786);
return x_787;
}
}
}
else
{
uint8_t x_788; 
lean_dec(x_757);
lean_dec(x_754);
lean_dec(x_741);
lean_dec(x_740);
x_788 = !lean_is_exclusive(x_773);
if (x_788 == 0)
{
lean_object* x_789; 
x_789 = lean_ctor_get(x_773, 0);
lean_dec(x_789);
lean_ctor_set_tag(x_773, 0);
lean_ctor_set(x_773, 0, x_3);
return x_773;
}
else
{
lean_object* x_790; lean_object* x_791; 
x_790 = lean_ctor_get(x_773, 1);
lean_inc(x_790);
lean_dec(x_773);
x_791 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_791, 0, x_3);
lean_ctor_set(x_791, 1, x_790);
return x_791;
}
}
}
}
}
}
else
{
uint8_t x_873; 
lean_dec(x_741);
lean_dec(x_740);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_873 = !lean_is_exclusive(x_750);
if (x_873 == 0)
{
return x_750;
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_874 = lean_ctor_get(x_750, 0);
x_875 = lean_ctor_get(x_750, 1);
lean_inc(x_875);
lean_inc(x_874);
lean_dec(x_750);
x_876 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_876, 0, x_874);
lean_ctor_set(x_876, 1, x_875);
return x_876;
}
}
}
}
}
}
case 7:
{
lean_object* x_877; 
lean_dec(x_7);
lean_dec(x_6);
x_877 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_877) == 0)
{
lean_object* x_878; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_878 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_878, 0, x_3);
lean_ctor_set(x_878, 1, x_12);
return x_878;
}
else
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_879 = lean_ctor_get(x_877, 0);
lean_inc(x_879);
lean_dec(x_877);
x_880 = lean_unsigned_to_nat(0u);
x_881 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_880);
if (lean_obj_tag(x_881) == 0)
{
lean_object* x_882; 
lean_dec(x_879);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_882 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_882, 0, x_3);
lean_ctor_set(x_882, 1, x_12);
return x_882;
}
else
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; uint8_t x_887; 
x_883 = lean_ctor_get(x_881, 0);
lean_inc(x_883);
if (lean_is_exclusive(x_881)) {
 lean_ctor_release(x_881, 0);
 x_884 = x_881;
} else {
 lean_dec_ref(x_881);
 x_884 = lean_box(0);
}
x_885 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_879, x_8, x_9, x_10, x_11, x_12);
x_886 = lean_ctor_get(x_885, 0);
lean_inc(x_886);
x_887 = lean_unbox(x_886);
lean_dec(x_886);
if (x_887 == 0)
{
uint8_t x_888; 
lean_dec(x_884);
lean_dec(x_883);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_888 = !lean_is_exclusive(x_885);
if (x_888 == 0)
{
lean_object* x_889; 
x_889 = lean_ctor_get(x_885, 0);
lean_dec(x_889);
lean_ctor_set(x_885, 0, x_3);
return x_885;
}
else
{
lean_object* x_890; lean_object* x_891; 
x_890 = lean_ctor_get(x_885, 1);
lean_inc(x_890);
lean_dec(x_885);
x_891 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_891, 0, x_3);
lean_ctor_set(x_891, 1, x_890);
return x_891;
}
}
else
{
lean_object* x_892; lean_object* x_893; 
x_892 = lean_ctor_get(x_885, 1);
lean_inc(x_892);
lean_dec(x_885);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_893 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_883, x_8, x_9, x_10, x_11, x_892);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_936; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
lean_dec(x_893);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_897 = x_894;
} else {
 lean_dec_ref(x_894);
 x_897 = lean_box(0);
}
x_898 = lean_box(0);
lean_inc(x_8);
x_899 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_896, x_898, x_8, x_9, x_10, x_11, x_895);
x_900 = lean_ctor_get(x_899, 0);
lean_inc(x_900);
x_901 = lean_ctor_get(x_899, 1);
lean_inc(x_901);
if (lean_is_exclusive(x_899)) {
 lean_ctor_release(x_899, 0);
 lean_ctor_release(x_899, 1);
 x_902 = x_899;
} else {
 lean_dec_ref(x_899);
 x_902 = lean_box(0);
}
x_903 = l_Lean_Expr_mvarId_x21(x_900);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_936 = l_Lean_Meta_ppGoal(x_903, x_8, x_9, x_10, x_11, x_901);
if (lean_obj_tag(x_936) == 0)
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_994; lean_object* x_995; lean_object* x_996; uint8_t x_997; 
x_937 = lean_ctor_get(x_936, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_936, 1);
lean_inc(x_938);
lean_dec(x_936);
x_994 = lean_st_ref_get(x_11, x_938);
x_995 = lean_ctor_get(x_994, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_995, 3);
lean_inc(x_996);
lean_dec(x_995);
x_997 = lean_ctor_get_uint8(x_996, sizeof(void*)*1);
lean_dec(x_996);
if (x_997 == 0)
{
lean_object* x_998; 
lean_dec(x_937);
x_998 = lean_ctor_get(x_994, 1);
lean_inc(x_998);
lean_dec(x_994);
x_939 = x_998;
goto block_993;
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; 
x_999 = lean_ctor_get(x_994, 1);
lean_inc(x_999);
lean_dec(x_994);
x_1000 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1001 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1000, x_8, x_9, x_10, x_11, x_999);
x_1002 = lean_ctor_get(x_1001, 0);
lean_inc(x_1002);
x_1003 = lean_unbox(x_1002);
lean_dec(x_1002);
if (x_1003 == 0)
{
lean_object* x_1004; 
lean_dec(x_937);
x_1004 = lean_ctor_get(x_1001, 1);
lean_inc(x_1004);
lean_dec(x_1001);
x_939 = x_1004;
goto block_993;
}
else
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
x_1005 = lean_ctor_get(x_1001, 1);
lean_inc(x_1005);
lean_dec(x_1001);
x_1006 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1006, 0, x_937);
x_1007 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_1008 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_1006);
x_1009 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1009, 0, x_1008);
lean_ctor_set(x_1009, 1, x_1007);
x_1010 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1000, x_1009, x_8, x_9, x_10, x_11, x_1005);
x_1011 = lean_ctor_get(x_1010, 1);
lean_inc(x_1011);
lean_dec(x_1010);
x_939 = x_1011;
goto block_993;
}
}
block_993:
{
lean_object* x_940; lean_object* x_941; 
x_940 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_941 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_903, x_940, x_8, x_9, x_10, x_11, x_939);
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_942; uint8_t x_943; 
x_942 = lean_ctor_get(x_941, 0);
lean_inc(x_942);
x_943 = lean_unbox(x_942);
lean_dec(x_942);
if (x_943 == 0)
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; uint8_t x_948; 
lean_dec(x_902);
lean_dec(x_900);
lean_dec(x_897);
lean_dec(x_884);
lean_dec(x_883);
x_944 = lean_ctor_get(x_941, 1);
lean_inc(x_944);
lean_dec(x_941);
x_945 = lean_st_ref_get(x_11, x_944);
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_946, 3);
lean_inc(x_947);
lean_dec(x_946);
x_948 = lean_ctor_get_uint8(x_947, sizeof(void*)*1);
lean_dec(x_947);
if (x_948 == 0)
{
uint8_t x_949; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_949 = !lean_is_exclusive(x_945);
if (x_949 == 0)
{
lean_object* x_950; 
x_950 = lean_ctor_get(x_945, 0);
lean_dec(x_950);
lean_ctor_set(x_945, 0, x_3);
return x_945;
}
else
{
lean_object* x_951; lean_object* x_952; 
x_951 = lean_ctor_get(x_945, 1);
lean_inc(x_951);
lean_dec(x_945);
x_952 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_952, 0, x_3);
lean_ctor_set(x_952, 1, x_951);
return x_952;
}
}
else
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; uint8_t x_957; 
x_953 = lean_ctor_get(x_945, 1);
lean_inc(x_953);
lean_dec(x_945);
x_954 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_955 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_954, x_8, x_9, x_10, x_11, x_953);
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
x_957 = lean_unbox(x_956);
lean_dec(x_956);
if (x_957 == 0)
{
uint8_t x_958; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_958 = !lean_is_exclusive(x_955);
if (x_958 == 0)
{
lean_object* x_959; 
x_959 = lean_ctor_get(x_955, 0);
lean_dec(x_959);
lean_ctor_set(x_955, 0, x_3);
return x_955;
}
else
{
lean_object* x_960; lean_object* x_961; 
x_960 = lean_ctor_get(x_955, 1);
lean_inc(x_960);
lean_dec(x_955);
x_961 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_961, 0, x_3);
lean_ctor_set(x_961, 1, x_960);
return x_961;
}
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; uint8_t x_965; 
x_962 = lean_ctor_get(x_955, 1);
lean_inc(x_962);
lean_dec(x_955);
x_963 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_964 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_954, x_963, x_8, x_9, x_10, x_11, x_962);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_965 = !lean_is_exclusive(x_964);
if (x_965 == 0)
{
lean_object* x_966; 
x_966 = lean_ctor_get(x_964, 0);
lean_dec(x_966);
lean_ctor_set(x_964, 0, x_3);
return x_964;
}
else
{
lean_object* x_967; lean_object* x_968; 
x_967 = lean_ctor_get(x_964, 1);
lean_inc(x_967);
lean_dec(x_964);
x_968 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_968, 0, x_3);
lean_ctor_set(x_968, 1, x_967);
return x_968;
}
}
}
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; uint8_t x_973; 
x_969 = lean_ctor_get(x_941, 1);
lean_inc(x_969);
lean_dec(x_941);
x_970 = lean_st_ref_get(x_11, x_969);
x_971 = lean_ctor_get(x_970, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_971, 3);
lean_inc(x_972);
lean_dec(x_971);
x_973 = lean_ctor_get_uint8(x_972, sizeof(void*)*1);
lean_dec(x_972);
if (x_973 == 0)
{
lean_object* x_974; 
x_974 = lean_ctor_get(x_970, 1);
lean_inc(x_974);
lean_dec(x_970);
x_904 = x_974;
goto block_935;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; uint8_t x_979; 
x_975 = lean_ctor_get(x_970, 1);
lean_inc(x_975);
lean_dec(x_970);
x_976 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_977 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_976, x_8, x_9, x_10, x_11, x_975);
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
x_979 = lean_unbox(x_978);
lean_dec(x_978);
if (x_979 == 0)
{
lean_object* x_980; 
x_980 = lean_ctor_get(x_977, 1);
lean_inc(x_980);
lean_dec(x_977);
x_904 = x_980;
goto block_935;
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
x_981 = lean_ctor_get(x_977, 1);
lean_inc(x_981);
lean_dec(x_977);
lean_inc(x_900);
x_982 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_982, 0, x_900);
x_983 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_984 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_984, 0, x_983);
lean_ctor_set(x_984, 1, x_982);
x_985 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_986 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_986, 0, x_984);
lean_ctor_set(x_986, 1, x_985);
x_987 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_976, x_986, x_8, x_9, x_10, x_11, x_981);
x_988 = lean_ctor_get(x_987, 1);
lean_inc(x_988);
lean_dec(x_987);
x_904 = x_988;
goto block_935;
}
}
}
}
else
{
uint8_t x_989; 
lean_dec(x_902);
lean_dec(x_900);
lean_dec(x_897);
lean_dec(x_884);
lean_dec(x_883);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_989 = !lean_is_exclusive(x_941);
if (x_989 == 0)
{
lean_object* x_990; 
x_990 = lean_ctor_get(x_941, 0);
lean_dec(x_990);
lean_ctor_set_tag(x_941, 0);
lean_ctor_set(x_941, 0, x_3);
return x_941;
}
else
{
lean_object* x_991; lean_object* x_992; 
x_991 = lean_ctor_get(x_941, 1);
lean_inc(x_991);
lean_dec(x_941);
x_992 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_992, 0, x_3);
lean_ctor_set(x_992, 1, x_991);
return x_992;
}
}
}
}
else
{
uint8_t x_1012; 
lean_dec(x_903);
lean_dec(x_902);
lean_dec(x_900);
lean_dec(x_897);
lean_dec(x_884);
lean_dec(x_883);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1012 = !lean_is_exclusive(x_936);
if (x_1012 == 0)
{
lean_object* x_1013; 
x_1013 = lean_ctor_get(x_936, 0);
lean_dec(x_1013);
lean_ctor_set_tag(x_936, 0);
lean_ctor_set(x_936, 0, x_3);
return x_936;
}
else
{
lean_object* x_1014; lean_object* x_1015; 
x_1014 = lean_ctor_get(x_936, 1);
lean_inc(x_1014);
lean_dec(x_936);
x_1015 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1015, 0, x_3);
lean_ctor_set(x_1015, 1, x_1014);
return x_1015;
}
}
block_935:
{
lean_object* x_905; uint8_t x_906; 
x_905 = lean_array_get_size(x_1);
x_906 = lean_nat_dec_lt(x_880, x_905);
if (x_906 == 0)
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; 
lean_dec(x_905);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_897)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_897;
}
lean_ctor_set(x_907, 0, x_900);
lean_ctor_set(x_907, 1, x_883);
if (lean_is_scalar(x_884)) {
 x_908 = lean_alloc_ctor(1, 1, 0);
} else {
 x_908 = x_884;
}
lean_ctor_set(x_908, 0, x_907);
if (lean_is_scalar(x_902)) {
 x_909 = lean_alloc_ctor(0, 2, 0);
} else {
 x_909 = x_902;
}
lean_ctor_set(x_909, 0, x_908);
lean_ctor_set(x_909, 1, x_904);
return x_909;
}
else
{
uint8_t x_910; 
x_910 = lean_nat_dec_le(x_905, x_905);
if (x_910 == 0)
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_905);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_897)) {
 x_911 = lean_alloc_ctor(0, 2, 0);
} else {
 x_911 = x_897;
}
lean_ctor_set(x_911, 0, x_900);
lean_ctor_set(x_911, 1, x_883);
if (lean_is_scalar(x_884)) {
 x_912 = lean_alloc_ctor(1, 1, 0);
} else {
 x_912 = x_884;
}
lean_ctor_set(x_912, 0, x_911);
if (lean_is_scalar(x_902)) {
 x_913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_913 = x_902;
}
lean_ctor_set(x_913, 0, x_912);
lean_ctor_set(x_913, 1, x_904);
return x_913;
}
else
{
size_t x_914; size_t x_915; lean_object* x_916; 
lean_dec(x_902);
x_914 = 0;
x_915 = lean_usize_of_nat(x_905);
lean_dec(x_905);
lean_inc(x_900);
x_916 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_900, x_1, x_914, x_915, x_8, x_9, x_10, x_11, x_904);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; uint8_t x_918; 
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
x_918 = lean_unbox(x_917);
lean_dec(x_917);
if (x_918 == 0)
{
uint8_t x_919; 
lean_dec(x_3);
x_919 = !lean_is_exclusive(x_916);
if (x_919 == 0)
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_920 = lean_ctor_get(x_916, 0);
lean_dec(x_920);
if (lean_is_scalar(x_897)) {
 x_921 = lean_alloc_ctor(0, 2, 0);
} else {
 x_921 = x_897;
}
lean_ctor_set(x_921, 0, x_900);
lean_ctor_set(x_921, 1, x_883);
if (lean_is_scalar(x_884)) {
 x_922 = lean_alloc_ctor(1, 1, 0);
} else {
 x_922 = x_884;
}
lean_ctor_set(x_922, 0, x_921);
lean_ctor_set(x_916, 0, x_922);
return x_916;
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_923 = lean_ctor_get(x_916, 1);
lean_inc(x_923);
lean_dec(x_916);
if (lean_is_scalar(x_897)) {
 x_924 = lean_alloc_ctor(0, 2, 0);
} else {
 x_924 = x_897;
}
lean_ctor_set(x_924, 0, x_900);
lean_ctor_set(x_924, 1, x_883);
if (lean_is_scalar(x_884)) {
 x_925 = lean_alloc_ctor(1, 1, 0);
} else {
 x_925 = x_884;
}
lean_ctor_set(x_925, 0, x_924);
x_926 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_926, 0, x_925);
lean_ctor_set(x_926, 1, x_923);
return x_926;
}
}
else
{
uint8_t x_927; 
lean_dec(x_900);
lean_dec(x_897);
lean_dec(x_884);
lean_dec(x_883);
x_927 = !lean_is_exclusive(x_916);
if (x_927 == 0)
{
lean_object* x_928; 
x_928 = lean_ctor_get(x_916, 0);
lean_dec(x_928);
lean_ctor_set(x_916, 0, x_3);
return x_916;
}
else
{
lean_object* x_929; lean_object* x_930; 
x_929 = lean_ctor_get(x_916, 1);
lean_inc(x_929);
lean_dec(x_916);
x_930 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_930, 0, x_3);
lean_ctor_set(x_930, 1, x_929);
return x_930;
}
}
}
else
{
uint8_t x_931; 
lean_dec(x_900);
lean_dec(x_897);
lean_dec(x_884);
lean_dec(x_883);
x_931 = !lean_is_exclusive(x_916);
if (x_931 == 0)
{
lean_object* x_932; 
x_932 = lean_ctor_get(x_916, 0);
lean_dec(x_932);
lean_ctor_set_tag(x_916, 0);
lean_ctor_set(x_916, 0, x_3);
return x_916;
}
else
{
lean_object* x_933; lean_object* x_934; 
x_933 = lean_ctor_get(x_916, 1);
lean_inc(x_933);
lean_dec(x_916);
x_934 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_934, 0, x_3);
lean_ctor_set(x_934, 1, x_933);
return x_934;
}
}
}
}
}
}
else
{
uint8_t x_1016; 
lean_dec(x_884);
lean_dec(x_883);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_1016 = !lean_is_exclusive(x_893);
if (x_1016 == 0)
{
return x_893;
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1017 = lean_ctor_get(x_893, 0);
x_1018 = lean_ctor_get(x_893, 1);
lean_inc(x_1018);
lean_inc(x_1017);
lean_dec(x_893);
x_1019 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1019, 0, x_1017);
lean_ctor_set(x_1019, 1, x_1018);
return x_1019;
}
}
}
}
}
}
case 8:
{
lean_object* x_1020; 
lean_dec(x_7);
lean_dec(x_6);
x_1020 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_1020) == 0)
{
lean_object* x_1021; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1021 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1021, 0, x_3);
lean_ctor_set(x_1021, 1, x_12);
return x_1021;
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1022 = lean_ctor_get(x_1020, 0);
lean_inc(x_1022);
lean_dec(x_1020);
x_1023 = lean_unsigned_to_nat(0u);
x_1024 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_1023);
if (lean_obj_tag(x_1024) == 0)
{
lean_object* x_1025; 
lean_dec(x_1022);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1025 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1025, 0, x_3);
lean_ctor_set(x_1025, 1, x_12);
return x_1025;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; uint8_t x_1030; 
x_1026 = lean_ctor_get(x_1024, 0);
lean_inc(x_1026);
if (lean_is_exclusive(x_1024)) {
 lean_ctor_release(x_1024, 0);
 x_1027 = x_1024;
} else {
 lean_dec_ref(x_1024);
 x_1027 = lean_box(0);
}
x_1028 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1022, x_8, x_9, x_10, x_11, x_12);
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_unbox(x_1029);
lean_dec(x_1029);
if (x_1030 == 0)
{
uint8_t x_1031; 
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1031 = !lean_is_exclusive(x_1028);
if (x_1031 == 0)
{
lean_object* x_1032; 
x_1032 = lean_ctor_get(x_1028, 0);
lean_dec(x_1032);
lean_ctor_set(x_1028, 0, x_3);
return x_1028;
}
else
{
lean_object* x_1033; lean_object* x_1034; 
x_1033 = lean_ctor_get(x_1028, 1);
lean_inc(x_1033);
lean_dec(x_1028);
x_1034 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1034, 0, x_3);
lean_ctor_set(x_1034, 1, x_1033);
return x_1034;
}
}
else
{
lean_object* x_1035; lean_object* x_1036; 
x_1035 = lean_ctor_get(x_1028, 1);
lean_inc(x_1035);
lean_dec(x_1028);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1036 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_1026, x_8, x_9, x_10, x_11, x_1035);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1079; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1036, 1);
lean_inc(x_1038);
lean_dec(x_1036);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
if (lean_is_exclusive(x_1037)) {
 lean_ctor_release(x_1037, 0);
 lean_ctor_release(x_1037, 1);
 x_1040 = x_1037;
} else {
 lean_dec_ref(x_1037);
 x_1040 = lean_box(0);
}
x_1041 = lean_box(0);
lean_inc(x_8);
x_1042 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1039, x_1041, x_8, x_9, x_10, x_11, x_1038);
x_1043 = lean_ctor_get(x_1042, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_1042, 1);
lean_inc(x_1044);
if (lean_is_exclusive(x_1042)) {
 lean_ctor_release(x_1042, 0);
 lean_ctor_release(x_1042, 1);
 x_1045 = x_1042;
} else {
 lean_dec_ref(x_1042);
 x_1045 = lean_box(0);
}
x_1046 = l_Lean_Expr_mvarId_x21(x_1043);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1079 = l_Lean_Meta_ppGoal(x_1046, x_8, x_9, x_10, x_11, x_1044);
if (lean_obj_tag(x_1079) == 0)
{
lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; uint8_t x_1140; 
x_1080 = lean_ctor_get(x_1079, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1079, 1);
lean_inc(x_1081);
lean_dec(x_1079);
x_1137 = lean_st_ref_get(x_11, x_1081);
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1138, 3);
lean_inc(x_1139);
lean_dec(x_1138);
x_1140 = lean_ctor_get_uint8(x_1139, sizeof(void*)*1);
lean_dec(x_1139);
if (x_1140 == 0)
{
lean_object* x_1141; 
lean_dec(x_1080);
x_1141 = lean_ctor_get(x_1137, 1);
lean_inc(x_1141);
lean_dec(x_1137);
x_1082 = x_1141;
goto block_1136;
}
else
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; uint8_t x_1146; 
x_1142 = lean_ctor_get(x_1137, 1);
lean_inc(x_1142);
lean_dec(x_1137);
x_1143 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1144 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1143, x_8, x_9, x_10, x_11, x_1142);
x_1145 = lean_ctor_get(x_1144, 0);
lean_inc(x_1145);
x_1146 = lean_unbox(x_1145);
lean_dec(x_1145);
if (x_1146 == 0)
{
lean_object* x_1147; 
lean_dec(x_1080);
x_1147 = lean_ctor_get(x_1144, 1);
lean_inc(x_1147);
lean_dec(x_1144);
x_1082 = x_1147;
goto block_1136;
}
else
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; 
x_1148 = lean_ctor_get(x_1144, 1);
lean_inc(x_1148);
lean_dec(x_1144);
x_1149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1149, 0, x_1080);
x_1150 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_1151 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1151, 0, x_1150);
lean_ctor_set(x_1151, 1, x_1149);
x_1152 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1152, 0, x_1151);
lean_ctor_set(x_1152, 1, x_1150);
x_1153 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1143, x_1152, x_8, x_9, x_10, x_11, x_1148);
x_1154 = lean_ctor_get(x_1153, 1);
lean_inc(x_1154);
lean_dec(x_1153);
x_1082 = x_1154;
goto block_1136;
}
}
block_1136:
{
lean_object* x_1083; lean_object* x_1084; 
x_1083 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1084 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1046, x_1083, x_8, x_9, x_10, x_11, x_1082);
if (lean_obj_tag(x_1084) == 0)
{
lean_object* x_1085; uint8_t x_1086; 
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_unbox(x_1085);
lean_dec(x_1085);
if (x_1086 == 0)
{
lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; uint8_t x_1091; 
lean_dec(x_1045);
lean_dec(x_1043);
lean_dec(x_1040);
lean_dec(x_1027);
lean_dec(x_1026);
x_1087 = lean_ctor_get(x_1084, 1);
lean_inc(x_1087);
lean_dec(x_1084);
x_1088 = lean_st_ref_get(x_11, x_1087);
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1089, 3);
lean_inc(x_1090);
lean_dec(x_1089);
x_1091 = lean_ctor_get_uint8(x_1090, sizeof(void*)*1);
lean_dec(x_1090);
if (x_1091 == 0)
{
uint8_t x_1092; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1092 = !lean_is_exclusive(x_1088);
if (x_1092 == 0)
{
lean_object* x_1093; 
x_1093 = lean_ctor_get(x_1088, 0);
lean_dec(x_1093);
lean_ctor_set(x_1088, 0, x_3);
return x_1088;
}
else
{
lean_object* x_1094; lean_object* x_1095; 
x_1094 = lean_ctor_get(x_1088, 1);
lean_inc(x_1094);
lean_dec(x_1088);
x_1095 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1095, 0, x_3);
lean_ctor_set(x_1095, 1, x_1094);
return x_1095;
}
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; uint8_t x_1100; 
x_1096 = lean_ctor_get(x_1088, 1);
lean_inc(x_1096);
lean_dec(x_1088);
x_1097 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1098 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1097, x_8, x_9, x_10, x_11, x_1096);
x_1099 = lean_ctor_get(x_1098, 0);
lean_inc(x_1099);
x_1100 = lean_unbox(x_1099);
lean_dec(x_1099);
if (x_1100 == 0)
{
uint8_t x_1101; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1101 = !lean_is_exclusive(x_1098);
if (x_1101 == 0)
{
lean_object* x_1102; 
x_1102 = lean_ctor_get(x_1098, 0);
lean_dec(x_1102);
lean_ctor_set(x_1098, 0, x_3);
return x_1098;
}
else
{
lean_object* x_1103; lean_object* x_1104; 
x_1103 = lean_ctor_get(x_1098, 1);
lean_inc(x_1103);
lean_dec(x_1098);
x_1104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1104, 0, x_3);
lean_ctor_set(x_1104, 1, x_1103);
return x_1104;
}
}
else
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; uint8_t x_1108; 
x_1105 = lean_ctor_get(x_1098, 1);
lean_inc(x_1105);
lean_dec(x_1098);
x_1106 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_1107 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1097, x_1106, x_8, x_9, x_10, x_11, x_1105);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1108 = !lean_is_exclusive(x_1107);
if (x_1108 == 0)
{
lean_object* x_1109; 
x_1109 = lean_ctor_get(x_1107, 0);
lean_dec(x_1109);
lean_ctor_set(x_1107, 0, x_3);
return x_1107;
}
else
{
lean_object* x_1110; lean_object* x_1111; 
x_1110 = lean_ctor_get(x_1107, 1);
lean_inc(x_1110);
lean_dec(x_1107);
x_1111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1111, 0, x_3);
lean_ctor_set(x_1111, 1, x_1110);
return x_1111;
}
}
}
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; uint8_t x_1116; 
x_1112 = lean_ctor_get(x_1084, 1);
lean_inc(x_1112);
lean_dec(x_1084);
x_1113 = lean_st_ref_get(x_11, x_1112);
x_1114 = lean_ctor_get(x_1113, 0);
lean_inc(x_1114);
x_1115 = lean_ctor_get(x_1114, 3);
lean_inc(x_1115);
lean_dec(x_1114);
x_1116 = lean_ctor_get_uint8(x_1115, sizeof(void*)*1);
lean_dec(x_1115);
if (x_1116 == 0)
{
lean_object* x_1117; 
x_1117 = lean_ctor_get(x_1113, 1);
lean_inc(x_1117);
lean_dec(x_1113);
x_1047 = x_1117;
goto block_1078;
}
else
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; uint8_t x_1122; 
x_1118 = lean_ctor_get(x_1113, 1);
lean_inc(x_1118);
lean_dec(x_1113);
x_1119 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1120 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1119, x_8, x_9, x_10, x_11, x_1118);
x_1121 = lean_ctor_get(x_1120, 0);
lean_inc(x_1121);
x_1122 = lean_unbox(x_1121);
lean_dec(x_1121);
if (x_1122 == 0)
{
lean_object* x_1123; 
x_1123 = lean_ctor_get(x_1120, 1);
lean_inc(x_1123);
lean_dec(x_1120);
x_1047 = x_1123;
goto block_1078;
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; 
x_1124 = lean_ctor_get(x_1120, 1);
lean_inc(x_1124);
lean_dec(x_1120);
lean_inc(x_1043);
x_1125 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1125, 0, x_1043);
x_1126 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1127 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1127, 0, x_1126);
lean_ctor_set(x_1127, 1, x_1125);
x_1128 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_1129 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1129, 0, x_1127);
lean_ctor_set(x_1129, 1, x_1128);
x_1130 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1119, x_1129, x_8, x_9, x_10, x_11, x_1124);
x_1131 = lean_ctor_get(x_1130, 1);
lean_inc(x_1131);
lean_dec(x_1130);
x_1047 = x_1131;
goto block_1078;
}
}
}
}
else
{
uint8_t x_1132; 
lean_dec(x_1045);
lean_dec(x_1043);
lean_dec(x_1040);
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1132 = !lean_is_exclusive(x_1084);
if (x_1132 == 0)
{
lean_object* x_1133; 
x_1133 = lean_ctor_get(x_1084, 0);
lean_dec(x_1133);
lean_ctor_set_tag(x_1084, 0);
lean_ctor_set(x_1084, 0, x_3);
return x_1084;
}
else
{
lean_object* x_1134; lean_object* x_1135; 
x_1134 = lean_ctor_get(x_1084, 1);
lean_inc(x_1134);
lean_dec(x_1084);
x_1135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1135, 0, x_3);
lean_ctor_set(x_1135, 1, x_1134);
return x_1135;
}
}
}
}
else
{
uint8_t x_1155; 
lean_dec(x_1046);
lean_dec(x_1045);
lean_dec(x_1043);
lean_dec(x_1040);
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1155 = !lean_is_exclusive(x_1079);
if (x_1155 == 0)
{
lean_object* x_1156; 
x_1156 = lean_ctor_get(x_1079, 0);
lean_dec(x_1156);
lean_ctor_set_tag(x_1079, 0);
lean_ctor_set(x_1079, 0, x_3);
return x_1079;
}
else
{
lean_object* x_1157; lean_object* x_1158; 
x_1157 = lean_ctor_get(x_1079, 1);
lean_inc(x_1157);
lean_dec(x_1079);
x_1158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1158, 0, x_3);
lean_ctor_set(x_1158, 1, x_1157);
return x_1158;
}
}
block_1078:
{
lean_object* x_1048; uint8_t x_1049; 
x_1048 = lean_array_get_size(x_1);
x_1049 = lean_nat_dec_lt(x_1023, x_1048);
if (x_1049 == 0)
{
lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_1048);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1040)) {
 x_1050 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1050 = x_1040;
}
lean_ctor_set(x_1050, 0, x_1043);
lean_ctor_set(x_1050, 1, x_1026);
if (lean_is_scalar(x_1027)) {
 x_1051 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1051 = x_1027;
}
lean_ctor_set(x_1051, 0, x_1050);
if (lean_is_scalar(x_1045)) {
 x_1052 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1052 = x_1045;
}
lean_ctor_set(x_1052, 0, x_1051);
lean_ctor_set(x_1052, 1, x_1047);
return x_1052;
}
else
{
uint8_t x_1053; 
x_1053 = lean_nat_dec_le(x_1048, x_1048);
if (x_1053 == 0)
{
lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1048);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1040)) {
 x_1054 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1054 = x_1040;
}
lean_ctor_set(x_1054, 0, x_1043);
lean_ctor_set(x_1054, 1, x_1026);
if (lean_is_scalar(x_1027)) {
 x_1055 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1055 = x_1027;
}
lean_ctor_set(x_1055, 0, x_1054);
if (lean_is_scalar(x_1045)) {
 x_1056 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1056 = x_1045;
}
lean_ctor_set(x_1056, 0, x_1055);
lean_ctor_set(x_1056, 1, x_1047);
return x_1056;
}
else
{
size_t x_1057; size_t x_1058; lean_object* x_1059; 
lean_dec(x_1045);
x_1057 = 0;
x_1058 = lean_usize_of_nat(x_1048);
lean_dec(x_1048);
lean_inc(x_1043);
x_1059 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1043, x_1, x_1057, x_1058, x_8, x_9, x_10, x_11, x_1047);
if (lean_obj_tag(x_1059) == 0)
{
lean_object* x_1060; uint8_t x_1061; 
x_1060 = lean_ctor_get(x_1059, 0);
lean_inc(x_1060);
x_1061 = lean_unbox(x_1060);
lean_dec(x_1060);
if (x_1061 == 0)
{
uint8_t x_1062; 
lean_dec(x_3);
x_1062 = !lean_is_exclusive(x_1059);
if (x_1062 == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1063 = lean_ctor_get(x_1059, 0);
lean_dec(x_1063);
if (lean_is_scalar(x_1040)) {
 x_1064 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1064 = x_1040;
}
lean_ctor_set(x_1064, 0, x_1043);
lean_ctor_set(x_1064, 1, x_1026);
if (lean_is_scalar(x_1027)) {
 x_1065 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1065 = x_1027;
}
lean_ctor_set(x_1065, 0, x_1064);
lean_ctor_set(x_1059, 0, x_1065);
return x_1059;
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1066 = lean_ctor_get(x_1059, 1);
lean_inc(x_1066);
lean_dec(x_1059);
if (lean_is_scalar(x_1040)) {
 x_1067 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1067 = x_1040;
}
lean_ctor_set(x_1067, 0, x_1043);
lean_ctor_set(x_1067, 1, x_1026);
if (lean_is_scalar(x_1027)) {
 x_1068 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1068 = x_1027;
}
lean_ctor_set(x_1068, 0, x_1067);
x_1069 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1069, 0, x_1068);
lean_ctor_set(x_1069, 1, x_1066);
return x_1069;
}
}
else
{
uint8_t x_1070; 
lean_dec(x_1043);
lean_dec(x_1040);
lean_dec(x_1027);
lean_dec(x_1026);
x_1070 = !lean_is_exclusive(x_1059);
if (x_1070 == 0)
{
lean_object* x_1071; 
x_1071 = lean_ctor_get(x_1059, 0);
lean_dec(x_1071);
lean_ctor_set(x_1059, 0, x_3);
return x_1059;
}
else
{
lean_object* x_1072; lean_object* x_1073; 
x_1072 = lean_ctor_get(x_1059, 1);
lean_inc(x_1072);
lean_dec(x_1059);
x_1073 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1073, 0, x_3);
lean_ctor_set(x_1073, 1, x_1072);
return x_1073;
}
}
}
else
{
uint8_t x_1074; 
lean_dec(x_1043);
lean_dec(x_1040);
lean_dec(x_1027);
lean_dec(x_1026);
x_1074 = !lean_is_exclusive(x_1059);
if (x_1074 == 0)
{
lean_object* x_1075; 
x_1075 = lean_ctor_get(x_1059, 0);
lean_dec(x_1075);
lean_ctor_set_tag(x_1059, 0);
lean_ctor_set(x_1059, 0, x_3);
return x_1059;
}
else
{
lean_object* x_1076; lean_object* x_1077; 
x_1076 = lean_ctor_get(x_1059, 1);
lean_inc(x_1076);
lean_dec(x_1059);
x_1077 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1077, 0, x_3);
lean_ctor_set(x_1077, 1, x_1076);
return x_1077;
}
}
}
}
}
}
else
{
uint8_t x_1159; 
lean_dec(x_1027);
lean_dec(x_1026);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_1159 = !lean_is_exclusive(x_1036);
if (x_1159 == 0)
{
return x_1036;
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
x_1160 = lean_ctor_get(x_1036, 0);
x_1161 = lean_ctor_get(x_1036, 1);
lean_inc(x_1161);
lean_inc(x_1160);
lean_dec(x_1036);
x_1162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1162, 0, x_1160);
lean_ctor_set(x_1162, 1, x_1161);
return x_1162;
}
}
}
}
}
}
case 9:
{
lean_object* x_1163; 
lean_dec(x_7);
lean_dec(x_6);
x_1163 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_1163) == 0)
{
lean_object* x_1164; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1164, 0, x_3);
lean_ctor_set(x_1164, 1, x_12);
return x_1164;
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1165 = lean_ctor_get(x_1163, 0);
lean_inc(x_1165);
lean_dec(x_1163);
x_1166 = lean_unsigned_to_nat(0u);
x_1167 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_1166);
if (lean_obj_tag(x_1167) == 0)
{
lean_object* x_1168; 
lean_dec(x_1165);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1168, 0, x_3);
lean_ctor_set(x_1168, 1, x_12);
return x_1168;
}
else
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; uint8_t x_1173; 
x_1169 = lean_ctor_get(x_1167, 0);
lean_inc(x_1169);
if (lean_is_exclusive(x_1167)) {
 lean_ctor_release(x_1167, 0);
 x_1170 = x_1167;
} else {
 lean_dec_ref(x_1167);
 x_1170 = lean_box(0);
}
x_1171 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1165, x_8, x_9, x_10, x_11, x_12);
x_1172 = lean_ctor_get(x_1171, 0);
lean_inc(x_1172);
x_1173 = lean_unbox(x_1172);
lean_dec(x_1172);
if (x_1173 == 0)
{
uint8_t x_1174; 
lean_dec(x_1170);
lean_dec(x_1169);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1174 = !lean_is_exclusive(x_1171);
if (x_1174 == 0)
{
lean_object* x_1175; 
x_1175 = lean_ctor_get(x_1171, 0);
lean_dec(x_1175);
lean_ctor_set(x_1171, 0, x_3);
return x_1171;
}
else
{
lean_object* x_1176; lean_object* x_1177; 
x_1176 = lean_ctor_get(x_1171, 1);
lean_inc(x_1176);
lean_dec(x_1171);
x_1177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1177, 0, x_3);
lean_ctor_set(x_1177, 1, x_1176);
return x_1177;
}
}
else
{
lean_object* x_1178; lean_object* x_1179; 
x_1178 = lean_ctor_get(x_1171, 1);
lean_inc(x_1178);
lean_dec(x_1171);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1179 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_1169, x_8, x_9, x_10, x_11, x_1178);
if (lean_obj_tag(x_1179) == 0)
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1222; 
x_1180 = lean_ctor_get(x_1179, 0);
lean_inc(x_1180);
x_1181 = lean_ctor_get(x_1179, 1);
lean_inc(x_1181);
lean_dec(x_1179);
x_1182 = lean_ctor_get(x_1180, 1);
lean_inc(x_1182);
if (lean_is_exclusive(x_1180)) {
 lean_ctor_release(x_1180, 0);
 lean_ctor_release(x_1180, 1);
 x_1183 = x_1180;
} else {
 lean_dec_ref(x_1180);
 x_1183 = lean_box(0);
}
x_1184 = lean_box(0);
lean_inc(x_8);
x_1185 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1182, x_1184, x_8, x_9, x_10, x_11, x_1181);
x_1186 = lean_ctor_get(x_1185, 0);
lean_inc(x_1186);
x_1187 = lean_ctor_get(x_1185, 1);
lean_inc(x_1187);
if (lean_is_exclusive(x_1185)) {
 lean_ctor_release(x_1185, 0);
 lean_ctor_release(x_1185, 1);
 x_1188 = x_1185;
} else {
 lean_dec_ref(x_1185);
 x_1188 = lean_box(0);
}
x_1189 = l_Lean_Expr_mvarId_x21(x_1186);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1222 = l_Lean_Meta_ppGoal(x_1189, x_8, x_9, x_10, x_11, x_1187);
if (lean_obj_tag(x_1222) == 0)
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; uint8_t x_1283; 
x_1223 = lean_ctor_get(x_1222, 0);
lean_inc(x_1223);
x_1224 = lean_ctor_get(x_1222, 1);
lean_inc(x_1224);
lean_dec(x_1222);
x_1280 = lean_st_ref_get(x_11, x_1224);
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1281, 3);
lean_inc(x_1282);
lean_dec(x_1281);
x_1283 = lean_ctor_get_uint8(x_1282, sizeof(void*)*1);
lean_dec(x_1282);
if (x_1283 == 0)
{
lean_object* x_1284; 
lean_dec(x_1223);
x_1284 = lean_ctor_get(x_1280, 1);
lean_inc(x_1284);
lean_dec(x_1280);
x_1225 = x_1284;
goto block_1279;
}
else
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; uint8_t x_1289; 
x_1285 = lean_ctor_get(x_1280, 1);
lean_inc(x_1285);
lean_dec(x_1280);
x_1286 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1287 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1286, x_8, x_9, x_10, x_11, x_1285);
x_1288 = lean_ctor_get(x_1287, 0);
lean_inc(x_1288);
x_1289 = lean_unbox(x_1288);
lean_dec(x_1288);
if (x_1289 == 0)
{
lean_object* x_1290; 
lean_dec(x_1223);
x_1290 = lean_ctor_get(x_1287, 1);
lean_inc(x_1290);
lean_dec(x_1287);
x_1225 = x_1290;
goto block_1279;
}
else
{
lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1291 = lean_ctor_get(x_1287, 1);
lean_inc(x_1291);
lean_dec(x_1287);
x_1292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1292, 0, x_1223);
x_1293 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_1294 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1294, 0, x_1293);
lean_ctor_set(x_1294, 1, x_1292);
x_1295 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1295, 0, x_1294);
lean_ctor_set(x_1295, 1, x_1293);
x_1296 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1286, x_1295, x_8, x_9, x_10, x_11, x_1291);
x_1297 = lean_ctor_get(x_1296, 1);
lean_inc(x_1297);
lean_dec(x_1296);
x_1225 = x_1297;
goto block_1279;
}
}
block_1279:
{
lean_object* x_1226; lean_object* x_1227; 
x_1226 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1227 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1189, x_1226, x_8, x_9, x_10, x_11, x_1225);
if (lean_obj_tag(x_1227) == 0)
{
lean_object* x_1228; uint8_t x_1229; 
x_1228 = lean_ctor_get(x_1227, 0);
lean_inc(x_1228);
x_1229 = lean_unbox(x_1228);
lean_dec(x_1228);
if (x_1229 == 0)
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; uint8_t x_1234; 
lean_dec(x_1188);
lean_dec(x_1186);
lean_dec(x_1183);
lean_dec(x_1170);
lean_dec(x_1169);
x_1230 = lean_ctor_get(x_1227, 1);
lean_inc(x_1230);
lean_dec(x_1227);
x_1231 = lean_st_ref_get(x_11, x_1230);
x_1232 = lean_ctor_get(x_1231, 0);
lean_inc(x_1232);
x_1233 = lean_ctor_get(x_1232, 3);
lean_inc(x_1233);
lean_dec(x_1232);
x_1234 = lean_ctor_get_uint8(x_1233, sizeof(void*)*1);
lean_dec(x_1233);
if (x_1234 == 0)
{
uint8_t x_1235; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1235 = !lean_is_exclusive(x_1231);
if (x_1235 == 0)
{
lean_object* x_1236; 
x_1236 = lean_ctor_get(x_1231, 0);
lean_dec(x_1236);
lean_ctor_set(x_1231, 0, x_3);
return x_1231;
}
else
{
lean_object* x_1237; lean_object* x_1238; 
x_1237 = lean_ctor_get(x_1231, 1);
lean_inc(x_1237);
lean_dec(x_1231);
x_1238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1238, 0, x_3);
lean_ctor_set(x_1238, 1, x_1237);
return x_1238;
}
}
else
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; uint8_t x_1243; 
x_1239 = lean_ctor_get(x_1231, 1);
lean_inc(x_1239);
lean_dec(x_1231);
x_1240 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1241 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1240, x_8, x_9, x_10, x_11, x_1239);
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
x_1243 = lean_unbox(x_1242);
lean_dec(x_1242);
if (x_1243 == 0)
{
uint8_t x_1244; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1244 = !lean_is_exclusive(x_1241);
if (x_1244 == 0)
{
lean_object* x_1245; 
x_1245 = lean_ctor_get(x_1241, 0);
lean_dec(x_1245);
lean_ctor_set(x_1241, 0, x_3);
return x_1241;
}
else
{
lean_object* x_1246; lean_object* x_1247; 
x_1246 = lean_ctor_get(x_1241, 1);
lean_inc(x_1246);
lean_dec(x_1241);
x_1247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1247, 0, x_3);
lean_ctor_set(x_1247, 1, x_1246);
return x_1247;
}
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; uint8_t x_1251; 
x_1248 = lean_ctor_get(x_1241, 1);
lean_inc(x_1248);
lean_dec(x_1241);
x_1249 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_1250 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1240, x_1249, x_8, x_9, x_10, x_11, x_1248);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1251 = !lean_is_exclusive(x_1250);
if (x_1251 == 0)
{
lean_object* x_1252; 
x_1252 = lean_ctor_get(x_1250, 0);
lean_dec(x_1252);
lean_ctor_set(x_1250, 0, x_3);
return x_1250;
}
else
{
lean_object* x_1253; lean_object* x_1254; 
x_1253 = lean_ctor_get(x_1250, 1);
lean_inc(x_1253);
lean_dec(x_1250);
x_1254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1254, 0, x_3);
lean_ctor_set(x_1254, 1, x_1253);
return x_1254;
}
}
}
}
else
{
lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; uint8_t x_1259; 
x_1255 = lean_ctor_get(x_1227, 1);
lean_inc(x_1255);
lean_dec(x_1227);
x_1256 = lean_st_ref_get(x_11, x_1255);
x_1257 = lean_ctor_get(x_1256, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1257, 3);
lean_inc(x_1258);
lean_dec(x_1257);
x_1259 = lean_ctor_get_uint8(x_1258, sizeof(void*)*1);
lean_dec(x_1258);
if (x_1259 == 0)
{
lean_object* x_1260; 
x_1260 = lean_ctor_get(x_1256, 1);
lean_inc(x_1260);
lean_dec(x_1256);
x_1190 = x_1260;
goto block_1221;
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; uint8_t x_1265; 
x_1261 = lean_ctor_get(x_1256, 1);
lean_inc(x_1261);
lean_dec(x_1256);
x_1262 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1263 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1262, x_8, x_9, x_10, x_11, x_1261);
x_1264 = lean_ctor_get(x_1263, 0);
lean_inc(x_1264);
x_1265 = lean_unbox(x_1264);
lean_dec(x_1264);
if (x_1265 == 0)
{
lean_object* x_1266; 
x_1266 = lean_ctor_get(x_1263, 1);
lean_inc(x_1266);
lean_dec(x_1263);
x_1190 = x_1266;
goto block_1221;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; 
x_1267 = lean_ctor_get(x_1263, 1);
lean_inc(x_1267);
lean_dec(x_1263);
lean_inc(x_1186);
x_1268 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1268, 0, x_1186);
x_1269 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1270 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1270, 0, x_1269);
lean_ctor_set(x_1270, 1, x_1268);
x_1271 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_1272 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1272, 0, x_1270);
lean_ctor_set(x_1272, 1, x_1271);
x_1273 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1262, x_1272, x_8, x_9, x_10, x_11, x_1267);
x_1274 = lean_ctor_get(x_1273, 1);
lean_inc(x_1274);
lean_dec(x_1273);
x_1190 = x_1274;
goto block_1221;
}
}
}
}
else
{
uint8_t x_1275; 
lean_dec(x_1188);
lean_dec(x_1186);
lean_dec(x_1183);
lean_dec(x_1170);
lean_dec(x_1169);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1275 = !lean_is_exclusive(x_1227);
if (x_1275 == 0)
{
lean_object* x_1276; 
x_1276 = lean_ctor_get(x_1227, 0);
lean_dec(x_1276);
lean_ctor_set_tag(x_1227, 0);
lean_ctor_set(x_1227, 0, x_3);
return x_1227;
}
else
{
lean_object* x_1277; lean_object* x_1278; 
x_1277 = lean_ctor_get(x_1227, 1);
lean_inc(x_1277);
lean_dec(x_1227);
x_1278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1278, 0, x_3);
lean_ctor_set(x_1278, 1, x_1277);
return x_1278;
}
}
}
}
else
{
uint8_t x_1298; 
lean_dec(x_1189);
lean_dec(x_1188);
lean_dec(x_1186);
lean_dec(x_1183);
lean_dec(x_1170);
lean_dec(x_1169);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1298 = !lean_is_exclusive(x_1222);
if (x_1298 == 0)
{
lean_object* x_1299; 
x_1299 = lean_ctor_get(x_1222, 0);
lean_dec(x_1299);
lean_ctor_set_tag(x_1222, 0);
lean_ctor_set(x_1222, 0, x_3);
return x_1222;
}
else
{
lean_object* x_1300; lean_object* x_1301; 
x_1300 = lean_ctor_get(x_1222, 1);
lean_inc(x_1300);
lean_dec(x_1222);
x_1301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1301, 0, x_3);
lean_ctor_set(x_1301, 1, x_1300);
return x_1301;
}
}
block_1221:
{
lean_object* x_1191; uint8_t x_1192; 
x_1191 = lean_array_get_size(x_1);
x_1192 = lean_nat_dec_lt(x_1166, x_1191);
if (x_1192 == 0)
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
lean_dec(x_1191);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1183)) {
 x_1193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1193 = x_1183;
}
lean_ctor_set(x_1193, 0, x_1186);
lean_ctor_set(x_1193, 1, x_1169);
if (lean_is_scalar(x_1170)) {
 x_1194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1194 = x_1170;
}
lean_ctor_set(x_1194, 0, x_1193);
if (lean_is_scalar(x_1188)) {
 x_1195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1195 = x_1188;
}
lean_ctor_set(x_1195, 0, x_1194);
lean_ctor_set(x_1195, 1, x_1190);
return x_1195;
}
else
{
uint8_t x_1196; 
x_1196 = lean_nat_dec_le(x_1191, x_1191);
if (x_1196 == 0)
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
lean_dec(x_1191);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1183)) {
 x_1197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1197 = x_1183;
}
lean_ctor_set(x_1197, 0, x_1186);
lean_ctor_set(x_1197, 1, x_1169);
if (lean_is_scalar(x_1170)) {
 x_1198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1198 = x_1170;
}
lean_ctor_set(x_1198, 0, x_1197);
if (lean_is_scalar(x_1188)) {
 x_1199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1199 = x_1188;
}
lean_ctor_set(x_1199, 0, x_1198);
lean_ctor_set(x_1199, 1, x_1190);
return x_1199;
}
else
{
size_t x_1200; size_t x_1201; lean_object* x_1202; 
lean_dec(x_1188);
x_1200 = 0;
x_1201 = lean_usize_of_nat(x_1191);
lean_dec(x_1191);
lean_inc(x_1186);
x_1202 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1186, x_1, x_1200, x_1201, x_8, x_9, x_10, x_11, x_1190);
if (lean_obj_tag(x_1202) == 0)
{
lean_object* x_1203; uint8_t x_1204; 
x_1203 = lean_ctor_get(x_1202, 0);
lean_inc(x_1203);
x_1204 = lean_unbox(x_1203);
lean_dec(x_1203);
if (x_1204 == 0)
{
uint8_t x_1205; 
lean_dec(x_3);
x_1205 = !lean_is_exclusive(x_1202);
if (x_1205 == 0)
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
x_1206 = lean_ctor_get(x_1202, 0);
lean_dec(x_1206);
if (lean_is_scalar(x_1183)) {
 x_1207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1207 = x_1183;
}
lean_ctor_set(x_1207, 0, x_1186);
lean_ctor_set(x_1207, 1, x_1169);
if (lean_is_scalar(x_1170)) {
 x_1208 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1208 = x_1170;
}
lean_ctor_set(x_1208, 0, x_1207);
lean_ctor_set(x_1202, 0, x_1208);
return x_1202;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1209 = lean_ctor_get(x_1202, 1);
lean_inc(x_1209);
lean_dec(x_1202);
if (lean_is_scalar(x_1183)) {
 x_1210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1210 = x_1183;
}
lean_ctor_set(x_1210, 0, x_1186);
lean_ctor_set(x_1210, 1, x_1169);
if (lean_is_scalar(x_1170)) {
 x_1211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1211 = x_1170;
}
lean_ctor_set(x_1211, 0, x_1210);
x_1212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1212, 0, x_1211);
lean_ctor_set(x_1212, 1, x_1209);
return x_1212;
}
}
else
{
uint8_t x_1213; 
lean_dec(x_1186);
lean_dec(x_1183);
lean_dec(x_1170);
lean_dec(x_1169);
x_1213 = !lean_is_exclusive(x_1202);
if (x_1213 == 0)
{
lean_object* x_1214; 
x_1214 = lean_ctor_get(x_1202, 0);
lean_dec(x_1214);
lean_ctor_set(x_1202, 0, x_3);
return x_1202;
}
else
{
lean_object* x_1215; lean_object* x_1216; 
x_1215 = lean_ctor_get(x_1202, 1);
lean_inc(x_1215);
lean_dec(x_1202);
x_1216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1216, 0, x_3);
lean_ctor_set(x_1216, 1, x_1215);
return x_1216;
}
}
}
else
{
uint8_t x_1217; 
lean_dec(x_1186);
lean_dec(x_1183);
lean_dec(x_1170);
lean_dec(x_1169);
x_1217 = !lean_is_exclusive(x_1202);
if (x_1217 == 0)
{
lean_object* x_1218; 
x_1218 = lean_ctor_get(x_1202, 0);
lean_dec(x_1218);
lean_ctor_set_tag(x_1202, 0);
lean_ctor_set(x_1202, 0, x_3);
return x_1202;
}
else
{
lean_object* x_1219; lean_object* x_1220; 
x_1219 = lean_ctor_get(x_1202, 1);
lean_inc(x_1219);
lean_dec(x_1202);
x_1220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1220, 0, x_3);
lean_ctor_set(x_1220, 1, x_1219);
return x_1220;
}
}
}
}
}
}
else
{
uint8_t x_1302; 
lean_dec(x_1170);
lean_dec(x_1169);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_1302 = !lean_is_exclusive(x_1179);
if (x_1302 == 0)
{
return x_1179;
}
else
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; 
x_1303 = lean_ctor_get(x_1179, 0);
x_1304 = lean_ctor_get(x_1179, 1);
lean_inc(x_1304);
lean_inc(x_1303);
lean_dec(x_1179);
x_1305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1305, 0, x_1303);
lean_ctor_set(x_1305, 1, x_1304);
return x_1305;
}
}
}
}
}
}
case 10:
{
lean_object* x_1306; 
lean_dec(x_7);
lean_dec(x_6);
x_1306 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1307, 0, x_3);
lean_ctor_set(x_1307, 1, x_12);
return x_1307;
}
else
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; 
x_1308 = lean_ctor_get(x_1306, 0);
lean_inc(x_1308);
lean_dec(x_1306);
x_1309 = lean_unsigned_to_nat(0u);
x_1310 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_1309);
if (lean_obj_tag(x_1310) == 0)
{
lean_object* x_1311; 
lean_dec(x_1308);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1311, 0, x_3);
lean_ctor_set(x_1311, 1, x_12);
return x_1311;
}
else
{
lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; uint8_t x_1316; 
x_1312 = lean_ctor_get(x_1310, 0);
lean_inc(x_1312);
if (lean_is_exclusive(x_1310)) {
 lean_ctor_release(x_1310, 0);
 x_1313 = x_1310;
} else {
 lean_dec_ref(x_1310);
 x_1313 = lean_box(0);
}
x_1314 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1308, x_8, x_9, x_10, x_11, x_12);
x_1315 = lean_ctor_get(x_1314, 0);
lean_inc(x_1315);
x_1316 = lean_unbox(x_1315);
lean_dec(x_1315);
if (x_1316 == 0)
{
uint8_t x_1317; 
lean_dec(x_1313);
lean_dec(x_1312);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1317 = !lean_is_exclusive(x_1314);
if (x_1317 == 0)
{
lean_object* x_1318; 
x_1318 = lean_ctor_get(x_1314, 0);
lean_dec(x_1318);
lean_ctor_set(x_1314, 0, x_3);
return x_1314;
}
else
{
lean_object* x_1319; lean_object* x_1320; 
x_1319 = lean_ctor_get(x_1314, 1);
lean_inc(x_1319);
lean_dec(x_1314);
x_1320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1320, 0, x_3);
lean_ctor_set(x_1320, 1, x_1319);
return x_1320;
}
}
else
{
lean_object* x_1321; lean_object* x_1322; 
x_1321 = lean_ctor_get(x_1314, 1);
lean_inc(x_1321);
lean_dec(x_1314);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1322 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_1312, x_8, x_9, x_10, x_11, x_1321);
if (lean_obj_tag(x_1322) == 0)
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1333; lean_object* x_1365; 
x_1323 = lean_ctor_get(x_1322, 0);
lean_inc(x_1323);
x_1324 = lean_ctor_get(x_1322, 1);
lean_inc(x_1324);
lean_dec(x_1322);
x_1325 = lean_ctor_get(x_1323, 1);
lean_inc(x_1325);
if (lean_is_exclusive(x_1323)) {
 lean_ctor_release(x_1323, 0);
 lean_ctor_release(x_1323, 1);
 x_1326 = x_1323;
} else {
 lean_dec_ref(x_1323);
 x_1326 = lean_box(0);
}
x_1327 = lean_box(0);
lean_inc(x_8);
x_1328 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1325, x_1327, x_8, x_9, x_10, x_11, x_1324);
x_1329 = lean_ctor_get(x_1328, 0);
lean_inc(x_1329);
x_1330 = lean_ctor_get(x_1328, 1);
lean_inc(x_1330);
if (lean_is_exclusive(x_1328)) {
 lean_ctor_release(x_1328, 0);
 lean_ctor_release(x_1328, 1);
 x_1331 = x_1328;
} else {
 lean_dec_ref(x_1328);
 x_1331 = lean_box(0);
}
x_1332 = l_Lean_Expr_mvarId_x21(x_1329);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1365 = l_Lean_Meta_ppGoal(x_1332, x_8, x_9, x_10, x_11, x_1330);
if (lean_obj_tag(x_1365) == 0)
{
lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; uint8_t x_1426; 
x_1366 = lean_ctor_get(x_1365, 0);
lean_inc(x_1366);
x_1367 = lean_ctor_get(x_1365, 1);
lean_inc(x_1367);
lean_dec(x_1365);
x_1423 = lean_st_ref_get(x_11, x_1367);
x_1424 = lean_ctor_get(x_1423, 0);
lean_inc(x_1424);
x_1425 = lean_ctor_get(x_1424, 3);
lean_inc(x_1425);
lean_dec(x_1424);
x_1426 = lean_ctor_get_uint8(x_1425, sizeof(void*)*1);
lean_dec(x_1425);
if (x_1426 == 0)
{
lean_object* x_1427; 
lean_dec(x_1366);
x_1427 = lean_ctor_get(x_1423, 1);
lean_inc(x_1427);
lean_dec(x_1423);
x_1368 = x_1427;
goto block_1422;
}
else
{
lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; uint8_t x_1432; 
x_1428 = lean_ctor_get(x_1423, 1);
lean_inc(x_1428);
lean_dec(x_1423);
x_1429 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1430 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1429, x_8, x_9, x_10, x_11, x_1428);
x_1431 = lean_ctor_get(x_1430, 0);
lean_inc(x_1431);
x_1432 = lean_unbox(x_1431);
lean_dec(x_1431);
if (x_1432 == 0)
{
lean_object* x_1433; 
lean_dec(x_1366);
x_1433 = lean_ctor_get(x_1430, 1);
lean_inc(x_1433);
lean_dec(x_1430);
x_1368 = x_1433;
goto block_1422;
}
else
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; 
x_1434 = lean_ctor_get(x_1430, 1);
lean_inc(x_1434);
lean_dec(x_1430);
x_1435 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1435, 0, x_1366);
x_1436 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_1437 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1437, 0, x_1436);
lean_ctor_set(x_1437, 1, x_1435);
x_1438 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1438, 0, x_1437);
lean_ctor_set(x_1438, 1, x_1436);
x_1439 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1429, x_1438, x_8, x_9, x_10, x_11, x_1434);
x_1440 = lean_ctor_get(x_1439, 1);
lean_inc(x_1440);
lean_dec(x_1439);
x_1368 = x_1440;
goto block_1422;
}
}
block_1422:
{
lean_object* x_1369; lean_object* x_1370; 
x_1369 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1370 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1332, x_1369, x_8, x_9, x_10, x_11, x_1368);
if (lean_obj_tag(x_1370) == 0)
{
lean_object* x_1371; uint8_t x_1372; 
x_1371 = lean_ctor_get(x_1370, 0);
lean_inc(x_1371);
x_1372 = lean_unbox(x_1371);
lean_dec(x_1371);
if (x_1372 == 0)
{
lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; uint8_t x_1377; 
lean_dec(x_1331);
lean_dec(x_1329);
lean_dec(x_1326);
lean_dec(x_1313);
lean_dec(x_1312);
x_1373 = lean_ctor_get(x_1370, 1);
lean_inc(x_1373);
lean_dec(x_1370);
x_1374 = lean_st_ref_get(x_11, x_1373);
x_1375 = lean_ctor_get(x_1374, 0);
lean_inc(x_1375);
x_1376 = lean_ctor_get(x_1375, 3);
lean_inc(x_1376);
lean_dec(x_1375);
x_1377 = lean_ctor_get_uint8(x_1376, sizeof(void*)*1);
lean_dec(x_1376);
if (x_1377 == 0)
{
uint8_t x_1378; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1378 = !lean_is_exclusive(x_1374);
if (x_1378 == 0)
{
lean_object* x_1379; 
x_1379 = lean_ctor_get(x_1374, 0);
lean_dec(x_1379);
lean_ctor_set(x_1374, 0, x_3);
return x_1374;
}
else
{
lean_object* x_1380; lean_object* x_1381; 
x_1380 = lean_ctor_get(x_1374, 1);
lean_inc(x_1380);
lean_dec(x_1374);
x_1381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1381, 0, x_3);
lean_ctor_set(x_1381, 1, x_1380);
return x_1381;
}
}
else
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; uint8_t x_1386; 
x_1382 = lean_ctor_get(x_1374, 1);
lean_inc(x_1382);
lean_dec(x_1374);
x_1383 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1384 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1383, x_8, x_9, x_10, x_11, x_1382);
x_1385 = lean_ctor_get(x_1384, 0);
lean_inc(x_1385);
x_1386 = lean_unbox(x_1385);
lean_dec(x_1385);
if (x_1386 == 0)
{
uint8_t x_1387; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1387 = !lean_is_exclusive(x_1384);
if (x_1387 == 0)
{
lean_object* x_1388; 
x_1388 = lean_ctor_get(x_1384, 0);
lean_dec(x_1388);
lean_ctor_set(x_1384, 0, x_3);
return x_1384;
}
else
{
lean_object* x_1389; lean_object* x_1390; 
x_1389 = lean_ctor_get(x_1384, 1);
lean_inc(x_1389);
lean_dec(x_1384);
x_1390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1390, 0, x_3);
lean_ctor_set(x_1390, 1, x_1389);
return x_1390;
}
}
else
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; uint8_t x_1394; 
x_1391 = lean_ctor_get(x_1384, 1);
lean_inc(x_1391);
lean_dec(x_1384);
x_1392 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_1393 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1383, x_1392, x_8, x_9, x_10, x_11, x_1391);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1394 = !lean_is_exclusive(x_1393);
if (x_1394 == 0)
{
lean_object* x_1395; 
x_1395 = lean_ctor_get(x_1393, 0);
lean_dec(x_1395);
lean_ctor_set(x_1393, 0, x_3);
return x_1393;
}
else
{
lean_object* x_1396; lean_object* x_1397; 
x_1396 = lean_ctor_get(x_1393, 1);
lean_inc(x_1396);
lean_dec(x_1393);
x_1397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1397, 0, x_3);
lean_ctor_set(x_1397, 1, x_1396);
return x_1397;
}
}
}
}
else
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; uint8_t x_1402; 
x_1398 = lean_ctor_get(x_1370, 1);
lean_inc(x_1398);
lean_dec(x_1370);
x_1399 = lean_st_ref_get(x_11, x_1398);
x_1400 = lean_ctor_get(x_1399, 0);
lean_inc(x_1400);
x_1401 = lean_ctor_get(x_1400, 3);
lean_inc(x_1401);
lean_dec(x_1400);
x_1402 = lean_ctor_get_uint8(x_1401, sizeof(void*)*1);
lean_dec(x_1401);
if (x_1402 == 0)
{
lean_object* x_1403; 
x_1403 = lean_ctor_get(x_1399, 1);
lean_inc(x_1403);
lean_dec(x_1399);
x_1333 = x_1403;
goto block_1364;
}
else
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; uint8_t x_1408; 
x_1404 = lean_ctor_get(x_1399, 1);
lean_inc(x_1404);
lean_dec(x_1399);
x_1405 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1406 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1405, x_8, x_9, x_10, x_11, x_1404);
x_1407 = lean_ctor_get(x_1406, 0);
lean_inc(x_1407);
x_1408 = lean_unbox(x_1407);
lean_dec(x_1407);
if (x_1408 == 0)
{
lean_object* x_1409; 
x_1409 = lean_ctor_get(x_1406, 1);
lean_inc(x_1409);
lean_dec(x_1406);
x_1333 = x_1409;
goto block_1364;
}
else
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; 
x_1410 = lean_ctor_get(x_1406, 1);
lean_inc(x_1410);
lean_dec(x_1406);
lean_inc(x_1329);
x_1411 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1411, 0, x_1329);
x_1412 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1413 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1413, 0, x_1412);
lean_ctor_set(x_1413, 1, x_1411);
x_1414 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_1415 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1415, 0, x_1413);
lean_ctor_set(x_1415, 1, x_1414);
x_1416 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1405, x_1415, x_8, x_9, x_10, x_11, x_1410);
x_1417 = lean_ctor_get(x_1416, 1);
lean_inc(x_1417);
lean_dec(x_1416);
x_1333 = x_1417;
goto block_1364;
}
}
}
}
else
{
uint8_t x_1418; 
lean_dec(x_1331);
lean_dec(x_1329);
lean_dec(x_1326);
lean_dec(x_1313);
lean_dec(x_1312);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1418 = !lean_is_exclusive(x_1370);
if (x_1418 == 0)
{
lean_object* x_1419; 
x_1419 = lean_ctor_get(x_1370, 0);
lean_dec(x_1419);
lean_ctor_set_tag(x_1370, 0);
lean_ctor_set(x_1370, 0, x_3);
return x_1370;
}
else
{
lean_object* x_1420; lean_object* x_1421; 
x_1420 = lean_ctor_get(x_1370, 1);
lean_inc(x_1420);
lean_dec(x_1370);
x_1421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1421, 0, x_3);
lean_ctor_set(x_1421, 1, x_1420);
return x_1421;
}
}
}
}
else
{
uint8_t x_1441; 
lean_dec(x_1332);
lean_dec(x_1331);
lean_dec(x_1329);
lean_dec(x_1326);
lean_dec(x_1313);
lean_dec(x_1312);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1441 = !lean_is_exclusive(x_1365);
if (x_1441 == 0)
{
lean_object* x_1442; 
x_1442 = lean_ctor_get(x_1365, 0);
lean_dec(x_1442);
lean_ctor_set_tag(x_1365, 0);
lean_ctor_set(x_1365, 0, x_3);
return x_1365;
}
else
{
lean_object* x_1443; lean_object* x_1444; 
x_1443 = lean_ctor_get(x_1365, 1);
lean_inc(x_1443);
lean_dec(x_1365);
x_1444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1444, 0, x_3);
lean_ctor_set(x_1444, 1, x_1443);
return x_1444;
}
}
block_1364:
{
lean_object* x_1334; uint8_t x_1335; 
x_1334 = lean_array_get_size(x_1);
x_1335 = lean_nat_dec_lt(x_1309, x_1334);
if (x_1335 == 0)
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
lean_dec(x_1334);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1326)) {
 x_1336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1336 = x_1326;
}
lean_ctor_set(x_1336, 0, x_1329);
lean_ctor_set(x_1336, 1, x_1312);
if (lean_is_scalar(x_1313)) {
 x_1337 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1337 = x_1313;
}
lean_ctor_set(x_1337, 0, x_1336);
if (lean_is_scalar(x_1331)) {
 x_1338 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1338 = x_1331;
}
lean_ctor_set(x_1338, 0, x_1337);
lean_ctor_set(x_1338, 1, x_1333);
return x_1338;
}
else
{
uint8_t x_1339; 
x_1339 = lean_nat_dec_le(x_1334, x_1334);
if (x_1339 == 0)
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; 
lean_dec(x_1334);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1326)) {
 x_1340 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1340 = x_1326;
}
lean_ctor_set(x_1340, 0, x_1329);
lean_ctor_set(x_1340, 1, x_1312);
if (lean_is_scalar(x_1313)) {
 x_1341 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1341 = x_1313;
}
lean_ctor_set(x_1341, 0, x_1340);
if (lean_is_scalar(x_1331)) {
 x_1342 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1342 = x_1331;
}
lean_ctor_set(x_1342, 0, x_1341);
lean_ctor_set(x_1342, 1, x_1333);
return x_1342;
}
else
{
size_t x_1343; size_t x_1344; lean_object* x_1345; 
lean_dec(x_1331);
x_1343 = 0;
x_1344 = lean_usize_of_nat(x_1334);
lean_dec(x_1334);
lean_inc(x_1329);
x_1345 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1329, x_1, x_1343, x_1344, x_8, x_9, x_10, x_11, x_1333);
if (lean_obj_tag(x_1345) == 0)
{
lean_object* x_1346; uint8_t x_1347; 
x_1346 = lean_ctor_get(x_1345, 0);
lean_inc(x_1346);
x_1347 = lean_unbox(x_1346);
lean_dec(x_1346);
if (x_1347 == 0)
{
uint8_t x_1348; 
lean_dec(x_3);
x_1348 = !lean_is_exclusive(x_1345);
if (x_1348 == 0)
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
x_1349 = lean_ctor_get(x_1345, 0);
lean_dec(x_1349);
if (lean_is_scalar(x_1326)) {
 x_1350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1350 = x_1326;
}
lean_ctor_set(x_1350, 0, x_1329);
lean_ctor_set(x_1350, 1, x_1312);
if (lean_is_scalar(x_1313)) {
 x_1351 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1351 = x_1313;
}
lean_ctor_set(x_1351, 0, x_1350);
lean_ctor_set(x_1345, 0, x_1351);
return x_1345;
}
else
{
lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1352 = lean_ctor_get(x_1345, 1);
lean_inc(x_1352);
lean_dec(x_1345);
if (lean_is_scalar(x_1326)) {
 x_1353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1353 = x_1326;
}
lean_ctor_set(x_1353, 0, x_1329);
lean_ctor_set(x_1353, 1, x_1312);
if (lean_is_scalar(x_1313)) {
 x_1354 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1354 = x_1313;
}
lean_ctor_set(x_1354, 0, x_1353);
x_1355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1355, 0, x_1354);
lean_ctor_set(x_1355, 1, x_1352);
return x_1355;
}
}
else
{
uint8_t x_1356; 
lean_dec(x_1329);
lean_dec(x_1326);
lean_dec(x_1313);
lean_dec(x_1312);
x_1356 = !lean_is_exclusive(x_1345);
if (x_1356 == 0)
{
lean_object* x_1357; 
x_1357 = lean_ctor_get(x_1345, 0);
lean_dec(x_1357);
lean_ctor_set(x_1345, 0, x_3);
return x_1345;
}
else
{
lean_object* x_1358; lean_object* x_1359; 
x_1358 = lean_ctor_get(x_1345, 1);
lean_inc(x_1358);
lean_dec(x_1345);
x_1359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1359, 0, x_3);
lean_ctor_set(x_1359, 1, x_1358);
return x_1359;
}
}
}
else
{
uint8_t x_1360; 
lean_dec(x_1329);
lean_dec(x_1326);
lean_dec(x_1313);
lean_dec(x_1312);
x_1360 = !lean_is_exclusive(x_1345);
if (x_1360 == 0)
{
lean_object* x_1361; 
x_1361 = lean_ctor_get(x_1345, 0);
lean_dec(x_1361);
lean_ctor_set_tag(x_1345, 0);
lean_ctor_set(x_1345, 0, x_3);
return x_1345;
}
else
{
lean_object* x_1362; lean_object* x_1363; 
x_1362 = lean_ctor_get(x_1345, 1);
lean_inc(x_1362);
lean_dec(x_1345);
x_1363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1363, 0, x_3);
lean_ctor_set(x_1363, 1, x_1362);
return x_1363;
}
}
}
}
}
}
else
{
uint8_t x_1445; 
lean_dec(x_1313);
lean_dec(x_1312);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_1445 = !lean_is_exclusive(x_1322);
if (x_1445 == 0)
{
return x_1322;
}
else
{
lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; 
x_1446 = lean_ctor_get(x_1322, 0);
x_1447 = lean_ctor_get(x_1322, 1);
lean_inc(x_1447);
lean_inc(x_1446);
lean_dec(x_1322);
x_1448 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1448, 0, x_1446);
lean_ctor_set(x_1448, 1, x_1447);
return x_1448;
}
}
}
}
}
}
default: 
{
lean_object* x_1449; 
lean_dec(x_7);
lean_dec(x_6);
x_1449 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_1449) == 0)
{
lean_object* x_1450; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1450, 0, x_3);
lean_ctor_set(x_1450, 1, x_12);
return x_1450;
}
else
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
x_1451 = lean_ctor_get(x_1449, 0);
lean_inc(x_1451);
lean_dec(x_1449);
x_1452 = lean_unsigned_to_nat(0u);
x_1453 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_1452);
if (lean_obj_tag(x_1453) == 0)
{
lean_object* x_1454; 
lean_dec(x_1451);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1454, 0, x_3);
lean_ctor_set(x_1454, 1, x_12);
return x_1454;
}
else
{
lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; uint8_t x_1459; 
x_1455 = lean_ctor_get(x_1453, 0);
lean_inc(x_1455);
if (lean_is_exclusive(x_1453)) {
 lean_ctor_release(x_1453, 0);
 x_1456 = x_1453;
} else {
 lean_dec_ref(x_1453);
 x_1456 = lean_box(0);
}
x_1457 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1451, x_8, x_9, x_10, x_11, x_12);
x_1458 = lean_ctor_get(x_1457, 0);
lean_inc(x_1458);
x_1459 = lean_unbox(x_1458);
lean_dec(x_1458);
if (x_1459 == 0)
{
uint8_t x_1460; 
lean_dec(x_1456);
lean_dec(x_1455);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1460 = !lean_is_exclusive(x_1457);
if (x_1460 == 0)
{
lean_object* x_1461; 
x_1461 = lean_ctor_get(x_1457, 0);
lean_dec(x_1461);
lean_ctor_set(x_1457, 0, x_3);
return x_1457;
}
else
{
lean_object* x_1462; lean_object* x_1463; 
x_1462 = lean_ctor_get(x_1457, 1);
lean_inc(x_1462);
lean_dec(x_1457);
x_1463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1463, 0, x_3);
lean_ctor_set(x_1463, 1, x_1462);
return x_1463;
}
}
else
{
lean_object* x_1464; lean_object* x_1465; 
x_1464 = lean_ctor_get(x_1457, 1);
lean_inc(x_1464);
lean_dec(x_1457);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1465 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_1455, x_8, x_9, x_10, x_11, x_1464);
if (lean_obj_tag(x_1465) == 0)
{
lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1508; 
x_1466 = lean_ctor_get(x_1465, 0);
lean_inc(x_1466);
x_1467 = lean_ctor_get(x_1465, 1);
lean_inc(x_1467);
lean_dec(x_1465);
x_1468 = lean_ctor_get(x_1466, 1);
lean_inc(x_1468);
if (lean_is_exclusive(x_1466)) {
 lean_ctor_release(x_1466, 0);
 lean_ctor_release(x_1466, 1);
 x_1469 = x_1466;
} else {
 lean_dec_ref(x_1466);
 x_1469 = lean_box(0);
}
x_1470 = lean_box(0);
lean_inc(x_8);
x_1471 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1468, x_1470, x_8, x_9, x_10, x_11, x_1467);
x_1472 = lean_ctor_get(x_1471, 0);
lean_inc(x_1472);
x_1473 = lean_ctor_get(x_1471, 1);
lean_inc(x_1473);
if (lean_is_exclusive(x_1471)) {
 lean_ctor_release(x_1471, 0);
 lean_ctor_release(x_1471, 1);
 x_1474 = x_1471;
} else {
 lean_dec_ref(x_1471);
 x_1474 = lean_box(0);
}
x_1475 = l_Lean_Expr_mvarId_x21(x_1472);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1508 = l_Lean_Meta_ppGoal(x_1475, x_8, x_9, x_10, x_11, x_1473);
if (lean_obj_tag(x_1508) == 0)
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; uint8_t x_1569; 
x_1509 = lean_ctor_get(x_1508, 0);
lean_inc(x_1509);
x_1510 = lean_ctor_get(x_1508, 1);
lean_inc(x_1510);
lean_dec(x_1508);
x_1566 = lean_st_ref_get(x_11, x_1510);
x_1567 = lean_ctor_get(x_1566, 0);
lean_inc(x_1567);
x_1568 = lean_ctor_get(x_1567, 3);
lean_inc(x_1568);
lean_dec(x_1567);
x_1569 = lean_ctor_get_uint8(x_1568, sizeof(void*)*1);
lean_dec(x_1568);
if (x_1569 == 0)
{
lean_object* x_1570; 
lean_dec(x_1509);
x_1570 = lean_ctor_get(x_1566, 1);
lean_inc(x_1570);
lean_dec(x_1566);
x_1511 = x_1570;
goto block_1565;
}
else
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; uint8_t x_1575; 
x_1571 = lean_ctor_get(x_1566, 1);
lean_inc(x_1571);
lean_dec(x_1566);
x_1572 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1573 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1572, x_8, x_9, x_10, x_11, x_1571);
x_1574 = lean_ctor_get(x_1573, 0);
lean_inc(x_1574);
x_1575 = lean_unbox(x_1574);
lean_dec(x_1574);
if (x_1575 == 0)
{
lean_object* x_1576; 
lean_dec(x_1509);
x_1576 = lean_ctor_get(x_1573, 1);
lean_inc(x_1576);
lean_dec(x_1573);
x_1511 = x_1576;
goto block_1565;
}
else
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; 
x_1577 = lean_ctor_get(x_1573, 1);
lean_inc(x_1577);
lean_dec(x_1573);
x_1578 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1578, 0, x_1509);
x_1579 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_1580 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1580, 0, x_1579);
lean_ctor_set(x_1580, 1, x_1578);
x_1581 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1581, 0, x_1580);
lean_ctor_set(x_1581, 1, x_1579);
x_1582 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1572, x_1581, x_8, x_9, x_10, x_11, x_1577);
x_1583 = lean_ctor_get(x_1582, 1);
lean_inc(x_1583);
lean_dec(x_1582);
x_1511 = x_1583;
goto block_1565;
}
}
block_1565:
{
lean_object* x_1512; lean_object* x_1513; 
x_1512 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1513 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1475, x_1512, x_8, x_9, x_10, x_11, x_1511);
if (lean_obj_tag(x_1513) == 0)
{
lean_object* x_1514; uint8_t x_1515; 
x_1514 = lean_ctor_get(x_1513, 0);
lean_inc(x_1514);
x_1515 = lean_unbox(x_1514);
lean_dec(x_1514);
if (x_1515 == 0)
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; uint8_t x_1520; 
lean_dec(x_1474);
lean_dec(x_1472);
lean_dec(x_1469);
lean_dec(x_1456);
lean_dec(x_1455);
x_1516 = lean_ctor_get(x_1513, 1);
lean_inc(x_1516);
lean_dec(x_1513);
x_1517 = lean_st_ref_get(x_11, x_1516);
x_1518 = lean_ctor_get(x_1517, 0);
lean_inc(x_1518);
x_1519 = lean_ctor_get(x_1518, 3);
lean_inc(x_1519);
lean_dec(x_1518);
x_1520 = lean_ctor_get_uint8(x_1519, sizeof(void*)*1);
lean_dec(x_1519);
if (x_1520 == 0)
{
uint8_t x_1521; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1521 = !lean_is_exclusive(x_1517);
if (x_1521 == 0)
{
lean_object* x_1522; 
x_1522 = lean_ctor_get(x_1517, 0);
lean_dec(x_1522);
lean_ctor_set(x_1517, 0, x_3);
return x_1517;
}
else
{
lean_object* x_1523; lean_object* x_1524; 
x_1523 = lean_ctor_get(x_1517, 1);
lean_inc(x_1523);
lean_dec(x_1517);
x_1524 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1524, 0, x_3);
lean_ctor_set(x_1524, 1, x_1523);
return x_1524;
}
}
else
{
lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; uint8_t x_1529; 
x_1525 = lean_ctor_get(x_1517, 1);
lean_inc(x_1525);
lean_dec(x_1517);
x_1526 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1527 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1526, x_8, x_9, x_10, x_11, x_1525);
x_1528 = lean_ctor_get(x_1527, 0);
lean_inc(x_1528);
x_1529 = lean_unbox(x_1528);
lean_dec(x_1528);
if (x_1529 == 0)
{
uint8_t x_1530; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1530 = !lean_is_exclusive(x_1527);
if (x_1530 == 0)
{
lean_object* x_1531; 
x_1531 = lean_ctor_get(x_1527, 0);
lean_dec(x_1531);
lean_ctor_set(x_1527, 0, x_3);
return x_1527;
}
else
{
lean_object* x_1532; lean_object* x_1533; 
x_1532 = lean_ctor_get(x_1527, 1);
lean_inc(x_1532);
lean_dec(x_1527);
x_1533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1533, 0, x_3);
lean_ctor_set(x_1533, 1, x_1532);
return x_1533;
}
}
else
{
lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; uint8_t x_1537; 
x_1534 = lean_ctor_get(x_1527, 1);
lean_inc(x_1534);
lean_dec(x_1527);
x_1535 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_1536 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1526, x_1535, x_8, x_9, x_10, x_11, x_1534);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1537 = !lean_is_exclusive(x_1536);
if (x_1537 == 0)
{
lean_object* x_1538; 
x_1538 = lean_ctor_get(x_1536, 0);
lean_dec(x_1538);
lean_ctor_set(x_1536, 0, x_3);
return x_1536;
}
else
{
lean_object* x_1539; lean_object* x_1540; 
x_1539 = lean_ctor_get(x_1536, 1);
lean_inc(x_1539);
lean_dec(x_1536);
x_1540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1540, 0, x_3);
lean_ctor_set(x_1540, 1, x_1539);
return x_1540;
}
}
}
}
else
{
lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; uint8_t x_1545; 
x_1541 = lean_ctor_get(x_1513, 1);
lean_inc(x_1541);
lean_dec(x_1513);
x_1542 = lean_st_ref_get(x_11, x_1541);
x_1543 = lean_ctor_get(x_1542, 0);
lean_inc(x_1543);
x_1544 = lean_ctor_get(x_1543, 3);
lean_inc(x_1544);
lean_dec(x_1543);
x_1545 = lean_ctor_get_uint8(x_1544, sizeof(void*)*1);
lean_dec(x_1544);
if (x_1545 == 0)
{
lean_object* x_1546; 
x_1546 = lean_ctor_get(x_1542, 1);
lean_inc(x_1546);
lean_dec(x_1542);
x_1476 = x_1546;
goto block_1507;
}
else
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; uint8_t x_1551; 
x_1547 = lean_ctor_get(x_1542, 1);
lean_inc(x_1547);
lean_dec(x_1542);
x_1548 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_1549 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1548, x_8, x_9, x_10, x_11, x_1547);
x_1550 = lean_ctor_get(x_1549, 0);
lean_inc(x_1550);
x_1551 = lean_unbox(x_1550);
lean_dec(x_1550);
if (x_1551 == 0)
{
lean_object* x_1552; 
x_1552 = lean_ctor_get(x_1549, 1);
lean_inc(x_1552);
lean_dec(x_1549);
x_1476 = x_1552;
goto block_1507;
}
else
{
lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; 
x_1553 = lean_ctor_get(x_1549, 1);
lean_inc(x_1553);
lean_dec(x_1549);
lean_inc(x_1472);
x_1554 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1554, 0, x_1472);
x_1555 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1556 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1556, 0, x_1555);
lean_ctor_set(x_1556, 1, x_1554);
x_1557 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_1558 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1558, 0, x_1556);
lean_ctor_set(x_1558, 1, x_1557);
x_1559 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1548, x_1558, x_8, x_9, x_10, x_11, x_1553);
x_1560 = lean_ctor_get(x_1559, 1);
lean_inc(x_1560);
lean_dec(x_1559);
x_1476 = x_1560;
goto block_1507;
}
}
}
}
else
{
uint8_t x_1561; 
lean_dec(x_1474);
lean_dec(x_1472);
lean_dec(x_1469);
lean_dec(x_1456);
lean_dec(x_1455);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1561 = !lean_is_exclusive(x_1513);
if (x_1561 == 0)
{
lean_object* x_1562; 
x_1562 = lean_ctor_get(x_1513, 0);
lean_dec(x_1562);
lean_ctor_set_tag(x_1513, 0);
lean_ctor_set(x_1513, 0, x_3);
return x_1513;
}
else
{
lean_object* x_1563; lean_object* x_1564; 
x_1563 = lean_ctor_get(x_1513, 1);
lean_inc(x_1563);
lean_dec(x_1513);
x_1564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1564, 0, x_3);
lean_ctor_set(x_1564, 1, x_1563);
return x_1564;
}
}
}
}
else
{
uint8_t x_1584; 
lean_dec(x_1475);
lean_dec(x_1474);
lean_dec(x_1472);
lean_dec(x_1469);
lean_dec(x_1456);
lean_dec(x_1455);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1584 = !lean_is_exclusive(x_1508);
if (x_1584 == 0)
{
lean_object* x_1585; 
x_1585 = lean_ctor_get(x_1508, 0);
lean_dec(x_1585);
lean_ctor_set_tag(x_1508, 0);
lean_ctor_set(x_1508, 0, x_3);
return x_1508;
}
else
{
lean_object* x_1586; lean_object* x_1587; 
x_1586 = lean_ctor_get(x_1508, 1);
lean_inc(x_1586);
lean_dec(x_1508);
x_1587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1587, 0, x_3);
lean_ctor_set(x_1587, 1, x_1586);
return x_1587;
}
}
block_1507:
{
lean_object* x_1477; uint8_t x_1478; 
x_1477 = lean_array_get_size(x_1);
x_1478 = lean_nat_dec_lt(x_1452, x_1477);
if (x_1478 == 0)
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; 
lean_dec(x_1477);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1469)) {
 x_1479 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1479 = x_1469;
}
lean_ctor_set(x_1479, 0, x_1472);
lean_ctor_set(x_1479, 1, x_1455);
if (lean_is_scalar(x_1456)) {
 x_1480 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1480 = x_1456;
}
lean_ctor_set(x_1480, 0, x_1479);
if (lean_is_scalar(x_1474)) {
 x_1481 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1481 = x_1474;
}
lean_ctor_set(x_1481, 0, x_1480);
lean_ctor_set(x_1481, 1, x_1476);
return x_1481;
}
else
{
uint8_t x_1482; 
x_1482 = lean_nat_dec_le(x_1477, x_1477);
if (x_1482 == 0)
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; 
lean_dec(x_1477);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1469)) {
 x_1483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1483 = x_1469;
}
lean_ctor_set(x_1483, 0, x_1472);
lean_ctor_set(x_1483, 1, x_1455);
if (lean_is_scalar(x_1456)) {
 x_1484 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1484 = x_1456;
}
lean_ctor_set(x_1484, 0, x_1483);
if (lean_is_scalar(x_1474)) {
 x_1485 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1485 = x_1474;
}
lean_ctor_set(x_1485, 0, x_1484);
lean_ctor_set(x_1485, 1, x_1476);
return x_1485;
}
else
{
size_t x_1486; size_t x_1487; lean_object* x_1488; 
lean_dec(x_1474);
x_1486 = 0;
x_1487 = lean_usize_of_nat(x_1477);
lean_dec(x_1477);
lean_inc(x_1472);
x_1488 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1472, x_1, x_1486, x_1487, x_8, x_9, x_10, x_11, x_1476);
if (lean_obj_tag(x_1488) == 0)
{
lean_object* x_1489; uint8_t x_1490; 
x_1489 = lean_ctor_get(x_1488, 0);
lean_inc(x_1489);
x_1490 = lean_unbox(x_1489);
lean_dec(x_1489);
if (x_1490 == 0)
{
uint8_t x_1491; 
lean_dec(x_3);
x_1491 = !lean_is_exclusive(x_1488);
if (x_1491 == 0)
{
lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
x_1492 = lean_ctor_get(x_1488, 0);
lean_dec(x_1492);
if (lean_is_scalar(x_1469)) {
 x_1493 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1493 = x_1469;
}
lean_ctor_set(x_1493, 0, x_1472);
lean_ctor_set(x_1493, 1, x_1455);
if (lean_is_scalar(x_1456)) {
 x_1494 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1494 = x_1456;
}
lean_ctor_set(x_1494, 0, x_1493);
lean_ctor_set(x_1488, 0, x_1494);
return x_1488;
}
else
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; 
x_1495 = lean_ctor_get(x_1488, 1);
lean_inc(x_1495);
lean_dec(x_1488);
if (lean_is_scalar(x_1469)) {
 x_1496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1496 = x_1469;
}
lean_ctor_set(x_1496, 0, x_1472);
lean_ctor_set(x_1496, 1, x_1455);
if (lean_is_scalar(x_1456)) {
 x_1497 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1497 = x_1456;
}
lean_ctor_set(x_1497, 0, x_1496);
x_1498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1498, 0, x_1497);
lean_ctor_set(x_1498, 1, x_1495);
return x_1498;
}
}
else
{
uint8_t x_1499; 
lean_dec(x_1472);
lean_dec(x_1469);
lean_dec(x_1456);
lean_dec(x_1455);
x_1499 = !lean_is_exclusive(x_1488);
if (x_1499 == 0)
{
lean_object* x_1500; 
x_1500 = lean_ctor_get(x_1488, 0);
lean_dec(x_1500);
lean_ctor_set(x_1488, 0, x_3);
return x_1488;
}
else
{
lean_object* x_1501; lean_object* x_1502; 
x_1501 = lean_ctor_get(x_1488, 1);
lean_inc(x_1501);
lean_dec(x_1488);
x_1502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1502, 0, x_3);
lean_ctor_set(x_1502, 1, x_1501);
return x_1502;
}
}
}
else
{
uint8_t x_1503; 
lean_dec(x_1472);
lean_dec(x_1469);
lean_dec(x_1456);
lean_dec(x_1455);
x_1503 = !lean_is_exclusive(x_1488);
if (x_1503 == 0)
{
lean_object* x_1504; 
x_1504 = lean_ctor_get(x_1488, 0);
lean_dec(x_1504);
lean_ctor_set_tag(x_1488, 0);
lean_ctor_set(x_1488, 0, x_3);
return x_1488;
}
else
{
lean_object* x_1505; lean_object* x_1506; 
x_1505 = lean_ctor_get(x_1488, 1);
lean_inc(x_1505);
lean_dec(x_1488);
x_1506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1506, 0, x_3);
lean_ctor_set(x_1506, 1, x_1505);
return x_1506;
}
}
}
}
}
}
else
{
uint8_t x_1588; 
lean_dec(x_1456);
lean_dec(x_1455);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_1588 = !lean_is_exclusive(x_1465);
if (x_1588 == 0)
{
return x_1465;
}
else
{
lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; 
x_1589 = lean_ctor_get(x_1465, 0);
x_1590 = lean_ctor_get(x_1465, 1);
lean_inc(x_1590);
lean_inc(x_1589);
lean_dec(x_1465);
x_1591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1591, 0, x_1589);
lean_ctor_set(x_1591, 1, x_1590);
return x_1591;
}
}
}
}
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = x_7 < x_6;
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
x_16 = lean_array_uget(x_5, x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_16);
x_17 = l_Lean_Meta_inferType(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Expr_getAppNumArgsAux(x_18, x_20);
x_22 = l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___closed__1;
lean_inc(x_21);
x_23 = lean_mk_array(x_21, x_22);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_21, x_24);
lean_dec(x_21);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3(x_1, x_2, x_3, x_16, x_18, x_23, x_25, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; size_t x_29; size_t x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 1;
x_30 = x_7 + x_29;
lean_inc(x_4);
{
size_t _tmp_6 = x_30;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_12 = x_28;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_13 = _tmp_12;
}
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_26, 0);
lean_dec(x_33);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_26, 0, x_36);
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_26, 0, x_40);
return x_26;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_ctor_get(x_27, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_43 = x_27;
} else {
 lean_dec_ref(x_27);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_26);
if (x_48 == 0)
{
return x_26;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_26, 0);
x_50 = lean_ctor_get(x_26, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_26);
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
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_17);
if (x_52 == 0)
{
return x_17;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_17, 0);
x_54 = lean_ctor_get(x_17, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_17);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_box(0);
x_9 = lean_array_get_size(x_1);
x_10 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_11 = 0;
x_12 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3;
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__4(x_1, x_2, x_8, x_12, x_1, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
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
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_ctor_set(x_13, 0, x_15);
return x_13;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_27 = x_15;
} else {
 lean_dec_ref(x_15);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_13);
if (x_30 == 0)
{
return x_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_13, 0);
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_13);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_12 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__4(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_1);
return x_16;
}
}
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_IndPredBelow_findBelowIdx(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_13 = l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(x_12, x_2, x_3, x_4, x_5, x_9);
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
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
lean_ctor_set(x_16, 0, x_14);
x_20 = lean_st_ref_set(x_5, x_16, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_16, 1);
x_28 = lean_ctor_get(x_16, 2);
x_29 = lean_ctor_get(x_16, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_30 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_30, 0, x_14);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_29);
x_31 = lean_st_ref_set(x_5, x_30, x_17);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
x_34 = lean_box(0);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to prove brecOn for ");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\n");
return x_1;
}
}
static lean_object* _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_4, 1);
x_14 = lean_nat_dec_le(x_13, x_6);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_57; 
lean_dec(x_7);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_5, x_17);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_57 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl(x_1, x_6, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_10);
x_60 = l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(x_58, x_8, x_9, x_10, x_11, x_59);
lean_dec(x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_ctor_get(x_4, 2);
x_63 = lean_nat_add(x_6, x_62);
lean_dec(x_6);
x_64 = lean_box(0);
x_5 = x_18;
x_6 = x_63;
x_7 = x_64;
x_12 = x_61;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_60, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_dec(x_60);
x_19 = x_66;
x_20 = x_67;
goto block_56;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_57, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_dec(x_57);
x_19 = x_68;
x_20 = x_69;
goto block_56;
}
block_56:
{
uint8_t x_21; lean_object* x_22; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_st_ref_get(x_11, x_20);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 3);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_ctor_get_uint8(x_47, sizeof(void*)*1);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = 0;
x_21 = x_50;
x_22 = x_49;
goto block_44;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_45, 1);
lean_inc(x_51);
lean_dec(x_45);
lean_inc(x_2);
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2, x_8, x_9, x_10, x_11, x_51);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_unbox(x_53);
lean_dec(x_53);
x_21 = x_55;
x_22 = x_54;
goto block_44;
}
block_44:
{
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_19);
x_23 = lean_ctor_get(x_4, 2);
x_24 = lean_nat_add(x_6, x_23);
lean_dec(x_6);
x_25 = lean_box(0);
x_5 = x_18;
x_6 = x_24;
x_7 = x_25;
x_12 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_27 = l_Lean_instInhabitedName;
x_28 = lean_array_get(x_27, x_3, x_6);
x_29 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__4;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Exception_toMessageData(x_19);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_37 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_inc(x_2);
x_38 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2, x_37, x_8, x_9, x_10, x_11, x_22);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_4, 2);
x_41 = lean_nat_add(x_6, x_40);
lean_dec(x_6);
x_42 = lean_box(0);
x_5 = x_18;
x_6 = x_41;
x_7 = x_42;
x_12 = x_39;
goto _start;
}
}
}
}
else
{
lean_object* x_70; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_7);
lean_ctor_set(x_70, 1, x_12);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_7);
lean_ctor_set(x_71, 1, x_12);
return x_71;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = x_2 == x_3;
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
x_16 = x_2 + x_15;
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
lean_object* l_List_map___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(lean_object* x_1) {
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
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(x_5);
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
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Not inductive predicate");
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
x_1 = lean_mk_string("Not recursive");
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
x_1 = lean_mk_string("added ");
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelow(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_7 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_st_ref_get(x_5, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 3);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*1);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_dec(x_11);
x_22 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_23 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_22, x_2, x_3, x_4, x_5, x_21);
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
x_34 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_22, x_33, x_2, x_3, x_4, x_5, x_32);
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
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_dec(x_1);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_st_ref_get(x_5, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 3);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*1);
lean_dec(x_42);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_40, 0);
lean_dec(x_45);
x_46 = lean_box(0);
lean_ctor_set(x_40, 0, x_46);
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_dec(x_40);
x_51 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_52 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_51, x_2, x_3, x_4, x_5, x_50);
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
x_63 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_51, x_62, x_2, x_3, x_4, x_5, x_61);
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
lean_inc(x_4);
x_71 = l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(x_69, x_2, x_3, x_4, x_5, x_70);
lean_dec(x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_102; lean_object* x_103; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_116 = lean_st_ref_get(x_5, x_72);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 3);
lean_inc(x_118);
lean_dec(x_117);
x_119 = lean_ctor_get_uint8(x_118, sizeof(void*)*1);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
lean_dec(x_116);
x_121 = 0;
x_102 = x_121;
x_103 = x_120;
goto block_115;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_116, 1);
lean_inc(x_122);
lean_dec(x_116);
x_123 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_124 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_123, x_2, x_3, x_4, x_5, x_122);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_unbox(x_125);
lean_dec(x_125);
x_102 = x_127;
x_103 = x_126;
goto block_115;
}
block_101:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_66, 2);
lean_inc(x_74);
x_75 = lean_array_get_size(x_74);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_lt(x_76, x_75);
if (x_77 == 0)
{
lean_dec(x_75);
x_78 = x_73;
goto block_90;
}
else
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_75, x_75);
if (x_91 == 0)
{
lean_dec(x_75);
x_78 = x_73;
goto block_90;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; lean_object* x_95; 
x_92 = 0;
x_93 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_94 = lean_box(0);
lean_inc(x_4);
x_95 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(x_74, x_92, x_93, x_94, x_2, x_3, x_4, x_5, x_73);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_78 = x_96;
goto block_90;
}
else
{
uint8_t x_97; 
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_95);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
block_90:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
x_80 = lean_array_get_size(x_79);
lean_dec(x_79);
x_81 = lean_unsigned_to_nat(1u);
lean_inc(x_80);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_81);
x_83 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_84 = lean_box(0);
x_85 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(x_66, x_83, x_74, x_82, x_80, x_76, x_84, x_2, x_3, x_4, x_5, x_78);
lean_dec(x_82);
lean_dec(x_74);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_84);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
block_115:
{
if (x_102 == 0)
{
x_73 = x_103;
goto block_101;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_104 = lean_ctor_get(x_66, 2);
lean_inc(x_104);
x_105 = lean_array_to_list(lean_box(0), x_104);
x_106 = l_List_map___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(x_105);
x_107 = l_Lean_MessageData_ofList(x_106);
lean_dec(x_106);
x_108 = l_Lean_Meta_IndPredBelow_mkBelow___closed__6;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3;
x_111 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_113 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_112, x_111, x_2, x_3, x_4, x_5, x_103);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_73 = x_114;
goto block_101;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_71);
if (x_128 == 0)
{
return x_71;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_71, 0);
x_130 = lean_ctor_get(x_71, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_71);
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
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_132 = !lean_is_exclusive(x_68);
if (x_132 == 0)
{
return x_68;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_68, 0);
x_134 = lean_ctor_get(x_68, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_68);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_136 = !lean_is_exclusive(x_65);
if (x_136 == 0)
{
return x_65;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_65, 0);
x_138 = lean_ctor_get(x_65, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_65);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_36);
if (x_140 == 0)
{
return x_36;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_36, 0);
x_142 = lean_ctor_get(x_36, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_36);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
}
lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5254_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_Constructions(lean_object*);
lean_object* initialize_Lean_Meta_Transform(lean_object*);
lean_object* initialize_Lean_Meta_Tactic(lean_object*);
lean_object* initialize_Lean_Meta_Match(lean_object*);
lean_object* initialize_Lean_Meta_Reduce(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_IndPredBelow(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Constructions(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Reduce(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4);
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__5 = _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__5();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__5);
l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth___closed__1 = _init_l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth___closed__1);
res = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth);
lean_dec_ref(res);
l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1 = _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1);
l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2 = _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__2();
l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3 = _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__3);
l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__4 = _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__4();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__4);
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
l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1 = _init_l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1);
l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__1 = _init_l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__1);
l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__2 = _init_l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___closed__2);
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
l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1___closed__1 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1___closed__1);
l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1);
l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2);
l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3);
l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4 = _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4();
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4);
l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1 = _init_l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1);
l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__1 = _init_l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__1();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__1);
l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__2 = _init_l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__2();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__2);
l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__3 = _init_l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__3();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__3);
l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__4 = _init_l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__4();
lean_mark_persistent(l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___closed__4);
l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1);
l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2);
l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__3);
l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_induction___closed__1);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__13 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__13();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__13);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__14 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__14();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__14);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__15 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__15();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__15);
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__16 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__16();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__16);
l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1);
l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2 = _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2);
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
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__3);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__1);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___closed__2);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3);
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4);
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
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11);
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__12 = _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__12();
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__12);
l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1 = _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1();
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3);
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4 = _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4();
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4);
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__1);
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__2);
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__3);
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__4 = _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__4();
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___closed__4);
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
res = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5254_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
