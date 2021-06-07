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
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkConstructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__2(lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkConstructor___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_Meta_getNondepPropHyps___closed__1;
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Meta_RecursorInfo_0__Lean_Meta_mkRecursorInfoForKernelRec___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_copyVarName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_fmt___at_Lean_Position_instToFormatPosition___spec__1(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_whnf___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__2(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
extern lean_object* l_Lean_Parser_Syntax_addPrec___closed__2;
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1046____closed__1;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5;
lean_object* l_Lean_ConstantInfo_numLevelParams(lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__12(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkHeader___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1;
lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1046____closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
lean_object* l_instInhabitedDepArrow___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__1(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_getMkMatcherInputInContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__2(lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx_match__1(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_updatePrefix(lean_object*, lean_object*);
lean_object* l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedNat;
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__4;
lean_object* l_Lean_Meta_withLetDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__9___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Util_Trace_0__Lean_withNestedTracesFinalizer___spec__5___closed__1;
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
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
lean_object* l_Lean_Meta_IndPredBelow_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1621____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1;
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ppGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__5;
lean_object* l_Lean_Option_get___at_Lean_initFn____x40_Lean_Util_PPExt___hyg_231____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__3;
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10;
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewBinderInfosImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_671____at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewBinderInfos___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8(lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3;
lean_object* l_Lean_Meta_Match_Pattern_toMessageData(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__3___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Match_Pattern_toExpr_visit(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls_loop___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_903____closed__4;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_caseValue___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__1___boxed(lean_object**);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount_match__2(lean_object*);
lean_object* l_Lean_ConstantInfo_name(lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_rebuild___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__3(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Array_back___at_Lean_Meta_DiscrTree_mkPathAux___spec__1(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10;
lean_object* l_List_forM___at_Lean_Meta_IndPredBelow_proveBrecOn___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkCtorType_addHeaderVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__2(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9;
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Message_toString___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__6;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
lean_object* l_List_map___at_Lean_Meta_Match_Alt_toMessageData___spec__2(lean_object*);
lean_object* l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitPost___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1___boxed(lean_object*, lean_object*);
uint8_t l_Lean_isInductivePredicate_visit(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11;
extern lean_object* l_Lean_KernelException_toMessageData___closed__15;
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__1(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkMotiveBinder___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_71____closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KernelException_toMessageData___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Init_Data_Option_Basic_0__beqOption____x40_Init_Data_Option_Basic___hyg_671____at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1;
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkInductiveType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4;
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3;
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Meta_MatcherApp_addArg___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___private_Lean_Meta_InferType_0__Lean_Meta_inferForallType___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2;
lean_object* l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___rarg(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__1(lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_4____spec__1(lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_instInhabitedBinderInfo;
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___boxed(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3;
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_match__3(lean_object*);
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1;
extern lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__4;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4;
extern lean_object* l_Lean_Meta_Match_instInhabitedPattern;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6;
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5254_(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5_(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_MessageData_instCoeListExprMessageData___spec__1(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2;
lean_object* l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkContext___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__1;
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__8___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr___closed__1;
uint8_t l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelow___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_13362____closed__1;
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2;
extern lean_object* l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprMVarAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_modifyBinders(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_induction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_anyMAux___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_rebuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8;
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
extern lean_object* l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives_match__1___rarg(lean_object*, lean_object*);
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitLet___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2;
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17801____closed__3;
lean_object* l_Lean_Meta_transform_visit___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxDefinition___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3;
lean_object* l_Lean_Meta_withIncRecDepth___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__13___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1;
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5;
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_replaceTempVars___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkContext_addMotives_match__1(lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors___spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2;
lean_object* l_Lean_Meta_IndPredBelow_findBelowIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkContext_addMotives___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_fmt___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1;
extern lean_object* l_Lean_instInhabitedInductiveVal;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2;
extern lean_object* l_Lean_brecOnSuffix;
extern lean_object* l_Lean_maxRecDepth___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_unexpand____x40_Init_Notation___hyg_1981____closed__1;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern_match__1(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfoCtor___at_Lean_Meta_IndPredBelow_mkConstructor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow_match__1(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_MetavarContext_instantiateExprMVars___spec__1(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_mkConstWithLevelParams___spec__1(lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext_mkHeader___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7;
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
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1;
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2;
extern lean_object* l_List_zip___rarg___closed__1;
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_proveBrecOn_induction___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields_loop___spec__2___boxed(lean_object**);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_getBelowIndices___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_term___x3d_____closed__3;
lean_object* l_Lean_Expr_constName_x21(lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxDefinition___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertAt___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2;
lean_object* l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1;
lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1;
extern lean_object* l_Array_findSomeM_x3f___rarg___closed__1;
lean_object* l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH_match__1(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1;
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
extern lean_object* l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
lean_object* l_Lean_Meta_IndPredBelow_proveBrecOn_intros_match__2(lean_object*);
lean_object* l_Lean_Meta_getFVarLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_IndPredBelow_mkCtorType_checkCount(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__7___boxed(lean_object*, lean_object*);
#define _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("maxBackwardChainingDepth");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("The maximum search depth used in the backwards chaining part of the proof of `brecOn` for inductive predicates.");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3_end;\
}\
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; \
x_1 = lean_unsigned_to_nat(10u);\
x_2 = l_Lean_instInhabitedParserDescr___closed__1;\
x_3 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3;\
x_4 = lean_alloc_ctor(0, 3, 0);\
lean_ctor_set(x_4, 0, x_1);\
lean_ctor_set(x_4, 1, x_2);\
lean_ctor_set(x_4, 2, x_3);\
__INIT_VAR__ = x_4; goto l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4_end;\
}\
l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4_end: ((void) 0);}
lean_object* l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2;
x_3 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4;
x_4 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_RecDepth___hyg_4____spec__1(x_2, x_3, x_1);
return x_4;
}
}
#define _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Array_empty___closed__1;\
x_2 = l_Lean_instInhabitedExpr___closed__1;\
x_3 = lean_alloc_ctor(0, 6, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_1);\
lean_ctor_set(x_3, 2, x_1);\
lean_ctor_set(x_3, 3, x_1);\
lean_ctor_set(x_3, 4, x_1);\
lean_ctor_set(x_3, 5, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_instInhabitedVariables(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_instInhabitedVariables_end;\
}\
l_Lean_Meta_IndPredBelow_instInhabitedVariables_end: ((void) 0);}
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
#define _init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("motive_");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1_end: ((void) 0);}
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
x_11 = l_Lean_Meta_Match_mkMatcher___lambda__3___closed__2;
x_12 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_11, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_nat_add(x_2, x_9);
x_14 = l_Nat_repr(x_13);
x_15 = l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_Lean_instInhabitedParserDescr___closed__1;
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
lean_object* l_Lean_Meta_IndPredBelow_mkContext_motiveType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_9 = l_Lean_Meta_IndPredBelow_mkContext_mkIndValConst(x_1);
x_10 = l_Lean_mkAppN(x_9, x_2);
x_11 = l_Lean_Expr_getAppArgs___closed__1;
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
#define _init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("below");\
__INIT_VAR__ = x_1; goto l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1_end;\
}\
l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1_end: ((void) 0);}
#define _init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2_end;\
}\
l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2_end: ((void) 0);}
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
#define _init_l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1(__INIT_VAR__) { \
{\
size_t x_1; lean_object* x_2; \
x_1 = 0;\
x_2 = lean_box_usize(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1_end: ((void) 0);}
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
x_43 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
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
x_13 = l_Lean_Expr_getAppArgs___closed__1;
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
x_29 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
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
x_15 = l_Lean_Expr_getAppArgs___closed__1;
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
#define _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("only trivial inductive applications supported in premises:");\
__INIT_VAR__ = x_1; goto l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1_end;\
}\
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1_end: ((void) 0);}
#define _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2_end;\
}\
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2_end: ((void) 0);}
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
x_26 = l_Lean_KernelException_toMessageData___closed__15;
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
x_38 = l_Lean_KernelException_toMessageData___closed__15;
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
x_54 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
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
x_14 = l_Lean_Expr_getAppArgs___closed__1;
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
#define _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1(__INIT_VAR__) { \
{\
size_t x_1; lean_object* x_2; \
x_1 = 0;\
x_2 = lean_box_usize(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1_end;\
}\
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1_end: ((void) 0);}
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
x_22 = l_Lean_withIncRecDepth___rarg___lambda__2___closed__2;
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
x_18 = l_Lean_Expr_getAppArgs___closed__1;
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
x_23 = l_Array_empty___closed__1;
x_24 = l_Lean_Meta_transform_visit_visitLambda___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__4(x_1, x_2, x_3, x_4, x_23, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_24;
}
case 7:
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Array_empty___closed__1;
x_26 = l_Lean_Meta_transform_visit_visitForall___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__5(x_1, x_2, x_3, x_4, x_25, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_26;
}
case 8:
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Array_empty___closed__1;
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
x_26 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__2), 3, 2);
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
x_52 = lean_alloc_closure((void*)(l_Lean_MetavarContext_instantiateExprMVars___rarg___lambda__2), 3, 2);
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
#define _init_l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___lambda__1___boxed), 8, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1_end;\
}\
l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1_end: ((void) 0);}
lean_object* l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_box(0);
x_11 = lean_st_ref_get(x_8, x_9);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_14 = lean_st_mk_ref(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1;
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
#define _init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___lambda__3___boxed), 7, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("only arrows are allowed as premises. Multiple recursive occurrences detected:");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3_end;\
}\
l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3_end: ((void) 0);}
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
x_30 = l_Lean_KernelException_toMessageData___closed__15;
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
x_23 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
x_24 = lean_array_push(x_23, x_22);
x_25 = l_unexpand____x40_Init_Notation___hyg_1981____closed__1;
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
lean_object* l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_array_push(x_1, x_4);
x_11 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
#define _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_tryUnificationHints_tryCandidate___closed__3;\
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___rarg___lambda__1___boxed), 2, 1);\
lean_closure_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1_end;\
}\
l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1;\
x_2 = lean_alloc_closure((void*)(l_instInhabitedDepArrow___rarg), 2, 1);\
lean_closure_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2_end;\
}\
l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2_end: ((void) 0);}
#define _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3(__INIT_VAR__) { \
{\
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; \
x_1 = l_Lean_instInhabitedBinderInfo;\
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2;\
x_3 = lean_box(x_1);\
x_4 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_4, 0, x_3);\
lean_ctor_set(x_4, 1, x_2);\
__INIT_VAR__ = x_4; goto l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3_end;\
}\
l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3_end: ((void) 0);}
#define _init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_instInhabitedName;\
x_2 = l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4_end;\
}\
l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4_end: ((void) 0);}
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
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___lambda__1), 9, 3);
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
x_8 = l_Array_empty___closed__1;
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
#define _init_l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1(__INIT_VAR__) { \
{\
size_t x_1; lean_object* x_2; \
x_1 = 0;\
x_2 = lean_box_usize(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1_end: ((void) 0);}
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
x_20 = lean_alloc_closure((void*)(l___private_Lean_Meta_InferType_0__Lean_Meta_checkInferTypeCache___lambda__1___boxed), 7, 1);
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
x_18 = l_Array_empty___closed__1;
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
x_19 = l_Lean_KernelException_toMessageData___closed__3;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_getConstInfoCtor___rarg___lambda__1___closed__2;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Meta_isExprDefEq(x_1, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = 0;
x_20 = lean_box(x_19);
lean_ctor_set(x_14, 0, x_20);
return x_14;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = 0;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_dec(x_14);
x_26 = l_Lean_LocalDecl_toExpr(x_2);
x_27 = l_Lean_mkAppN(x_26, x_12);
x_28 = l_Lean_Meta_assignExprMVar(x_3, x_27, x_6, x_7, x_8, x_9, x_25);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_28, 1);
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_array_get_size(x_12);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_lt(x_33, x_32);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = 1;
x_36 = lean_box(x_35);
lean_ctor_set(x_28, 0, x_36);
return x_28;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_32, x_32);
if (x_37 == 0)
{
uint8_t x_38; lean_object* x_39; 
lean_dec(x_32);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_38 = 1;
x_39 = lean_box(x_38);
lean_ctor_set(x_28, 0, x_39);
return x_28;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; 
lean_free_object(x_28);
x_40 = 0;
x_41 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_42 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(x_4, x_12, x_40, x_41, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_42);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_dec(x_46);
x_47 = 1;
x_48 = lean_box(x_47);
lean_ctor_set(x_42, 0, x_48);
return x_42;
}
else
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_dec(x_42);
x_50 = 1;
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_42);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_42, 0);
lean_dec(x_54);
x_55 = 0;
x_56 = lean_box(x_55);
lean_ctor_set(x_42, 0, x_56);
return x_42;
}
else
{
lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_42, 1);
lean_inc(x_57);
lean_dec(x_42);
x_58 = 0;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_42);
if (x_61 == 0)
{
return x_42;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_42, 0);
x_63 = lean_ctor_get(x_42, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_42);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_28, 1);
lean_inc(x_65);
lean_dec(x_28);
x_66 = lean_array_get_size(x_12);
x_67 = lean_unsigned_to_nat(0u);
x_68 = lean_nat_dec_lt(x_67, x_66);
if (x_68 == 0)
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_66);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_69 = 1;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_65);
return x_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_66, x_66);
if (x_72 == 0)
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_66);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_73 = 1;
x_74 = lean_box(x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_65);
return x_75;
}
else
{
size_t x_76; size_t x_77; lean_object* x_78; 
x_76 = 0;
x_77 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_78 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__1(x_4, x_12, x_76, x_77, x_6, x_7, x_8, x_9, x_65);
lean_dec(x_12);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = 1;
x_84 = lean_box(x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_81);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_78, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_87 = x_78;
} else {
 lean_dec_ref(x_78);
 x_87 = lean_box(0);
}
x_88 = 0;
x_89 = lean_box(x_88);
if (lean_is_scalar(x_87)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_87;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_86);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_78, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_78, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_93 = x_78;
} else {
 lean_dec_ref(x_78);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_14);
if (x_95 == 0)
{
return x_14;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_14, 0);
x_97 = lean_ctor_get(x_14, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_14);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
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
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l_Lean_LocalDecl_type(x_17);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_forallMetaTelescope___boxed), 7, 2);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_21);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_23 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1___boxed), 10, 4);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_1);
lean_closure_set(x_23, 3, x_2);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3(x_24, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; size_t x_29; size_t x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = 1;
x_30 = x_5 + x_29;
x_5 = x_30;
x_11 = x_28;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = 1;
x_35 = lean_box(x_34);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_dec(x_25);
x_37 = 1;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
size_t x_44; size_t x_45; 
lean_dec(x_17);
x_44 = 1;
x_45 = x_5 + x_44;
x_5 = x_45;
goto _start;
}
}
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_11);
return x_49;
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
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = l_Lean_LocalDecl_type(x_17);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Meta_forallMetaTelescope___boxed), 7, 2);
lean_closure_set(x_22, 0, x_19);
lean_closure_set(x_22, 1, x_21);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_23 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__5___lambda__1___boxed), 10, 4);
lean_closure_set(x_23, 0, x_3);
lean_closure_set(x_23, 1, x_17);
lean_closure_set(x_23, 2, x_1);
lean_closure_set(x_23, 3, x_2);
x_24 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3(x_24, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; size_t x_29; size_t x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = 1;
x_30 = x_5 + x_29;
x_5 = x_30;
x_11 = x_28;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_25);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
x_34 = 1;
x_35 = lean_box(x_34);
lean_ctor_set(x_25, 0, x_35);
return x_25;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_25, 1);
lean_inc(x_36);
lean_dec(x_25);
x_37 = 1;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
size_t x_44; size_t x_45; 
lean_dec(x_17);
x_44 = 1;
x_45 = x_5 + x_44;
x_5 = x_45;
goto _start;
}
}
}
else
{
uint8_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = 0;
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_11);
return x_49;
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
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_Meta_getMVarType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_3, 1);
x_13 = l_Std_PersistentArray_anyM___at_Lean_Meta_IndPredBelow_backwardsChaining___spec__2(x_1, x_2, x_10, x_12, x_4, x_5, x_6, x_7, x_11);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1___boxed), 8, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_Meta_getNondepPropHyps___closed__1;
x_12 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_10);
x_13 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(x_1, x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
return x_16;
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
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_backwardsChaining___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
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
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("cannot apply induction hypothesis: ");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2_end: ((void) 0);}
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
x_24 = l_Array_findSomeM_x3f___rarg___closed__1;
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
x_13 = l_Lean_KernelException_toMessageData___closed__15;
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
x_34 = l_Lean_Parser_Tactic_myMacro____x40_Init_Notation___hyg_17801____closed__3;
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
x_19 = l_Lean_Expr_getAppArgs___closed__1;
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
x_24 = l_Lean_Expr_getAppArgs___closed__1;
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
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("couldn't solve by backwards chaining (");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Parser_Syntax_addPrec___closed__2;\
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1046____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("IndPredBelow");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3;\
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5;\
x_2 = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6;\
x_2 = lean_alloc_ctor(4, 1, 0);\
lean_ctor_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2;\
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7;\
x_3 = lean_alloc_ctor(10, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_term___x3d_____closed__3;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8;\
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9;\
x_3 = lean_alloc_ctor(10, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("): ");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12_end: ((void) 0);}
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
x_21 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_13);
x_25 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_25, 0, x_13);
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_KernelException_toMessageData___closed__15;
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
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("applying the induction hypothesis should only return one goal");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2_end: ((void) 0);}
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
x_23 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1621____spec__1(x_22, x_4, x_5, x_6, x_7, x_21);
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
x_50 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1621____spec__1(x_49, x_4, x_5, x_6, x_7, x_48);
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
#define _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("ih");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("ih_");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3_end;\
}\
l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3_end: ((void) 0);}
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
x_34 = l_Lean_instInhabitedParserDescr___closed__1;
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
#define _init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_brecOnSuffix;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1_end: ((void) 0);}
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
x_24 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_updateAlts___lambda__2___closed__1;
x_25 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_addPPExplicitToExposeDiff_visit___spec__2___rarg(x_2, x_24, x_23, x_6, x_7, x_8, x_9, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
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
x_11 = l_Array_empty___closed__1;
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
x_24 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
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
x_45 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
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
x_16 = l_Lean_Expr_getAppArgs___closed__1;
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
#define _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;\
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___lambda__1___boxed), 7, 1);\
lean_closure_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1_end;\
}\
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1_end: ((void) 0);}
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
x_17 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
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
x_24 = l_Lean_Meta_caseValue___closed__2;
x_25 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_24, x_8, x_9, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = 0;
x_29 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1;
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
}
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string(" ↦ ");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__2_end: ((void) 0);}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_4 == 0)
{
lean_object* x_10; lean_object* x_11; 
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = l_Lean_Meta_Match_Pattern_toMessageData(x_1);
x_13 = l_Lean_KernelException_toMessageData___closed__15;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__2;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_Match_Pattern_toMessageData(x_2);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
x_20 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_3, x_19, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1046____closed__2;\
x_2 = l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;\
x_2 = l_myMacro____x40_Init_Notation___hyg_13362____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;\
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___boxed), 7, 1);\
lean_closure_set(x_2, 0, x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l___private_Lean_Meta_SynthInstance_0__Lean_Meta_SynthInstance_mkAnswer___closed__4;\
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3;\
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);\
lean_closure_set(x_3, 0, x_1);\
lean_closure_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4_end: ((void) 0);}
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
x_16 = l_Lean_Expr_getAppArgs___closed__1;
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
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
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
x_82 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
lean_inc(x_81);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___boxed), 9, 3);
lean_closure_set(x_83, 0, x_3);
lean_closure_set(x_83, 1, x_81);
lean_closure_set(x_83, 2, x_82);
x_84 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4;
x_85 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_85, 0, x_84);
lean_closure_set(x_85, 1, x_83);
x_86 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___boxed), 8, 2);
lean_closure_set(x_86, 0, x_76);
lean_closure_set(x_86, 1, x_81);
x_87 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_87, 0, x_85);
lean_closure_set(x_87, 1, x_86);
x_88 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_78, x_87, x_4, x_5, x_6, x_7, x_75);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_26);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = !lean_is_exclusive(x_73);
if (x_89 == 0)
{
return x_73;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_73, 0);
x_91 = lean_ctor_get(x_73, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_73);
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
x_93 = !lean_is_exclusive(x_39);
if (x_93 == 0)
{
return x_39;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_39, 0);
x_95 = lean_ctor_get(x_39, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_39);
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
x_97 = !lean_is_exclusive(x_36);
if (x_97 == 0)
{
return x_36;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_36, 0);
x_99 = lean_ctor_get(x_36, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_36);
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
x_101 = !lean_is_exclusive(x_29);
if (x_101 == 0)
{
return x_29;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_29, 0);
x_103 = lean_ctor_get(x_29, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_29);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
case 5:
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_3);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_3, 0);
x_107 = lean_ctor_get(x_3, 1);
x_108 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_107, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_110, 1);
lean_ctor_set(x_3, 1, x_112);
lean_ctor_set(x_110, 1, x_3);
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_110, 0);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_110);
lean_ctor_set(x_3, 1, x_114);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_108, 0, x_115);
return x_108;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_108, 0);
x_117 = lean_ctor_get(x_108, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_108);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_120 = x_116;
} else {
 lean_dec_ref(x_116);
 x_120 = lean_box(0);
}
lean_ctor_set(x_3, 1, x_119);
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_3);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_free_object(x_3);
lean_dec(x_106);
x_123 = !lean_is_exclusive(x_108);
if (x_123 == 0)
{
return x_108;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_108, 0);
x_125 = lean_ctor_get(x_108, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_108);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_3, 0);
x_128 = lean_ctor_get(x_3, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_3);
x_129 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow(x_1, x_2, x_128, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_135 = x_130;
} else {
 lean_dec_ref(x_130);
 x_135 = lean_box(0);
}
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_134);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_133);
lean_ctor_set(x_137, 1, x_136);
if (lean_is_scalar(x_132)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_132;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_131);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_127);
x_139 = lean_ctor_get(x_129, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_129, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_141 = x_129;
} else {
 lean_dec_ref(x_129);
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
default: 
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_143 = l_Array_empty___closed__1;
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_3);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_8);
return x_145;
}
}
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_transformFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Array_empty___closed__1;
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
x_20 = l_Array_myMacro____x40_Init_Data_Array_Subarray___hyg_903____closed__4;
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
x_43 = l_Lean_Expr_getAppArgs___closed__1;
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
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_set(x_1, x_2, x_6);
x_13 = lean_ctor_get(x_3, 0);
x_14 = l_List_append___rarg(x_4, x_5);
x_15 = lean_array_to_list(lean_box(0), x_12);
lean_inc(x_13);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_array_to_list(lean_box(0), x_12);
x_15 = lean_array_push(x_1, x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_toInaccessible), 6, 1);
lean_closure_set(x_16, 0, x_2);
lean_inc(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1___boxed), 11, 5);
lean_closure_set(x_17, 0, x_15);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_14);
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_18, 0, x_16);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_14, x_18, x_7, x_8, x_9, x_10, x_11);
return x_19;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
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
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow), 8, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_16);
lean_inc(x_10);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__2), 11, 5);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_16);
lean_closure_set(x_18, 2, x_2);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_10);
x_19 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_10, x_19, x_5, x_6, x_7, x_8, x_9);
return x_20;
}
}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_addBelowPattern___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("motive := ");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2_end: ((void) 0);}
lean_object* l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_10 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Array_toSubarray___rarg(x_1, x_10, x_2);
x_12 = l_myMacro____x40_Init_Notation___hyg_71____closed__2;
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
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
x_41 = lean_st_ref_get(x_8, x_24);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 3);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get_uint8(x_43, sizeof(void*)*1);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_26 = x_20;
x_27 = x_45;
goto block_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_48 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_47, x_5, x_6, x_7, x_8, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_49);
lean_dec(x_49);
x_26 = x_51;
x_27 = x_50;
goto block_40;
}
block_40:
{
if (x_26 == 0)
{
lean_object* x_28; 
lean_dec(x_5);
if (lean_is_scalar(x_25)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_25;
}
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_25);
lean_inc(x_23);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_23);
x_30 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Lean_KernelException_toMessageData___closed__15;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_35 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_34, x_33, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_23);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_23);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_5);
x_52 = !lean_is_exclusive(x_22);
if (x_52 == 0)
{
return x_22;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_22, 0);
x_54 = lean_ctor_get(x_22, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_22);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("h_below");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2_end: ((void) 0);}
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
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("alt ");\
__INIT_VAR__ = x_1; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Message_toString___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("xs = ");\
__INIT_VAR__ = x_1; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("; oldFVars = ");\
__INIT_VAR__ = x_1; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("; fvars = ");\
__INIT_VAR__ = x_1; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("; new = ");\
__INIT_VAR__ = x_1; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10_end: ((void) 0);}
#define _init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11_end;\
}\
l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11_end: ((void) 0);}
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
x_142 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
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
x_83 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
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
x_60 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3;
x_61 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_7);
x_63 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__2;
x_65 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_inc(x_50);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_50);
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_KernelException_toMessageData___closed__15;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
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
x_98 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5;
x_99 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
x_100 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7;
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
x_110 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9;
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
x_116 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11;
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
x_130 = l_Lean_KernelException_toMessageData___closed__15;
x_131 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
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
x_30 = lean_st_ref_get(x_6, x_14);
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
x_15 = x_35;
x_16 = x_34;
goto block_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_38 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_37, x_3, x_4, x_5, x_6, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unbox(x_39);
lean_dec(x_39);
x_15 = x_41;
x_16 = x_40;
goto block_29;
}
block_29:
{
if (x_15 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = lean_box(0);
x_1 = x_10;
x_2 = x_17;
x_7 = x_16;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = l_List_map___at_Lean_Meta_Match_Alt_toMessageData___spec__2(x_13);
x_20 = l_Lean_MessageData_ofList(x_19);
lean_dec(x_19);
x_21 = l_Lean_KernelException_toMessageData___closed__15;
x_22 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
x_24 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_25 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_24, x_23, x_3, x_4, x_5, x_6, x_16);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_box(0);
x_1 = x_10;
x_2 = x_27;
x_7 = x_26;
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
x_30 = l_List_zip___rarg___closed__1;
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
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
x_49 = lean_box(0);
lean_inc(x_28);
x_50 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7___boxed), 7, 2);
lean_closure_set(x_50, 0, x_28);
lean_closure_set(x_50, 1, x_49);
x_51 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___closed__1;
x_52 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_51);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_48, x_52, x_5, x_6, x_7, x_8, x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_14, x_55);
lean_dec(x_14);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_45);
lean_ctor_set(x_57, 1, x_25);
lean_ctor_set(x_57, 2, x_56);
lean_ctor_set(x_57, 3, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_58 = l_Lean_Meta_Match_mkMatcher(x_57, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 3);
lean_inc(x_61);
lean_inc(x_61);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_62 = lean_apply_5(x_61, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_ctor_get(x_59, 0);
lean_inc(x_64);
lean_dec(x_59);
lean_inc(x_64);
x_65 = l_Lean_Meta_check(x_64, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
x_68 = lean_ctor_get(x_1, 5);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_array_push(x_68, x_3);
x_70 = l_Lean_mkApp(x_64, x_24);
x_71 = l_Lean_mkAppN(x_70, x_69);
lean_dec(x_69);
x_72 = l_Lean_mkAppN(x_71, x_41);
lean_dec(x_41);
lean_ctor_set(x_20, 1, x_61);
lean_ctor_set(x_20, 0, x_72);
lean_ctor_set(x_65, 0, x_20);
return x_65;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_dec(x_65);
x_74 = lean_ctor_get(x_1, 5);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_array_push(x_74, x_3);
x_76 = l_Lean_mkApp(x_64, x_24);
x_77 = l_Lean_mkAppN(x_76, x_75);
lean_dec(x_75);
x_78 = l_Lean_mkAppN(x_77, x_41);
lean_dec(x_41);
lean_ctor_set(x_20, 1, x_61);
lean_ctor_set(x_20, 0, x_78);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_20);
lean_ctor_set(x_79, 1, x_73);
return x_79;
}
}
else
{
uint8_t x_80; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_65);
if (x_80 == 0)
{
return x_65;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_65, 0);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_65);
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
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_62);
if (x_84 == 0)
{
return x_62;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_62, 0);
x_86 = lean_ctor_get(x_62, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_62);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_41);
lean_free_object(x_20);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_58);
if (x_88 == 0)
{
return x_58;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_58, 0);
x_90 = lean_ctor_get(x_58, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_58);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
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
x_92 = !lean_is_exclusive(x_53);
if (x_92 == 0)
{
return x_53;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_53, 0);
x_94 = lean_ctor_get(x_53, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_53);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
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
x_96 = !lean_is_exclusive(x_40);
if (x_96 == 0)
{
return x_40;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_40, 0);
x_98 = lean_ctor_get(x_40, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_40);
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
x_100 = !lean_is_exclusive(x_27);
if (x_100 == 0)
{
return x_27;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_27, 0);
x_102 = lean_ctor_get(x_27, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_27);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_20, 0);
x_105 = lean_ctor_get(x_20, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_20);
x_106 = lean_ctor_get(x_11, 3);
lean_inc(x_106);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_106);
x_107 = l_List_mapM___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__1(x_2, x_4, x_22, x_106, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_List_zip___rarg___closed__1;
lean_inc(x_108);
x_111 = l_List_zipWith___rarg(x_110, x_106, x_108);
x_112 = l_List_redLength___rarg(x_111);
x_113 = lean_mk_empty_array_with_capacity(x_112);
lean_dec(x_112);
x_114 = l_List_toArrayAux___rarg(x_111, x_113);
x_115 = lean_ctor_get(x_1, 7);
lean_inc(x_115);
x_116 = l_Array_zip___rarg(x_114, x_115);
lean_dec(x_115);
lean_dec(x_114);
x_117 = lean_array_get_size(x_116);
x_118 = lean_mk_empty_array_with_capacity(x_117);
x_119 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_108);
lean_inc(x_11);
lean_inc(x_1);
x_120 = l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4(x_1, x_11, x_108, x_116, x_117, x_119, lean_box(0), x_118, x_5, x_6, x_7, x_8, x_109);
lean_dec(x_116);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_ctor_get(x_11, 0);
lean_inc(x_123);
lean_dec(x_11);
x_124 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_123, x_7, x_8, x_122);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_box(0);
lean_inc(x_108);
x_128 = l_List_foldl___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__5(x_127, x_108);
x_129 = lean_box(0);
lean_inc(x_108);
x_130 = lean_alloc_closure((void*)(l_List_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__7___boxed), 7, 2);
lean_closure_set(x_130, 0, x_108);
lean_closure_set(x_130, 1, x_129);
x_131 = l___private_Lean_Meta_Match_Match_0__Lean_Meta_Match_checkNextPatternTypes___closed__1;
x_132 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_132, 0, x_130);
lean_closure_set(x_132, 1, x_131);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_133 = l_Lean_Meta_withExistingLocalDecls___at_Lean_Meta_Match_Alt_toMessageData___spec__3___rarg(x_128, x_132, x_5, x_6, x_7, x_8, x_126);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_14, x_135);
lean_dec(x_14);
x_137 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_137, 0, x_125);
lean_ctor_set(x_137, 1, x_105);
lean_ctor_set(x_137, 2, x_136);
lean_ctor_set(x_137, 3, x_108);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_138 = l_Lean_Meta_Match_mkMatcher(x_137, x_5, x_6, x_7, x_8, x_134);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_139, 3);
lean_inc(x_141);
lean_inc(x_141);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_142 = lean_apply_5(x_141, x_5, x_6, x_7, x_8, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_ctor_get(x_139, 0);
lean_inc(x_144);
lean_dec(x_139);
lean_inc(x_144);
x_145 = l_Lean_Meta_check(x_144, x_5, x_6, x_7, x_8, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
x_148 = lean_ctor_get(x_1, 5);
lean_inc(x_148);
lean_dec(x_1);
x_149 = lean_array_push(x_148, x_3);
x_150 = l_Lean_mkApp(x_144, x_104);
x_151 = l_Lean_mkAppN(x_150, x_149);
lean_dec(x_149);
x_152 = l_Lean_mkAppN(x_151, x_121);
lean_dec(x_121);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_141);
if (lean_is_scalar(x_147)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_147;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_146);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_144);
lean_dec(x_141);
lean_dec(x_121);
lean_dec(x_104);
lean_dec(x_3);
lean_dec(x_1);
x_155 = lean_ctor_get(x_145, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_145, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_157 = x_145;
} else {
 lean_dec_ref(x_145);
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
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_121);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_159 = lean_ctor_get(x_142, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_142, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_161 = x_142;
} else {
 lean_dec_ref(x_142);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_121);
lean_dec(x_104);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_163 = lean_ctor_get(x_138, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_138, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_165 = x_138;
} else {
 lean_dec_ref(x_138);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 2, 0);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_125);
lean_dec(x_121);
lean_dec(x_108);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_167 = lean_ctor_get(x_133, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_133, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_169 = x_133;
} else {
 lean_dec_ref(x_133);
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
lean_dec(x_108);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_171 = lean_ctor_get(x_120, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_120, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_173 = x_120;
} else {
 lean_dec_ref(x_120);
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
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_175 = lean_ctor_get(x_107, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_107, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_177 = x_107;
} else {
 lean_dec_ref(x_107);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
else
{
uint8_t x_179; 
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
x_179 = !lean_is_exclusive(x_17);
if (x_179 == 0)
{
return x_17;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_17, 0);
x_181 = lean_ctor_get(x_17, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_17);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_10);
if (x_183 == 0)
{
return x_10;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_10, 0);
x_185 = lean_ctor_get(x_10, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_10);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
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
#define _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("Found below term in the local context: ");\
__INIT_VAR__ = x_1; goto l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1_end;\
}\
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1_end: ((void) 0);}
#define _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2_end;\
}\
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2_end: ((void) 0);}
#define _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("could not find below term in the local context");\
__INIT_VAR__ = x_1; goto l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3_end;\
}\
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3_end: ((void) 0);}
#define _init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4_end;\
}\
l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4_end: ((void) 0);}
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
lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_86 = lean_st_ref_get(x_11, x_74);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 3);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_ctor_get_uint8(x_88, sizeof(void*)*1);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_73);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_92 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_39, x_91, x_8, x_9, x_10, x_11, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_st_ref_get(x_11, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 3);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_ctor_get_uint8(x_98, sizeof(void*)*1);
lean_dec(x_98);
if (x_99 == 0)
{
uint8_t x_100; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_100 = !lean_is_exclusive(x_96);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_96, 0);
lean_dec(x_101);
lean_ctor_set(x_96, 0, x_3);
return x_96;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_dec(x_96);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_3);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_104 = lean_ctor_get(x_96, 1);
lean_inc(x_104);
lean_dec(x_96);
x_105 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_106 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_105, x_8, x_9, x_10, x_11, x_104);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
uint8_t x_109; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_106, 0);
lean_dec(x_110);
lean_ctor_set(x_106, 0, x_3);
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_3);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
lean_dec(x_106);
x_114 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_115 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_105, x_114, x_8, x_9, x_10, x_11, x_113);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_115, 0);
lean_dec(x_117);
lean_ctor_set(x_115, 0, x_3);
return x_115;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_3);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_92, 1);
lean_inc(x_120);
lean_dec(x_92);
x_121 = lean_st_ref_get(x_11, x_120);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 3);
lean_inc(x_123);
lean_dec(x_122);
x_124 = lean_ctor_get_uint8(x_123, sizeof(void*)*1);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_121, 1);
lean_inc(x_125);
lean_dec(x_121);
x_126 = 0;
x_75 = x_126;
x_76 = x_125;
goto block_85;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_127 = lean_ctor_get(x_121, 1);
lean_inc(x_127);
lean_dec(x_121);
x_128 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_129 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_128, x_8, x_9, x_10, x_11, x_127);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_unbox(x_130);
lean_dec(x_130);
x_75 = x_132;
x_76 = x_131;
goto block_85;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_133 = !lean_is_exclusive(x_92);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_92, 0);
lean_dec(x_134);
lean_ctor_set_tag(x_92, 0);
lean_ctor_set(x_92, 0, x_3);
return x_92;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_92, 1);
lean_inc(x_135);
lean_dec(x_92);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_3);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_137 = lean_ctor_get(x_86, 1);
lean_inc(x_137);
lean_dec(x_86);
x_138 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_139 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_138, x_8, x_9, x_10, x_11, x_137);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_73);
x_142 = lean_ctor_get(x_139, 1);
lean_inc(x_142);
lean_dec(x_139);
x_143 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_144 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_39, x_143, x_8, x_9, x_10, x_11, x_142);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_148 = lean_st_ref_get(x_11, x_147);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_149, 3);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_ctor_get_uint8(x_150, sizeof(void*)*1);
lean_dec(x_150);
if (x_151 == 0)
{
uint8_t x_152; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_152 = !lean_is_exclusive(x_148);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_148, 0);
lean_dec(x_153);
lean_ctor_set(x_148, 0, x_3);
return x_148;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_148, 1);
lean_inc(x_154);
lean_dec(x_148);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_3);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_156 = lean_ctor_get(x_148, 1);
lean_inc(x_156);
lean_dec(x_148);
x_157 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_138, x_8, x_9, x_10, x_11, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
uint8_t x_160; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_160 = !lean_is_exclusive(x_157);
if (x_160 == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_157, 0);
lean_dec(x_161);
lean_ctor_set(x_157, 0, x_3);
return x_157;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_157, 1);
lean_inc(x_162);
lean_dec(x_157);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_3);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_dec(x_157);
x_165 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_166 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_138, x_165, x_8, x_9, x_10, x_11, x_164);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_166, 0);
lean_dec(x_168);
lean_ctor_set(x_166, 0, x_3);
return x_166;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_3);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_171 = lean_ctor_get(x_144, 1);
lean_inc(x_171);
lean_dec(x_144);
x_172 = lean_st_ref_get(x_11, x_171);
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_173, 3);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_ctor_get_uint8(x_174, sizeof(void*)*1);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_172, 1);
lean_inc(x_176);
lean_dec(x_172);
x_177 = 0;
x_75 = x_177;
x_76 = x_176;
goto block_85;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = lean_ctor_get(x_172, 1);
lean_inc(x_178);
lean_dec(x_172);
x_179 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_138, x_8, x_9, x_10, x_11, x_178);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unbox(x_180);
lean_dec(x_180);
x_75 = x_182;
x_76 = x_181;
goto block_85;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_183 = !lean_is_exclusive(x_144);
if (x_183 == 0)
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_144, 0);
lean_dec(x_184);
lean_ctor_set_tag(x_144, 0);
lean_ctor_set(x_144, 0, x_3);
return x_144;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_144, 1);
lean_inc(x_185);
lean_dec(x_144);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_3);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_187 = lean_ctor_get(x_139, 1);
lean_inc(x_187);
lean_dec(x_139);
x_188 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_188, 0, x_73);
x_189 = l_Lean_KernelException_toMessageData___closed__15;
x_190 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
x_191 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
x_192 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_138, x_191, x_8, x_9, x_10, x_11, x_187);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_195 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_39, x_194, x_8, x_9, x_10, x_11, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_199 = lean_st_ref_get(x_11, x_198);
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_200, 3);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_ctor_get_uint8(x_201, sizeof(void*)*1);
lean_dec(x_201);
if (x_202 == 0)
{
uint8_t x_203; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_203 = !lean_is_exclusive(x_199);
if (x_203 == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_199, 0);
lean_dec(x_204);
lean_ctor_set(x_199, 0, x_3);
return x_199;
}
else
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_199, 1);
lean_inc(x_205);
lean_dec(x_199);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_3);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_207 = lean_ctor_get(x_199, 1);
lean_inc(x_207);
lean_dec(x_199);
x_208 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_138, x_8, x_9, x_10, x_11, x_207);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_unbox(x_209);
lean_dec(x_209);
if (x_210 == 0)
{
uint8_t x_211; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_211 = !lean_is_exclusive(x_208);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_208, 0);
lean_dec(x_212);
lean_ctor_set(x_208, 0, x_3);
return x_208;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_208, 1);
lean_inc(x_213);
lean_dec(x_208);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_3);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = lean_ctor_get(x_208, 1);
lean_inc(x_215);
lean_dec(x_208);
x_216 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_217 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_138, x_216, x_8, x_9, x_10, x_11, x_215);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_217, 0);
lean_dec(x_219);
lean_ctor_set(x_217, 0, x_3);
return x_217;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_3);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_222 = lean_ctor_get(x_195, 1);
lean_inc(x_222);
lean_dec(x_195);
x_223 = lean_st_ref_get(x_11, x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_224, 3);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_ctor_get_uint8(x_225, sizeof(void*)*1);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_ctor_get(x_223, 1);
lean_inc(x_227);
lean_dec(x_223);
x_228 = 0;
x_75 = x_228;
x_76 = x_227;
goto block_85;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_229 = lean_ctor_get(x_223, 1);
lean_inc(x_229);
lean_dec(x_223);
x_230 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_138, x_8, x_9, x_10, x_11, x_229);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_unbox(x_231);
lean_dec(x_231);
x_75 = x_233;
x_76 = x_232;
goto block_85;
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_234 = !lean_is_exclusive(x_195);
if (x_234 == 0)
{
lean_object* x_235; 
x_235 = lean_ctor_get(x_195, 0);
lean_dec(x_235);
lean_ctor_set_tag(x_195, 0);
lean_ctor_set(x_195, 0, x_3);
return x_195;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_195, 1);
lean_inc(x_236);
lean_dec(x_195);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_3);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
block_85:
{
if (x_75 == 0)
{
x_40 = x_76;
goto block_71;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_inc(x_36);
x_77 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_77, 0, x_36);
x_78 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_79 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
x_80 = l_Lean_KernelException_toMessageData___closed__15;
x_81 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_83 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_82, x_81, x_8, x_9, x_10, x_11, x_76);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_40 = x_84;
goto block_71;
}
}
}
else
{
uint8_t x_238; 
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
x_238 = !lean_is_exclusive(x_72);
if (x_238 == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_72, 0);
lean_dec(x_239);
lean_ctor_set_tag(x_72, 0);
lean_ctor_set(x_72, 0, x_3);
return x_72;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_72, 1);
lean_inc(x_240);
lean_dec(x_72);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_3);
lean_ctor_set(x_241, 1, x_240);
return x_241;
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
uint8_t x_242; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_242 = !lean_is_exclusive(x_29);
if (x_242 == 0)
{
return x_29;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_29, 0);
x_244 = lean_ctor_get(x_29, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_29);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
}
}
case 1:
{
lean_object* x_246; 
lean_dec(x_7);
lean_dec(x_6);
x_246 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_3);
lean_ctor_set(x_247, 1, x_12);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
lean_dec(x_246);
x_249 = lean_unsigned_to_nat(0u);
x_250 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_249);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
lean_dec(x_248);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_3);
lean_ctor_set(x_251, 1, x_12);
return x_251;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_252 = lean_ctor_get(x_250, 0);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
x_254 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_248, x_8, x_9, x_10, x_11, x_12);
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_unbox(x_255);
lean_dec(x_255);
if (x_256 == 0)
{
uint8_t x_257; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_257 = !lean_is_exclusive(x_254);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_254, 0);
lean_dec(x_258);
lean_ctor_set(x_254, 0, x_3);
return x_254;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_254, 1);
lean_inc(x_259);
lean_dec(x_254);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_3);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_254, 1);
lean_inc(x_261);
lean_dec(x_254);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_262 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_252, x_8, x_9, x_10, x_11, x_261);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_305; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_266 = x_263;
} else {
 lean_dec_ref(x_263);
 x_266 = lean_box(0);
}
x_267 = lean_box(0);
lean_inc(x_8);
x_268 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_265, x_267, x_8, x_9, x_10, x_11, x_264);
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
x_272 = l_Lean_Expr_mvarId_x21(x_269);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_305 = l_Lean_Meta_ppGoal(x_272, x_8, x_9, x_10, x_11, x_270);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_319 = lean_st_ref_get(x_11, x_307);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_320, 3);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_ctor_get_uint8(x_321, sizeof(void*)*1);
lean_dec(x_321);
if (x_322 == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_306);
x_323 = lean_ctor_get(x_319, 1);
lean_inc(x_323);
lean_dec(x_319);
x_324 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_325 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_272, x_324, x_8, x_9, x_10, x_11, x_323);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; uint8_t x_327; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_unbox(x_326);
lean_dec(x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_253);
lean_dec(x_252);
x_328 = lean_ctor_get(x_325, 1);
lean_inc(x_328);
lean_dec(x_325);
x_329 = lean_st_ref_get(x_11, x_328);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_330, 3);
lean_inc(x_331);
lean_dec(x_330);
x_332 = lean_ctor_get_uint8(x_331, sizeof(void*)*1);
lean_dec(x_331);
if (x_332 == 0)
{
uint8_t x_333; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_333 = !lean_is_exclusive(x_329);
if (x_333 == 0)
{
lean_object* x_334; 
x_334 = lean_ctor_get(x_329, 0);
lean_dec(x_334);
lean_ctor_set(x_329, 0, x_3);
return x_329;
}
else
{
lean_object* x_335; lean_object* x_336; 
x_335 = lean_ctor_get(x_329, 1);
lean_inc(x_335);
lean_dec(x_329);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_3);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_337 = lean_ctor_get(x_329, 1);
lean_inc(x_337);
lean_dec(x_329);
x_338 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_339 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_338, x_8, x_9, x_10, x_11, x_337);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
x_341 = lean_unbox(x_340);
lean_dec(x_340);
if (x_341 == 0)
{
uint8_t x_342; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_342 = !lean_is_exclusive(x_339);
if (x_342 == 0)
{
lean_object* x_343; 
x_343 = lean_ctor_get(x_339, 0);
lean_dec(x_343);
lean_ctor_set(x_339, 0, x_3);
return x_339;
}
else
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_339, 1);
lean_inc(x_344);
lean_dec(x_339);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_3);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; uint8_t x_349; 
x_346 = lean_ctor_get(x_339, 1);
lean_inc(x_346);
lean_dec(x_339);
x_347 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_348 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_338, x_347, x_8, x_9, x_10, x_11, x_346);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_348, 0);
lean_dec(x_350);
lean_ctor_set(x_348, 0, x_3);
return x_348;
}
else
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
lean_dec(x_348);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_3);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_353 = lean_ctor_get(x_325, 1);
lean_inc(x_353);
lean_dec(x_325);
x_354 = lean_st_ref_get(x_11, x_353);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_355, 3);
lean_inc(x_356);
lean_dec(x_355);
x_357 = lean_ctor_get_uint8(x_356, sizeof(void*)*1);
lean_dec(x_356);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; 
x_358 = lean_ctor_get(x_354, 1);
lean_inc(x_358);
lean_dec(x_354);
x_359 = 0;
x_308 = x_359;
x_309 = x_358;
goto block_318;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_360 = lean_ctor_get(x_354, 1);
lean_inc(x_360);
lean_dec(x_354);
x_361 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_362 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_361, x_8, x_9, x_10, x_11, x_360);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = lean_unbox(x_363);
lean_dec(x_363);
x_308 = x_365;
x_309 = x_364;
goto block_318;
}
}
}
else
{
uint8_t x_366; 
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_366 = !lean_is_exclusive(x_325);
if (x_366 == 0)
{
lean_object* x_367; 
x_367 = lean_ctor_get(x_325, 0);
lean_dec(x_367);
lean_ctor_set_tag(x_325, 0);
lean_ctor_set(x_325, 0, x_3);
return x_325;
}
else
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_325, 1);
lean_inc(x_368);
lean_dec(x_325);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_3);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_370 = lean_ctor_get(x_319, 1);
lean_inc(x_370);
lean_dec(x_319);
x_371 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_372 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_371, x_8, x_9, x_10, x_11, x_370);
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
x_374 = lean_unbox(x_373);
lean_dec(x_373);
if (x_374 == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_306);
x_375 = lean_ctor_get(x_372, 1);
lean_inc(x_375);
lean_dec(x_372);
x_376 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_377 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_272, x_376, x_8, x_9, x_10, x_11, x_375);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; uint8_t x_379; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_unbox(x_378);
lean_dec(x_378);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_253);
lean_dec(x_252);
x_380 = lean_ctor_get(x_377, 1);
lean_inc(x_380);
lean_dec(x_377);
x_381 = lean_st_ref_get(x_11, x_380);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_382, 3);
lean_inc(x_383);
lean_dec(x_382);
x_384 = lean_ctor_get_uint8(x_383, sizeof(void*)*1);
lean_dec(x_383);
if (x_384 == 0)
{
uint8_t x_385; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_385 = !lean_is_exclusive(x_381);
if (x_385 == 0)
{
lean_object* x_386; 
x_386 = lean_ctor_get(x_381, 0);
lean_dec(x_386);
lean_ctor_set(x_381, 0, x_3);
return x_381;
}
else
{
lean_object* x_387; lean_object* x_388; 
x_387 = lean_ctor_get(x_381, 1);
lean_inc(x_387);
lean_dec(x_381);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_3);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; 
x_389 = lean_ctor_get(x_381, 1);
lean_inc(x_389);
lean_dec(x_381);
x_390 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_371, x_8, x_9, x_10, x_11, x_389);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_unbox(x_391);
lean_dec(x_391);
if (x_392 == 0)
{
uint8_t x_393; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_393 = !lean_is_exclusive(x_390);
if (x_393 == 0)
{
lean_object* x_394; 
x_394 = lean_ctor_get(x_390, 0);
lean_dec(x_394);
lean_ctor_set(x_390, 0, x_3);
return x_390;
}
else
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_390, 1);
lean_inc(x_395);
lean_dec(x_390);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_3);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
x_397 = lean_ctor_get(x_390, 1);
lean_inc(x_397);
lean_dec(x_390);
x_398 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_399 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_371, x_398, x_8, x_9, x_10, x_11, x_397);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_400 = !lean_is_exclusive(x_399);
if (x_400 == 0)
{
lean_object* x_401; 
x_401 = lean_ctor_get(x_399, 0);
lean_dec(x_401);
lean_ctor_set(x_399, 0, x_3);
return x_399;
}
else
{
lean_object* x_402; lean_object* x_403; 
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
lean_dec(x_399);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_3);
lean_ctor_set(x_403, 1, x_402);
return x_403;
}
}
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_404 = lean_ctor_get(x_377, 1);
lean_inc(x_404);
lean_dec(x_377);
x_405 = lean_st_ref_get(x_11, x_404);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_406, 3);
lean_inc(x_407);
lean_dec(x_406);
x_408 = lean_ctor_get_uint8(x_407, sizeof(void*)*1);
lean_dec(x_407);
if (x_408 == 0)
{
lean_object* x_409; uint8_t x_410; 
x_409 = lean_ctor_get(x_405, 1);
lean_inc(x_409);
lean_dec(x_405);
x_410 = 0;
x_308 = x_410;
x_309 = x_409;
goto block_318;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; 
x_411 = lean_ctor_get(x_405, 1);
lean_inc(x_411);
lean_dec(x_405);
x_412 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_371, x_8, x_9, x_10, x_11, x_411);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_unbox(x_413);
lean_dec(x_413);
x_308 = x_415;
x_309 = x_414;
goto block_318;
}
}
}
else
{
uint8_t x_416; 
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_416 = !lean_is_exclusive(x_377);
if (x_416 == 0)
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_377, 0);
lean_dec(x_417);
lean_ctor_set_tag(x_377, 0);
lean_ctor_set(x_377, 0, x_3);
return x_377;
}
else
{
lean_object* x_418; lean_object* x_419; 
x_418 = lean_ctor_get(x_377, 1);
lean_inc(x_418);
lean_dec(x_377);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_3);
lean_ctor_set(x_419, 1, x_418);
return x_419;
}
}
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_420 = lean_ctor_get(x_372, 1);
lean_inc(x_420);
lean_dec(x_372);
x_421 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_421, 0, x_306);
x_422 = l_Lean_KernelException_toMessageData___closed__15;
x_423 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_421);
x_424 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_424, 0, x_423);
lean_ctor_set(x_424, 1, x_422);
x_425 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_371, x_424, x_8, x_9, x_10, x_11, x_420);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_427 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_428 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_272, x_427, x_8, x_9, x_10, x_11, x_426);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; uint8_t x_430; 
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_unbox(x_429);
lean_dec(x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; uint8_t x_435; 
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_253);
lean_dec(x_252);
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
lean_dec(x_428);
x_432 = lean_st_ref_get(x_11, x_431);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_433, 3);
lean_inc(x_434);
lean_dec(x_433);
x_435 = lean_ctor_get_uint8(x_434, sizeof(void*)*1);
lean_dec(x_434);
if (x_435 == 0)
{
uint8_t x_436; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_436 = !lean_is_exclusive(x_432);
if (x_436 == 0)
{
lean_object* x_437; 
x_437 = lean_ctor_get(x_432, 0);
lean_dec(x_437);
lean_ctor_set(x_432, 0, x_3);
return x_432;
}
else
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_432, 1);
lean_inc(x_438);
lean_dec(x_432);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_3);
lean_ctor_set(x_439, 1, x_438);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; 
x_440 = lean_ctor_get(x_432, 1);
lean_inc(x_440);
lean_dec(x_432);
x_441 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_371, x_8, x_9, x_10, x_11, x_440);
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_unbox(x_442);
lean_dec(x_442);
if (x_443 == 0)
{
uint8_t x_444; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_444 = !lean_is_exclusive(x_441);
if (x_444 == 0)
{
lean_object* x_445; 
x_445 = lean_ctor_get(x_441, 0);
lean_dec(x_445);
lean_ctor_set(x_441, 0, x_3);
return x_441;
}
else
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_441, 1);
lean_inc(x_446);
lean_dec(x_441);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_3);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_448 = lean_ctor_get(x_441, 1);
lean_inc(x_448);
lean_dec(x_441);
x_449 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_450 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_371, x_449, x_8, x_9, x_10, x_11, x_448);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_451 = !lean_is_exclusive(x_450);
if (x_451 == 0)
{
lean_object* x_452; 
x_452 = lean_ctor_get(x_450, 0);
lean_dec(x_452);
lean_ctor_set(x_450, 0, x_3);
return x_450;
}
else
{
lean_object* x_453; lean_object* x_454; 
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_3);
lean_ctor_set(x_454, 1, x_453);
return x_454;
}
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; 
x_455 = lean_ctor_get(x_428, 1);
lean_inc(x_455);
lean_dec(x_428);
x_456 = lean_st_ref_get(x_11, x_455);
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_457, 3);
lean_inc(x_458);
lean_dec(x_457);
x_459 = lean_ctor_get_uint8(x_458, sizeof(void*)*1);
lean_dec(x_458);
if (x_459 == 0)
{
lean_object* x_460; uint8_t x_461; 
x_460 = lean_ctor_get(x_456, 1);
lean_inc(x_460);
lean_dec(x_456);
x_461 = 0;
x_308 = x_461;
x_309 = x_460;
goto block_318;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; 
x_462 = lean_ctor_get(x_456, 1);
lean_inc(x_462);
lean_dec(x_456);
x_463 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_371, x_8, x_9, x_10, x_11, x_462);
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
x_466 = lean_unbox(x_464);
lean_dec(x_464);
x_308 = x_466;
x_309 = x_465;
goto block_318;
}
}
}
else
{
uint8_t x_467; 
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_467 = !lean_is_exclusive(x_428);
if (x_467 == 0)
{
lean_object* x_468; 
x_468 = lean_ctor_get(x_428, 0);
lean_dec(x_468);
lean_ctor_set_tag(x_428, 0);
lean_ctor_set(x_428, 0, x_3);
return x_428;
}
else
{
lean_object* x_469; lean_object* x_470; 
x_469 = lean_ctor_get(x_428, 1);
lean_inc(x_469);
lean_dec(x_428);
x_470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_470, 0, x_3);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
}
}
}
block_318:
{
if (x_308 == 0)
{
x_273 = x_309;
goto block_304;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_inc(x_269);
x_310 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_310, 0, x_269);
x_311 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_312 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_310);
x_313 = l_Lean_KernelException_toMessageData___closed__15;
x_314 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_316 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_315, x_314, x_8, x_9, x_10, x_11, x_309);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_273 = x_317;
goto block_304;
}
}
}
else
{
uint8_t x_471; 
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_471 = !lean_is_exclusive(x_305);
if (x_471 == 0)
{
lean_object* x_472; 
x_472 = lean_ctor_get(x_305, 0);
lean_dec(x_472);
lean_ctor_set_tag(x_305, 0);
lean_ctor_set(x_305, 0, x_3);
return x_305;
}
else
{
lean_object* x_473; lean_object* x_474; 
x_473 = lean_ctor_get(x_305, 1);
lean_inc(x_473);
lean_dec(x_305);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_3);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
block_304:
{
lean_object* x_274; uint8_t x_275; 
x_274 = lean_array_get_size(x_1);
x_275 = lean_nat_dec_lt(x_249, x_274);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_274);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_266)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_266;
}
lean_ctor_set(x_276, 0, x_269);
lean_ctor_set(x_276, 1, x_252);
if (lean_is_scalar(x_253)) {
 x_277 = lean_alloc_ctor(1, 1, 0);
} else {
 x_277 = x_253;
}
lean_ctor_set(x_277, 0, x_276);
if (lean_is_scalar(x_271)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_271;
}
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_273);
return x_278;
}
else
{
uint8_t x_279; 
x_279 = lean_nat_dec_le(x_274, x_274);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_274);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_266)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_266;
}
lean_ctor_set(x_280, 0, x_269);
lean_ctor_set(x_280, 1, x_252);
if (lean_is_scalar(x_253)) {
 x_281 = lean_alloc_ctor(1, 1, 0);
} else {
 x_281 = x_253;
}
lean_ctor_set(x_281, 0, x_280);
if (lean_is_scalar(x_271)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_271;
}
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_273);
return x_282;
}
else
{
size_t x_283; size_t x_284; lean_object* x_285; 
lean_dec(x_271);
x_283 = 0;
x_284 = lean_usize_of_nat(x_274);
lean_dec(x_274);
lean_inc(x_269);
x_285 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_269, x_1, x_283, x_284, x_8, x_9, x_10, x_11, x_273);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; uint8_t x_287; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_unbox(x_286);
lean_dec(x_286);
if (x_287 == 0)
{
uint8_t x_288; 
lean_dec(x_3);
x_288 = !lean_is_exclusive(x_285);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_285, 0);
lean_dec(x_289);
if (lean_is_scalar(x_266)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_266;
}
lean_ctor_set(x_290, 0, x_269);
lean_ctor_set(x_290, 1, x_252);
if (lean_is_scalar(x_253)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_253;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_285, 0, x_291);
return x_285;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_285, 1);
lean_inc(x_292);
lean_dec(x_285);
if (lean_is_scalar(x_266)) {
 x_293 = lean_alloc_ctor(0, 2, 0);
} else {
 x_293 = x_266;
}
lean_ctor_set(x_293, 0, x_269);
lean_ctor_set(x_293, 1, x_252);
if (lean_is_scalar(x_253)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_253;
}
lean_ctor_set(x_294, 0, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_292);
return x_295;
}
}
else
{
uint8_t x_296; 
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_253);
lean_dec(x_252);
x_296 = !lean_is_exclusive(x_285);
if (x_296 == 0)
{
lean_object* x_297; 
x_297 = lean_ctor_get(x_285, 0);
lean_dec(x_297);
lean_ctor_set(x_285, 0, x_3);
return x_285;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_285, 1);
lean_inc(x_298);
lean_dec(x_285);
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_3);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_269);
lean_dec(x_266);
lean_dec(x_253);
lean_dec(x_252);
x_300 = !lean_is_exclusive(x_285);
if (x_300 == 0)
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_285, 0);
lean_dec(x_301);
lean_ctor_set_tag(x_285, 0);
lean_ctor_set(x_285, 0, x_3);
return x_285;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_285, 1);
lean_inc(x_302);
lean_dec(x_285);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_3);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
}
}
}
else
{
uint8_t x_475; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_475 = !lean_is_exclusive(x_262);
if (x_475 == 0)
{
return x_262;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_262, 0);
x_477 = lean_ctor_get(x_262, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_262);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
}
}
}
case 2:
{
lean_object* x_479; 
lean_dec(x_7);
lean_dec(x_6);
x_479 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_3);
lean_ctor_set(x_480, 1, x_12);
return x_480;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_479, 0);
lean_inc(x_481);
lean_dec(x_479);
x_482 = lean_unsigned_to_nat(0u);
x_483 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_482);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; 
lean_dec(x_481);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_3);
lean_ctor_set(x_484, 1, x_12);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; 
x_485 = lean_ctor_get(x_483, 0);
lean_inc(x_485);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 x_486 = x_483;
} else {
 lean_dec_ref(x_483);
 x_486 = lean_box(0);
}
x_487 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_481, x_8, x_9, x_10, x_11, x_12);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_unbox(x_488);
lean_dec(x_488);
if (x_489 == 0)
{
uint8_t x_490; 
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_490 = !lean_is_exclusive(x_487);
if (x_490 == 0)
{
lean_object* x_491; 
x_491 = lean_ctor_get(x_487, 0);
lean_dec(x_491);
lean_ctor_set(x_487, 0, x_3);
return x_487;
}
else
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_ctor_get(x_487, 1);
lean_inc(x_492);
lean_dec(x_487);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_3);
lean_ctor_set(x_493, 1, x_492);
return x_493;
}
}
else
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_ctor_get(x_487, 1);
lean_inc(x_494);
lean_dec(x_487);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_495 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_485, x_8, x_9, x_10, x_11, x_494);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_538; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_499 = x_496;
} else {
 lean_dec_ref(x_496);
 x_499 = lean_box(0);
}
x_500 = lean_box(0);
lean_inc(x_8);
x_501 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_498, x_500, x_8, x_9, x_10, x_11, x_497);
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_504 = x_501;
} else {
 lean_dec_ref(x_501);
 x_504 = lean_box(0);
}
x_505 = l_Lean_Expr_mvarId_x21(x_502);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_538 = l_Lean_Meta_ppGoal(x_505, x_8, x_9, x_10, x_11, x_503);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; uint8_t x_541; lean_object* x_542; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
lean_dec(x_538);
x_552 = lean_st_ref_get(x_11, x_540);
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_553, 3);
lean_inc(x_554);
lean_dec(x_553);
x_555 = lean_ctor_get_uint8(x_554, sizeof(void*)*1);
lean_dec(x_554);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_539);
x_556 = lean_ctor_get(x_552, 1);
lean_inc(x_556);
lean_dec(x_552);
x_557 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_558 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_505, x_557, x_8, x_9, x_10, x_11, x_556);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; uint8_t x_560; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_unbox(x_559);
lean_dec(x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint8_t x_565; 
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_499);
lean_dec(x_486);
lean_dec(x_485);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_dec(x_558);
x_562 = lean_st_ref_get(x_11, x_561);
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_563, 3);
lean_inc(x_564);
lean_dec(x_563);
x_565 = lean_ctor_get_uint8(x_564, sizeof(void*)*1);
lean_dec(x_564);
if (x_565 == 0)
{
uint8_t x_566; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_566 = !lean_is_exclusive(x_562);
if (x_566 == 0)
{
lean_object* x_567; 
x_567 = lean_ctor_get(x_562, 0);
lean_dec(x_567);
lean_ctor_set(x_562, 0, x_3);
return x_562;
}
else
{
lean_object* x_568; lean_object* x_569; 
x_568 = lean_ctor_get(x_562, 1);
lean_inc(x_568);
lean_dec(x_562);
x_569 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_569, 0, x_3);
lean_ctor_set(x_569, 1, x_568);
return x_569;
}
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; uint8_t x_574; 
x_570 = lean_ctor_get(x_562, 1);
lean_inc(x_570);
lean_dec(x_562);
x_571 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_572 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_571, x_8, x_9, x_10, x_11, x_570);
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_unbox(x_573);
lean_dec(x_573);
if (x_574 == 0)
{
uint8_t x_575; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_575 = !lean_is_exclusive(x_572);
if (x_575 == 0)
{
lean_object* x_576; 
x_576 = lean_ctor_get(x_572, 0);
lean_dec(x_576);
lean_ctor_set(x_572, 0, x_3);
return x_572;
}
else
{
lean_object* x_577; lean_object* x_578; 
x_577 = lean_ctor_get(x_572, 1);
lean_inc(x_577);
lean_dec(x_572);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_3);
lean_ctor_set(x_578, 1, x_577);
return x_578;
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; uint8_t x_582; 
x_579 = lean_ctor_get(x_572, 1);
lean_inc(x_579);
lean_dec(x_572);
x_580 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_581 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_571, x_580, x_8, x_9, x_10, x_11, x_579);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_582 = !lean_is_exclusive(x_581);
if (x_582 == 0)
{
lean_object* x_583; 
x_583 = lean_ctor_get(x_581, 0);
lean_dec(x_583);
lean_ctor_set(x_581, 0, x_3);
return x_581;
}
else
{
lean_object* x_584; lean_object* x_585; 
x_584 = lean_ctor_get(x_581, 1);
lean_inc(x_584);
lean_dec(x_581);
x_585 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_585, 0, x_3);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; 
x_586 = lean_ctor_get(x_558, 1);
lean_inc(x_586);
lean_dec(x_558);
x_587 = lean_st_ref_get(x_11, x_586);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_588, 3);
lean_inc(x_589);
lean_dec(x_588);
x_590 = lean_ctor_get_uint8(x_589, sizeof(void*)*1);
lean_dec(x_589);
if (x_590 == 0)
{
lean_object* x_591; uint8_t x_592; 
x_591 = lean_ctor_get(x_587, 1);
lean_inc(x_591);
lean_dec(x_587);
x_592 = 0;
x_541 = x_592;
x_542 = x_591;
goto block_551;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; 
x_593 = lean_ctor_get(x_587, 1);
lean_inc(x_593);
lean_dec(x_587);
x_594 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_595 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_594, x_8, x_9, x_10, x_11, x_593);
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = lean_unbox(x_596);
lean_dec(x_596);
x_541 = x_598;
x_542 = x_597;
goto block_551;
}
}
}
else
{
uint8_t x_599; 
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_499);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_599 = !lean_is_exclusive(x_558);
if (x_599 == 0)
{
lean_object* x_600; 
x_600 = lean_ctor_get(x_558, 0);
lean_dec(x_600);
lean_ctor_set_tag(x_558, 0);
lean_ctor_set(x_558, 0, x_3);
return x_558;
}
else
{
lean_object* x_601; lean_object* x_602; 
x_601 = lean_ctor_get(x_558, 1);
lean_inc(x_601);
lean_dec(x_558);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_3);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; 
x_603 = lean_ctor_get(x_552, 1);
lean_inc(x_603);
lean_dec(x_552);
x_604 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_605 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_604, x_8, x_9, x_10, x_11, x_603);
x_606 = lean_ctor_get(x_605, 0);
lean_inc(x_606);
x_607 = lean_unbox(x_606);
lean_dec(x_606);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; 
lean_dec(x_539);
x_608 = lean_ctor_get(x_605, 1);
lean_inc(x_608);
lean_dec(x_605);
x_609 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_610 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_505, x_609, x_8, x_9, x_10, x_11, x_608);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; uint8_t x_612; 
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
x_612 = lean_unbox(x_611);
lean_dec(x_611);
if (x_612 == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; 
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_499);
lean_dec(x_486);
lean_dec(x_485);
x_613 = lean_ctor_get(x_610, 1);
lean_inc(x_613);
lean_dec(x_610);
x_614 = lean_st_ref_get(x_11, x_613);
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_615, 3);
lean_inc(x_616);
lean_dec(x_615);
x_617 = lean_ctor_get_uint8(x_616, sizeof(void*)*1);
lean_dec(x_616);
if (x_617 == 0)
{
uint8_t x_618; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_618 = !lean_is_exclusive(x_614);
if (x_618 == 0)
{
lean_object* x_619; 
x_619 = lean_ctor_get(x_614, 0);
lean_dec(x_619);
lean_ctor_set(x_614, 0, x_3);
return x_614;
}
else
{
lean_object* x_620; lean_object* x_621; 
x_620 = lean_ctor_get(x_614, 1);
lean_inc(x_620);
lean_dec(x_614);
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_3);
lean_ctor_set(x_621, 1, x_620);
return x_621;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; uint8_t x_625; 
x_622 = lean_ctor_get(x_614, 1);
lean_inc(x_622);
lean_dec(x_614);
x_623 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_604, x_8, x_9, x_10, x_11, x_622);
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_unbox(x_624);
lean_dec(x_624);
if (x_625 == 0)
{
uint8_t x_626; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_626 = !lean_is_exclusive(x_623);
if (x_626 == 0)
{
lean_object* x_627; 
x_627 = lean_ctor_get(x_623, 0);
lean_dec(x_627);
lean_ctor_set(x_623, 0, x_3);
return x_623;
}
else
{
lean_object* x_628; lean_object* x_629; 
x_628 = lean_ctor_get(x_623, 1);
lean_inc(x_628);
lean_dec(x_623);
x_629 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_629, 0, x_3);
lean_ctor_set(x_629, 1, x_628);
return x_629;
}
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; 
x_630 = lean_ctor_get(x_623, 1);
lean_inc(x_630);
lean_dec(x_623);
x_631 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_632 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_604, x_631, x_8, x_9, x_10, x_11, x_630);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_633 = !lean_is_exclusive(x_632);
if (x_633 == 0)
{
lean_object* x_634; 
x_634 = lean_ctor_get(x_632, 0);
lean_dec(x_634);
lean_ctor_set(x_632, 0, x_3);
return x_632;
}
else
{
lean_object* x_635; lean_object* x_636; 
x_635 = lean_ctor_get(x_632, 1);
lean_inc(x_635);
lean_dec(x_632);
x_636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_636, 0, x_3);
lean_ctor_set(x_636, 1, x_635);
return x_636;
}
}
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; 
x_637 = lean_ctor_get(x_610, 1);
lean_inc(x_637);
lean_dec(x_610);
x_638 = lean_st_ref_get(x_11, x_637);
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_639, 3);
lean_inc(x_640);
lean_dec(x_639);
x_641 = lean_ctor_get_uint8(x_640, sizeof(void*)*1);
lean_dec(x_640);
if (x_641 == 0)
{
lean_object* x_642; uint8_t x_643; 
x_642 = lean_ctor_get(x_638, 1);
lean_inc(x_642);
lean_dec(x_638);
x_643 = 0;
x_541 = x_643;
x_542 = x_642;
goto block_551;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; uint8_t x_648; 
x_644 = lean_ctor_get(x_638, 1);
lean_inc(x_644);
lean_dec(x_638);
x_645 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_604, x_8, x_9, x_10, x_11, x_644);
x_646 = lean_ctor_get(x_645, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_645, 1);
lean_inc(x_647);
lean_dec(x_645);
x_648 = lean_unbox(x_646);
lean_dec(x_646);
x_541 = x_648;
x_542 = x_647;
goto block_551;
}
}
}
else
{
uint8_t x_649; 
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_499);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_649 = !lean_is_exclusive(x_610);
if (x_649 == 0)
{
lean_object* x_650; 
x_650 = lean_ctor_get(x_610, 0);
lean_dec(x_650);
lean_ctor_set_tag(x_610, 0);
lean_ctor_set(x_610, 0, x_3);
return x_610;
}
else
{
lean_object* x_651; lean_object* x_652; 
x_651 = lean_ctor_get(x_610, 1);
lean_inc(x_651);
lean_dec(x_610);
x_652 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_652, 0, x_3);
lean_ctor_set(x_652, 1, x_651);
return x_652;
}
}
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_653 = lean_ctor_get(x_605, 1);
lean_inc(x_653);
lean_dec(x_605);
x_654 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_654, 0, x_539);
x_655 = l_Lean_KernelException_toMessageData___closed__15;
x_656 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_654);
x_657 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_657, 0, x_656);
lean_ctor_set(x_657, 1, x_655);
x_658 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_604, x_657, x_8, x_9, x_10, x_11, x_653);
x_659 = lean_ctor_get(x_658, 1);
lean_inc(x_659);
lean_dec(x_658);
x_660 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_661 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_505, x_660, x_8, x_9, x_10, x_11, x_659);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; uint8_t x_663; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_unbox(x_662);
lean_dec(x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; 
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_499);
lean_dec(x_486);
lean_dec(x_485);
x_664 = lean_ctor_get(x_661, 1);
lean_inc(x_664);
lean_dec(x_661);
x_665 = lean_st_ref_get(x_11, x_664);
x_666 = lean_ctor_get(x_665, 0);
lean_inc(x_666);
x_667 = lean_ctor_get(x_666, 3);
lean_inc(x_667);
lean_dec(x_666);
x_668 = lean_ctor_get_uint8(x_667, sizeof(void*)*1);
lean_dec(x_667);
if (x_668 == 0)
{
uint8_t x_669; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_669 = !lean_is_exclusive(x_665);
if (x_669 == 0)
{
lean_object* x_670; 
x_670 = lean_ctor_get(x_665, 0);
lean_dec(x_670);
lean_ctor_set(x_665, 0, x_3);
return x_665;
}
else
{
lean_object* x_671; lean_object* x_672; 
x_671 = lean_ctor_get(x_665, 1);
lean_inc(x_671);
lean_dec(x_665);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_3);
lean_ctor_set(x_672, 1, x_671);
return x_672;
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_673 = lean_ctor_get(x_665, 1);
lean_inc(x_673);
lean_dec(x_665);
x_674 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_604, x_8, x_9, x_10, x_11, x_673);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_unbox(x_675);
lean_dec(x_675);
if (x_676 == 0)
{
uint8_t x_677; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_677 = !lean_is_exclusive(x_674);
if (x_677 == 0)
{
lean_object* x_678; 
x_678 = lean_ctor_get(x_674, 0);
lean_dec(x_678);
lean_ctor_set(x_674, 0, x_3);
return x_674;
}
else
{
lean_object* x_679; lean_object* x_680; 
x_679 = lean_ctor_get(x_674, 1);
lean_inc(x_679);
lean_dec(x_674);
x_680 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_680, 0, x_3);
lean_ctor_set(x_680, 1, x_679);
return x_680;
}
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; 
x_681 = lean_ctor_get(x_674, 1);
lean_inc(x_681);
lean_dec(x_674);
x_682 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_683 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_604, x_682, x_8, x_9, x_10, x_11, x_681);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_684 = !lean_is_exclusive(x_683);
if (x_684 == 0)
{
lean_object* x_685; 
x_685 = lean_ctor_get(x_683, 0);
lean_dec(x_685);
lean_ctor_set(x_683, 0, x_3);
return x_683;
}
else
{
lean_object* x_686; lean_object* x_687; 
x_686 = lean_ctor_get(x_683, 1);
lean_inc(x_686);
lean_dec(x_683);
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_3);
lean_ctor_set(x_687, 1, x_686);
return x_687;
}
}
}
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; uint8_t x_692; 
x_688 = lean_ctor_get(x_661, 1);
lean_inc(x_688);
lean_dec(x_661);
x_689 = lean_st_ref_get(x_11, x_688);
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_690, 3);
lean_inc(x_691);
lean_dec(x_690);
x_692 = lean_ctor_get_uint8(x_691, sizeof(void*)*1);
lean_dec(x_691);
if (x_692 == 0)
{
lean_object* x_693; uint8_t x_694; 
x_693 = lean_ctor_get(x_689, 1);
lean_inc(x_693);
lean_dec(x_689);
x_694 = 0;
x_541 = x_694;
x_542 = x_693;
goto block_551;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; 
x_695 = lean_ctor_get(x_689, 1);
lean_inc(x_695);
lean_dec(x_689);
x_696 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_604, x_8, x_9, x_10, x_11, x_695);
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_unbox(x_697);
lean_dec(x_697);
x_541 = x_699;
x_542 = x_698;
goto block_551;
}
}
}
else
{
uint8_t x_700; 
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_499);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_700 = !lean_is_exclusive(x_661);
if (x_700 == 0)
{
lean_object* x_701; 
x_701 = lean_ctor_get(x_661, 0);
lean_dec(x_701);
lean_ctor_set_tag(x_661, 0);
lean_ctor_set(x_661, 0, x_3);
return x_661;
}
else
{
lean_object* x_702; lean_object* x_703; 
x_702 = lean_ctor_get(x_661, 1);
lean_inc(x_702);
lean_dec(x_661);
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_3);
lean_ctor_set(x_703, 1, x_702);
return x_703;
}
}
}
}
block_551:
{
if (x_541 == 0)
{
x_506 = x_542;
goto block_537;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_inc(x_502);
x_543 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_543, 0, x_502);
x_544 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_545 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_543);
x_546 = l_Lean_KernelException_toMessageData___closed__15;
x_547 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
x_548 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_549 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_548, x_547, x_8, x_9, x_10, x_11, x_542);
x_550 = lean_ctor_get(x_549, 1);
lean_inc(x_550);
lean_dec(x_549);
x_506 = x_550;
goto block_537;
}
}
}
else
{
uint8_t x_704; 
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_502);
lean_dec(x_499);
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_704 = !lean_is_exclusive(x_538);
if (x_704 == 0)
{
lean_object* x_705; 
x_705 = lean_ctor_get(x_538, 0);
lean_dec(x_705);
lean_ctor_set_tag(x_538, 0);
lean_ctor_set(x_538, 0, x_3);
return x_538;
}
else
{
lean_object* x_706; lean_object* x_707; 
x_706 = lean_ctor_get(x_538, 1);
lean_inc(x_706);
lean_dec(x_538);
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_3);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
block_537:
{
lean_object* x_507; uint8_t x_508; 
x_507 = lean_array_get_size(x_1);
x_508 = lean_nat_dec_lt(x_482, x_507);
if (x_508 == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_507);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_499)) {
 x_509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_509 = x_499;
}
lean_ctor_set(x_509, 0, x_502);
lean_ctor_set(x_509, 1, x_485);
if (lean_is_scalar(x_486)) {
 x_510 = lean_alloc_ctor(1, 1, 0);
} else {
 x_510 = x_486;
}
lean_ctor_set(x_510, 0, x_509);
if (lean_is_scalar(x_504)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_504;
}
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_506);
return x_511;
}
else
{
uint8_t x_512; 
x_512 = lean_nat_dec_le(x_507, x_507);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_507);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_499)) {
 x_513 = lean_alloc_ctor(0, 2, 0);
} else {
 x_513 = x_499;
}
lean_ctor_set(x_513, 0, x_502);
lean_ctor_set(x_513, 1, x_485);
if (lean_is_scalar(x_486)) {
 x_514 = lean_alloc_ctor(1, 1, 0);
} else {
 x_514 = x_486;
}
lean_ctor_set(x_514, 0, x_513);
if (lean_is_scalar(x_504)) {
 x_515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_515 = x_504;
}
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_506);
return x_515;
}
else
{
size_t x_516; size_t x_517; lean_object* x_518; 
lean_dec(x_504);
x_516 = 0;
x_517 = lean_usize_of_nat(x_507);
lean_dec(x_507);
lean_inc(x_502);
x_518 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_502, x_1, x_516, x_517, x_8, x_9, x_10, x_11, x_506);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; uint8_t x_520; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_unbox(x_519);
lean_dec(x_519);
if (x_520 == 0)
{
uint8_t x_521; 
lean_dec(x_3);
x_521 = !lean_is_exclusive(x_518);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_522 = lean_ctor_get(x_518, 0);
lean_dec(x_522);
if (lean_is_scalar(x_499)) {
 x_523 = lean_alloc_ctor(0, 2, 0);
} else {
 x_523 = x_499;
}
lean_ctor_set(x_523, 0, x_502);
lean_ctor_set(x_523, 1, x_485);
if (lean_is_scalar(x_486)) {
 x_524 = lean_alloc_ctor(1, 1, 0);
} else {
 x_524 = x_486;
}
lean_ctor_set(x_524, 0, x_523);
lean_ctor_set(x_518, 0, x_524);
return x_518;
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_525 = lean_ctor_get(x_518, 1);
lean_inc(x_525);
lean_dec(x_518);
if (lean_is_scalar(x_499)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_499;
}
lean_ctor_set(x_526, 0, x_502);
lean_ctor_set(x_526, 1, x_485);
if (lean_is_scalar(x_486)) {
 x_527 = lean_alloc_ctor(1, 1, 0);
} else {
 x_527 = x_486;
}
lean_ctor_set(x_527, 0, x_526);
x_528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_525);
return x_528;
}
}
else
{
uint8_t x_529; 
lean_dec(x_502);
lean_dec(x_499);
lean_dec(x_486);
lean_dec(x_485);
x_529 = !lean_is_exclusive(x_518);
if (x_529 == 0)
{
lean_object* x_530; 
x_530 = lean_ctor_get(x_518, 0);
lean_dec(x_530);
lean_ctor_set(x_518, 0, x_3);
return x_518;
}
else
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_ctor_get(x_518, 1);
lean_inc(x_531);
lean_dec(x_518);
x_532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_532, 0, x_3);
lean_ctor_set(x_532, 1, x_531);
return x_532;
}
}
}
else
{
uint8_t x_533; 
lean_dec(x_502);
lean_dec(x_499);
lean_dec(x_486);
lean_dec(x_485);
x_533 = !lean_is_exclusive(x_518);
if (x_533 == 0)
{
lean_object* x_534; 
x_534 = lean_ctor_get(x_518, 0);
lean_dec(x_534);
lean_ctor_set_tag(x_518, 0);
lean_ctor_set(x_518, 0, x_3);
return x_518;
}
else
{
lean_object* x_535; lean_object* x_536; 
x_535 = lean_ctor_get(x_518, 1);
lean_inc(x_535);
lean_dec(x_518);
x_536 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_536, 0, x_3);
lean_ctor_set(x_536, 1, x_535);
return x_536;
}
}
}
}
}
}
else
{
uint8_t x_708; 
lean_dec(x_486);
lean_dec(x_485);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_708 = !lean_is_exclusive(x_495);
if (x_708 == 0)
{
return x_495;
}
else
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; 
x_709 = lean_ctor_get(x_495, 0);
x_710 = lean_ctor_get(x_495, 1);
lean_inc(x_710);
lean_inc(x_709);
lean_dec(x_495);
x_711 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
return x_711;
}
}
}
}
}
}
case 3:
{
lean_object* x_712; 
lean_dec(x_7);
lean_dec(x_6);
x_712 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_3);
lean_ctor_set(x_713, 1, x_12);
return x_713;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_712, 0);
lean_inc(x_714);
lean_dec(x_712);
x_715 = lean_unsigned_to_nat(0u);
x_716 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_715);
if (lean_obj_tag(x_716) == 0)
{
lean_object* x_717; 
lean_dec(x_714);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_717 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_717, 0, x_3);
lean_ctor_set(x_717, 1, x_12);
return x_717;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_722; 
x_718 = lean_ctor_get(x_716, 0);
lean_inc(x_718);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 x_719 = x_716;
} else {
 lean_dec_ref(x_716);
 x_719 = lean_box(0);
}
x_720 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_714, x_8, x_9, x_10, x_11, x_12);
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_unbox(x_721);
lean_dec(x_721);
if (x_722 == 0)
{
uint8_t x_723; 
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_723 = !lean_is_exclusive(x_720);
if (x_723 == 0)
{
lean_object* x_724; 
x_724 = lean_ctor_get(x_720, 0);
lean_dec(x_724);
lean_ctor_set(x_720, 0, x_3);
return x_720;
}
else
{
lean_object* x_725; lean_object* x_726; 
x_725 = lean_ctor_get(x_720, 1);
lean_inc(x_725);
lean_dec(x_720);
x_726 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_726, 0, x_3);
lean_ctor_set(x_726, 1, x_725);
return x_726;
}
}
else
{
lean_object* x_727; lean_object* x_728; 
x_727 = lean_ctor_get(x_720, 1);
lean_inc(x_727);
lean_dec(x_720);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_728 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_718, x_8, x_9, x_10, x_11, x_727);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_771; 
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
lean_dec(x_728);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_732 = x_729;
} else {
 lean_dec_ref(x_729);
 x_732 = lean_box(0);
}
x_733 = lean_box(0);
lean_inc(x_8);
x_734 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_731, x_733, x_8, x_9, x_10, x_11, x_730);
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 x_737 = x_734;
} else {
 lean_dec_ref(x_734);
 x_737 = lean_box(0);
}
x_738 = l_Lean_Expr_mvarId_x21(x_735);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_771 = l_Lean_Meta_ppGoal(x_738, x_8, x_9, x_10, x_11, x_736);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; uint8_t x_774; lean_object* x_775; lean_object* x_785; lean_object* x_786; lean_object* x_787; uint8_t x_788; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
lean_dec(x_771);
x_785 = lean_st_ref_get(x_11, x_773);
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_786, 3);
lean_inc(x_787);
lean_dec(x_786);
x_788 = lean_ctor_get_uint8(x_787, sizeof(void*)*1);
lean_dec(x_787);
if (x_788 == 0)
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; 
lean_dec(x_772);
x_789 = lean_ctor_get(x_785, 1);
lean_inc(x_789);
lean_dec(x_785);
x_790 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_791 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_738, x_790, x_8, x_9, x_10, x_11, x_789);
if (lean_obj_tag(x_791) == 0)
{
lean_object* x_792; uint8_t x_793; 
x_792 = lean_ctor_get(x_791, 0);
lean_inc(x_792);
x_793 = lean_unbox(x_792);
lean_dec(x_792);
if (x_793 == 0)
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; uint8_t x_798; 
lean_dec(x_737);
lean_dec(x_735);
lean_dec(x_732);
lean_dec(x_719);
lean_dec(x_718);
x_794 = lean_ctor_get(x_791, 1);
lean_inc(x_794);
lean_dec(x_791);
x_795 = lean_st_ref_get(x_11, x_794);
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_796, 3);
lean_inc(x_797);
lean_dec(x_796);
x_798 = lean_ctor_get_uint8(x_797, sizeof(void*)*1);
lean_dec(x_797);
if (x_798 == 0)
{
uint8_t x_799; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_799 = !lean_is_exclusive(x_795);
if (x_799 == 0)
{
lean_object* x_800; 
x_800 = lean_ctor_get(x_795, 0);
lean_dec(x_800);
lean_ctor_set(x_795, 0, x_3);
return x_795;
}
else
{
lean_object* x_801; lean_object* x_802; 
x_801 = lean_ctor_get(x_795, 1);
lean_inc(x_801);
lean_dec(x_795);
x_802 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_802, 0, x_3);
lean_ctor_set(x_802, 1, x_801);
return x_802;
}
}
else
{
lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; uint8_t x_807; 
x_803 = lean_ctor_get(x_795, 1);
lean_inc(x_803);
lean_dec(x_795);
x_804 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_805 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_804, x_8, x_9, x_10, x_11, x_803);
x_806 = lean_ctor_get(x_805, 0);
lean_inc(x_806);
x_807 = lean_unbox(x_806);
lean_dec(x_806);
if (x_807 == 0)
{
uint8_t x_808; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_808 = !lean_is_exclusive(x_805);
if (x_808 == 0)
{
lean_object* x_809; 
x_809 = lean_ctor_get(x_805, 0);
lean_dec(x_809);
lean_ctor_set(x_805, 0, x_3);
return x_805;
}
else
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_ctor_get(x_805, 1);
lean_inc(x_810);
lean_dec(x_805);
x_811 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_811, 0, x_3);
lean_ctor_set(x_811, 1, x_810);
return x_811;
}
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; 
x_812 = lean_ctor_get(x_805, 1);
lean_inc(x_812);
lean_dec(x_805);
x_813 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_814 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_804, x_813, x_8, x_9, x_10, x_11, x_812);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_815 = !lean_is_exclusive(x_814);
if (x_815 == 0)
{
lean_object* x_816; 
x_816 = lean_ctor_get(x_814, 0);
lean_dec(x_816);
lean_ctor_set(x_814, 0, x_3);
return x_814;
}
else
{
lean_object* x_817; lean_object* x_818; 
x_817 = lean_ctor_get(x_814, 1);
lean_inc(x_817);
lean_dec(x_814);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_3);
lean_ctor_set(x_818, 1, x_817);
return x_818;
}
}
}
}
else
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; uint8_t x_823; 
x_819 = lean_ctor_get(x_791, 1);
lean_inc(x_819);
lean_dec(x_791);
x_820 = lean_st_ref_get(x_11, x_819);
x_821 = lean_ctor_get(x_820, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_821, 3);
lean_inc(x_822);
lean_dec(x_821);
x_823 = lean_ctor_get_uint8(x_822, sizeof(void*)*1);
lean_dec(x_822);
if (x_823 == 0)
{
lean_object* x_824; uint8_t x_825; 
x_824 = lean_ctor_get(x_820, 1);
lean_inc(x_824);
lean_dec(x_820);
x_825 = 0;
x_774 = x_825;
x_775 = x_824;
goto block_784;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; 
x_826 = lean_ctor_get(x_820, 1);
lean_inc(x_826);
lean_dec(x_820);
x_827 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_828 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_827, x_8, x_9, x_10, x_11, x_826);
x_829 = lean_ctor_get(x_828, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_828, 1);
lean_inc(x_830);
lean_dec(x_828);
x_831 = lean_unbox(x_829);
lean_dec(x_829);
x_774 = x_831;
x_775 = x_830;
goto block_784;
}
}
}
else
{
uint8_t x_832; 
lean_dec(x_737);
lean_dec(x_735);
lean_dec(x_732);
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_832 = !lean_is_exclusive(x_791);
if (x_832 == 0)
{
lean_object* x_833; 
x_833 = lean_ctor_get(x_791, 0);
lean_dec(x_833);
lean_ctor_set_tag(x_791, 0);
lean_ctor_set(x_791, 0, x_3);
return x_791;
}
else
{
lean_object* x_834; lean_object* x_835; 
x_834 = lean_ctor_get(x_791, 1);
lean_inc(x_834);
lean_dec(x_791);
x_835 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_835, 0, x_3);
lean_ctor_set(x_835, 1, x_834);
return x_835;
}
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; uint8_t x_840; 
x_836 = lean_ctor_get(x_785, 1);
lean_inc(x_836);
lean_dec(x_785);
x_837 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_838 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_837, x_8, x_9, x_10, x_11, x_836);
x_839 = lean_ctor_get(x_838, 0);
lean_inc(x_839);
x_840 = lean_unbox(x_839);
lean_dec(x_839);
if (x_840 == 0)
{
lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_772);
x_841 = lean_ctor_get(x_838, 1);
lean_inc(x_841);
lean_dec(x_838);
x_842 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_843 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_738, x_842, x_8, x_9, x_10, x_11, x_841);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_844; uint8_t x_845; 
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
x_845 = lean_unbox(x_844);
lean_dec(x_844);
if (x_845 == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; uint8_t x_850; 
lean_dec(x_737);
lean_dec(x_735);
lean_dec(x_732);
lean_dec(x_719);
lean_dec(x_718);
x_846 = lean_ctor_get(x_843, 1);
lean_inc(x_846);
lean_dec(x_843);
x_847 = lean_st_ref_get(x_11, x_846);
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_848, 3);
lean_inc(x_849);
lean_dec(x_848);
x_850 = lean_ctor_get_uint8(x_849, sizeof(void*)*1);
lean_dec(x_849);
if (x_850 == 0)
{
uint8_t x_851; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_851 = !lean_is_exclusive(x_847);
if (x_851 == 0)
{
lean_object* x_852; 
x_852 = lean_ctor_get(x_847, 0);
lean_dec(x_852);
lean_ctor_set(x_847, 0, x_3);
return x_847;
}
else
{
lean_object* x_853; lean_object* x_854; 
x_853 = lean_ctor_get(x_847, 1);
lean_inc(x_853);
lean_dec(x_847);
x_854 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_854, 0, x_3);
lean_ctor_set(x_854, 1, x_853);
return x_854;
}
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; uint8_t x_858; 
x_855 = lean_ctor_get(x_847, 1);
lean_inc(x_855);
lean_dec(x_847);
x_856 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_837, x_8, x_9, x_10, x_11, x_855);
x_857 = lean_ctor_get(x_856, 0);
lean_inc(x_857);
x_858 = lean_unbox(x_857);
lean_dec(x_857);
if (x_858 == 0)
{
uint8_t x_859; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_859 = !lean_is_exclusive(x_856);
if (x_859 == 0)
{
lean_object* x_860; 
x_860 = lean_ctor_get(x_856, 0);
lean_dec(x_860);
lean_ctor_set(x_856, 0, x_3);
return x_856;
}
else
{
lean_object* x_861; lean_object* x_862; 
x_861 = lean_ctor_get(x_856, 1);
lean_inc(x_861);
lean_dec(x_856);
x_862 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_862, 0, x_3);
lean_ctor_set(x_862, 1, x_861);
return x_862;
}
}
else
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; uint8_t x_866; 
x_863 = lean_ctor_get(x_856, 1);
lean_inc(x_863);
lean_dec(x_856);
x_864 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_865 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_837, x_864, x_8, x_9, x_10, x_11, x_863);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_866 = !lean_is_exclusive(x_865);
if (x_866 == 0)
{
lean_object* x_867; 
x_867 = lean_ctor_get(x_865, 0);
lean_dec(x_867);
lean_ctor_set(x_865, 0, x_3);
return x_865;
}
else
{
lean_object* x_868; lean_object* x_869; 
x_868 = lean_ctor_get(x_865, 1);
lean_inc(x_868);
lean_dec(x_865);
x_869 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_869, 0, x_3);
lean_ctor_set(x_869, 1, x_868);
return x_869;
}
}
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; uint8_t x_874; 
x_870 = lean_ctor_get(x_843, 1);
lean_inc(x_870);
lean_dec(x_843);
x_871 = lean_st_ref_get(x_11, x_870);
x_872 = lean_ctor_get(x_871, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_872, 3);
lean_inc(x_873);
lean_dec(x_872);
x_874 = lean_ctor_get_uint8(x_873, sizeof(void*)*1);
lean_dec(x_873);
if (x_874 == 0)
{
lean_object* x_875; uint8_t x_876; 
x_875 = lean_ctor_get(x_871, 1);
lean_inc(x_875);
lean_dec(x_871);
x_876 = 0;
x_774 = x_876;
x_775 = x_875;
goto block_784;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; uint8_t x_881; 
x_877 = lean_ctor_get(x_871, 1);
lean_inc(x_877);
lean_dec(x_871);
x_878 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_837, x_8, x_9, x_10, x_11, x_877);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_unbox(x_879);
lean_dec(x_879);
x_774 = x_881;
x_775 = x_880;
goto block_784;
}
}
}
else
{
uint8_t x_882; 
lean_dec(x_737);
lean_dec(x_735);
lean_dec(x_732);
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_882 = !lean_is_exclusive(x_843);
if (x_882 == 0)
{
lean_object* x_883; 
x_883 = lean_ctor_get(x_843, 0);
lean_dec(x_883);
lean_ctor_set_tag(x_843, 0);
lean_ctor_set(x_843, 0, x_3);
return x_843;
}
else
{
lean_object* x_884; lean_object* x_885; 
x_884 = lean_ctor_get(x_843, 1);
lean_inc(x_884);
lean_dec(x_843);
x_885 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_885, 0, x_3);
lean_ctor_set(x_885, 1, x_884);
return x_885;
}
}
}
else
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_886 = lean_ctor_get(x_838, 1);
lean_inc(x_886);
lean_dec(x_838);
x_887 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_887, 0, x_772);
x_888 = l_Lean_KernelException_toMessageData___closed__15;
x_889 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_887);
x_890 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_890, 0, x_889);
lean_ctor_set(x_890, 1, x_888);
x_891 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_837, x_890, x_8, x_9, x_10, x_11, x_886);
x_892 = lean_ctor_get(x_891, 1);
lean_inc(x_892);
lean_dec(x_891);
x_893 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_894 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_738, x_893, x_8, x_9, x_10, x_11, x_892);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; uint8_t x_896; 
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_unbox(x_895);
lean_dec(x_895);
if (x_896 == 0)
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; uint8_t x_901; 
lean_dec(x_737);
lean_dec(x_735);
lean_dec(x_732);
lean_dec(x_719);
lean_dec(x_718);
x_897 = lean_ctor_get(x_894, 1);
lean_inc(x_897);
lean_dec(x_894);
x_898 = lean_st_ref_get(x_11, x_897);
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_899, 3);
lean_inc(x_900);
lean_dec(x_899);
x_901 = lean_ctor_get_uint8(x_900, sizeof(void*)*1);
lean_dec(x_900);
if (x_901 == 0)
{
uint8_t x_902; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_902 = !lean_is_exclusive(x_898);
if (x_902 == 0)
{
lean_object* x_903; 
x_903 = lean_ctor_get(x_898, 0);
lean_dec(x_903);
lean_ctor_set(x_898, 0, x_3);
return x_898;
}
else
{
lean_object* x_904; lean_object* x_905; 
x_904 = lean_ctor_get(x_898, 1);
lean_inc(x_904);
lean_dec(x_898);
x_905 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_905, 0, x_3);
lean_ctor_set(x_905, 1, x_904);
return x_905;
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; uint8_t x_909; 
x_906 = lean_ctor_get(x_898, 1);
lean_inc(x_906);
lean_dec(x_898);
x_907 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_837, x_8, x_9, x_10, x_11, x_906);
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
x_909 = lean_unbox(x_908);
lean_dec(x_908);
if (x_909 == 0)
{
uint8_t x_910; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_910 = !lean_is_exclusive(x_907);
if (x_910 == 0)
{
lean_object* x_911; 
x_911 = lean_ctor_get(x_907, 0);
lean_dec(x_911);
lean_ctor_set(x_907, 0, x_3);
return x_907;
}
else
{
lean_object* x_912; lean_object* x_913; 
x_912 = lean_ctor_get(x_907, 1);
lean_inc(x_912);
lean_dec(x_907);
x_913 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_913, 0, x_3);
lean_ctor_set(x_913, 1, x_912);
return x_913;
}
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; uint8_t x_917; 
x_914 = lean_ctor_get(x_907, 1);
lean_inc(x_914);
lean_dec(x_907);
x_915 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_916 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_837, x_915, x_8, x_9, x_10, x_11, x_914);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_917 = !lean_is_exclusive(x_916);
if (x_917 == 0)
{
lean_object* x_918; 
x_918 = lean_ctor_get(x_916, 0);
lean_dec(x_918);
lean_ctor_set(x_916, 0, x_3);
return x_916;
}
else
{
lean_object* x_919; lean_object* x_920; 
x_919 = lean_ctor_get(x_916, 1);
lean_inc(x_919);
lean_dec(x_916);
x_920 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_920, 0, x_3);
lean_ctor_set(x_920, 1, x_919);
return x_920;
}
}
}
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; uint8_t x_925; 
x_921 = lean_ctor_get(x_894, 1);
lean_inc(x_921);
lean_dec(x_894);
x_922 = lean_st_ref_get(x_11, x_921);
x_923 = lean_ctor_get(x_922, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_923, 3);
lean_inc(x_924);
lean_dec(x_923);
x_925 = lean_ctor_get_uint8(x_924, sizeof(void*)*1);
lean_dec(x_924);
if (x_925 == 0)
{
lean_object* x_926; uint8_t x_927; 
x_926 = lean_ctor_get(x_922, 1);
lean_inc(x_926);
lean_dec(x_922);
x_927 = 0;
x_774 = x_927;
x_775 = x_926;
goto block_784;
}
else
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; 
x_928 = lean_ctor_get(x_922, 1);
lean_inc(x_928);
lean_dec(x_922);
x_929 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_837, x_8, x_9, x_10, x_11, x_928);
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_929, 1);
lean_inc(x_931);
lean_dec(x_929);
x_932 = lean_unbox(x_930);
lean_dec(x_930);
x_774 = x_932;
x_775 = x_931;
goto block_784;
}
}
}
else
{
uint8_t x_933; 
lean_dec(x_737);
lean_dec(x_735);
lean_dec(x_732);
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_933 = !lean_is_exclusive(x_894);
if (x_933 == 0)
{
lean_object* x_934; 
x_934 = lean_ctor_get(x_894, 0);
lean_dec(x_934);
lean_ctor_set_tag(x_894, 0);
lean_ctor_set(x_894, 0, x_3);
return x_894;
}
else
{
lean_object* x_935; lean_object* x_936; 
x_935 = lean_ctor_get(x_894, 1);
lean_inc(x_935);
lean_dec(x_894);
x_936 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_936, 0, x_3);
lean_ctor_set(x_936, 1, x_935);
return x_936;
}
}
}
}
block_784:
{
if (x_774 == 0)
{
x_739 = x_775;
goto block_770;
}
else
{
lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
lean_inc(x_735);
x_776 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_776, 0, x_735);
x_777 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_778 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_778, 0, x_777);
lean_ctor_set(x_778, 1, x_776);
x_779 = l_Lean_KernelException_toMessageData___closed__15;
x_780 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
x_781 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_782 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_781, x_780, x_8, x_9, x_10, x_11, x_775);
x_783 = lean_ctor_get(x_782, 1);
lean_inc(x_783);
lean_dec(x_782);
x_739 = x_783;
goto block_770;
}
}
}
else
{
uint8_t x_937; 
lean_dec(x_738);
lean_dec(x_737);
lean_dec(x_735);
lean_dec(x_732);
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_937 = !lean_is_exclusive(x_771);
if (x_937 == 0)
{
lean_object* x_938; 
x_938 = lean_ctor_get(x_771, 0);
lean_dec(x_938);
lean_ctor_set_tag(x_771, 0);
lean_ctor_set(x_771, 0, x_3);
return x_771;
}
else
{
lean_object* x_939; lean_object* x_940; 
x_939 = lean_ctor_get(x_771, 1);
lean_inc(x_939);
lean_dec(x_771);
x_940 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_940, 0, x_3);
lean_ctor_set(x_940, 1, x_939);
return x_940;
}
}
block_770:
{
lean_object* x_740; uint8_t x_741; 
x_740 = lean_array_get_size(x_1);
x_741 = lean_nat_dec_lt(x_715, x_740);
if (x_741 == 0)
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_740);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_732)) {
 x_742 = lean_alloc_ctor(0, 2, 0);
} else {
 x_742 = x_732;
}
lean_ctor_set(x_742, 0, x_735);
lean_ctor_set(x_742, 1, x_718);
if (lean_is_scalar(x_719)) {
 x_743 = lean_alloc_ctor(1, 1, 0);
} else {
 x_743 = x_719;
}
lean_ctor_set(x_743, 0, x_742);
if (lean_is_scalar(x_737)) {
 x_744 = lean_alloc_ctor(0, 2, 0);
} else {
 x_744 = x_737;
}
lean_ctor_set(x_744, 0, x_743);
lean_ctor_set(x_744, 1, x_739);
return x_744;
}
else
{
uint8_t x_745; 
x_745 = lean_nat_dec_le(x_740, x_740);
if (x_745 == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_dec(x_740);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_732)) {
 x_746 = lean_alloc_ctor(0, 2, 0);
} else {
 x_746 = x_732;
}
lean_ctor_set(x_746, 0, x_735);
lean_ctor_set(x_746, 1, x_718);
if (lean_is_scalar(x_719)) {
 x_747 = lean_alloc_ctor(1, 1, 0);
} else {
 x_747 = x_719;
}
lean_ctor_set(x_747, 0, x_746);
if (lean_is_scalar(x_737)) {
 x_748 = lean_alloc_ctor(0, 2, 0);
} else {
 x_748 = x_737;
}
lean_ctor_set(x_748, 0, x_747);
lean_ctor_set(x_748, 1, x_739);
return x_748;
}
else
{
size_t x_749; size_t x_750; lean_object* x_751; 
lean_dec(x_737);
x_749 = 0;
x_750 = lean_usize_of_nat(x_740);
lean_dec(x_740);
lean_inc(x_735);
x_751 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_735, x_1, x_749, x_750, x_8, x_9, x_10, x_11, x_739);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; uint8_t x_753; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_unbox(x_752);
lean_dec(x_752);
if (x_753 == 0)
{
uint8_t x_754; 
lean_dec(x_3);
x_754 = !lean_is_exclusive(x_751);
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_755 = lean_ctor_get(x_751, 0);
lean_dec(x_755);
if (lean_is_scalar(x_732)) {
 x_756 = lean_alloc_ctor(0, 2, 0);
} else {
 x_756 = x_732;
}
lean_ctor_set(x_756, 0, x_735);
lean_ctor_set(x_756, 1, x_718);
if (lean_is_scalar(x_719)) {
 x_757 = lean_alloc_ctor(1, 1, 0);
} else {
 x_757 = x_719;
}
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_751, 0, x_757);
return x_751;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_758 = lean_ctor_get(x_751, 1);
lean_inc(x_758);
lean_dec(x_751);
if (lean_is_scalar(x_732)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_732;
}
lean_ctor_set(x_759, 0, x_735);
lean_ctor_set(x_759, 1, x_718);
if (lean_is_scalar(x_719)) {
 x_760 = lean_alloc_ctor(1, 1, 0);
} else {
 x_760 = x_719;
}
lean_ctor_set(x_760, 0, x_759);
x_761 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_761, 0, x_760);
lean_ctor_set(x_761, 1, x_758);
return x_761;
}
}
else
{
uint8_t x_762; 
lean_dec(x_735);
lean_dec(x_732);
lean_dec(x_719);
lean_dec(x_718);
x_762 = !lean_is_exclusive(x_751);
if (x_762 == 0)
{
lean_object* x_763; 
x_763 = lean_ctor_get(x_751, 0);
lean_dec(x_763);
lean_ctor_set(x_751, 0, x_3);
return x_751;
}
else
{
lean_object* x_764; lean_object* x_765; 
x_764 = lean_ctor_get(x_751, 1);
lean_inc(x_764);
lean_dec(x_751);
x_765 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_765, 0, x_3);
lean_ctor_set(x_765, 1, x_764);
return x_765;
}
}
}
else
{
uint8_t x_766; 
lean_dec(x_735);
lean_dec(x_732);
lean_dec(x_719);
lean_dec(x_718);
x_766 = !lean_is_exclusive(x_751);
if (x_766 == 0)
{
lean_object* x_767; 
x_767 = lean_ctor_get(x_751, 0);
lean_dec(x_767);
lean_ctor_set_tag(x_751, 0);
lean_ctor_set(x_751, 0, x_3);
return x_751;
}
else
{
lean_object* x_768; lean_object* x_769; 
x_768 = lean_ctor_get(x_751, 1);
lean_inc(x_768);
lean_dec(x_751);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_3);
lean_ctor_set(x_769, 1, x_768);
return x_769;
}
}
}
}
}
}
else
{
uint8_t x_941; 
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_941 = !lean_is_exclusive(x_728);
if (x_941 == 0)
{
return x_728;
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_942 = lean_ctor_get(x_728, 0);
x_943 = lean_ctor_get(x_728, 1);
lean_inc(x_943);
lean_inc(x_942);
lean_dec(x_728);
x_944 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_944, 0, x_942);
lean_ctor_set(x_944, 1, x_943);
return x_944;
}
}
}
}
}
}
case 4:
{
lean_object* x_945; 
lean_dec(x_7);
lean_dec(x_6);
x_945 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_946 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_946, 0, x_3);
lean_ctor_set(x_946, 1, x_12);
return x_946;
}
else
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; 
x_947 = lean_ctor_get(x_945, 0);
lean_inc(x_947);
lean_dec(x_945);
x_948 = lean_unsigned_to_nat(0u);
x_949 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_948);
if (lean_obj_tag(x_949) == 0)
{
lean_object* x_950; 
lean_dec(x_947);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_950 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_950, 0, x_3);
lean_ctor_set(x_950, 1, x_12);
return x_950;
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; uint8_t x_955; 
x_951 = lean_ctor_get(x_949, 0);
lean_inc(x_951);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 x_952 = x_949;
} else {
 lean_dec_ref(x_949);
 x_952 = lean_box(0);
}
x_953 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_947, x_8, x_9, x_10, x_11, x_12);
x_954 = lean_ctor_get(x_953, 0);
lean_inc(x_954);
x_955 = lean_unbox(x_954);
lean_dec(x_954);
if (x_955 == 0)
{
uint8_t x_956; 
lean_dec(x_952);
lean_dec(x_951);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_956 = !lean_is_exclusive(x_953);
if (x_956 == 0)
{
lean_object* x_957; 
x_957 = lean_ctor_get(x_953, 0);
lean_dec(x_957);
lean_ctor_set(x_953, 0, x_3);
return x_953;
}
else
{
lean_object* x_958; lean_object* x_959; 
x_958 = lean_ctor_get(x_953, 1);
lean_inc(x_958);
lean_dec(x_953);
x_959 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_959, 0, x_3);
lean_ctor_set(x_959, 1, x_958);
return x_959;
}
}
else
{
lean_object* x_960; lean_object* x_961; 
x_960 = lean_ctor_get(x_953, 1);
lean_inc(x_960);
lean_dec(x_953);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_961 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_951, x_8, x_9, x_10, x_11, x_960);
if (lean_obj_tag(x_961) == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_1004; 
x_962 = lean_ctor_get(x_961, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
lean_dec(x_961);
x_964 = lean_ctor_get(x_962, 1);
lean_inc(x_964);
if (lean_is_exclusive(x_962)) {
 lean_ctor_release(x_962, 0);
 lean_ctor_release(x_962, 1);
 x_965 = x_962;
} else {
 lean_dec_ref(x_962);
 x_965 = lean_box(0);
}
x_966 = lean_box(0);
lean_inc(x_8);
x_967 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_964, x_966, x_8, x_9, x_10, x_11, x_963);
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
if (lean_is_exclusive(x_967)) {
 lean_ctor_release(x_967, 0);
 lean_ctor_release(x_967, 1);
 x_970 = x_967;
} else {
 lean_dec_ref(x_967);
 x_970 = lean_box(0);
}
x_971 = l_Lean_Expr_mvarId_x21(x_968);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1004 = l_Lean_Meta_ppGoal(x_971, x_8, x_9, x_10, x_11, x_969);
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; lean_object* x_1006; uint8_t x_1007; lean_object* x_1008; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; uint8_t x_1021; 
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_1004, 1);
lean_inc(x_1006);
lean_dec(x_1004);
x_1018 = lean_st_ref_get(x_11, x_1006);
x_1019 = lean_ctor_get(x_1018, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1019, 3);
lean_inc(x_1020);
lean_dec(x_1019);
x_1021 = lean_ctor_get_uint8(x_1020, sizeof(void*)*1);
lean_dec(x_1020);
if (x_1021 == 0)
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
lean_dec(x_1005);
x_1022 = lean_ctor_get(x_1018, 1);
lean_inc(x_1022);
lean_dec(x_1018);
x_1023 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1024 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_971, x_1023, x_8, x_9, x_10, x_11, x_1022);
if (lean_obj_tag(x_1024) == 0)
{
lean_object* x_1025; uint8_t x_1026; 
x_1025 = lean_ctor_get(x_1024, 0);
lean_inc(x_1025);
x_1026 = lean_unbox(x_1025);
lean_dec(x_1025);
if (x_1026 == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; uint8_t x_1031; 
lean_dec(x_970);
lean_dec(x_968);
lean_dec(x_965);
lean_dec(x_952);
lean_dec(x_951);
x_1027 = lean_ctor_get(x_1024, 1);
lean_inc(x_1027);
lean_dec(x_1024);
x_1028 = lean_st_ref_get(x_11, x_1027);
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1029, 3);
lean_inc(x_1030);
lean_dec(x_1029);
x_1031 = lean_ctor_get_uint8(x_1030, sizeof(void*)*1);
lean_dec(x_1030);
if (x_1031 == 0)
{
uint8_t x_1032; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1032 = !lean_is_exclusive(x_1028);
if (x_1032 == 0)
{
lean_object* x_1033; 
x_1033 = lean_ctor_get(x_1028, 0);
lean_dec(x_1033);
lean_ctor_set(x_1028, 0, x_3);
return x_1028;
}
else
{
lean_object* x_1034; lean_object* x_1035; 
x_1034 = lean_ctor_get(x_1028, 1);
lean_inc(x_1034);
lean_dec(x_1028);
x_1035 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1035, 0, x_3);
lean_ctor_set(x_1035, 1, x_1034);
return x_1035;
}
}
else
{
lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; uint8_t x_1040; 
x_1036 = lean_ctor_get(x_1028, 1);
lean_inc(x_1036);
lean_dec(x_1028);
x_1037 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1038 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1037, x_8, x_9, x_10, x_11, x_1036);
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_unbox(x_1039);
lean_dec(x_1039);
if (x_1040 == 0)
{
uint8_t x_1041; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1041 = !lean_is_exclusive(x_1038);
if (x_1041 == 0)
{
lean_object* x_1042; 
x_1042 = lean_ctor_get(x_1038, 0);
lean_dec(x_1042);
lean_ctor_set(x_1038, 0, x_3);
return x_1038;
}
else
{
lean_object* x_1043; lean_object* x_1044; 
x_1043 = lean_ctor_get(x_1038, 1);
lean_inc(x_1043);
lean_dec(x_1038);
x_1044 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1044, 0, x_3);
lean_ctor_set(x_1044, 1, x_1043);
return x_1044;
}
}
else
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; uint8_t x_1048; 
x_1045 = lean_ctor_get(x_1038, 1);
lean_inc(x_1045);
lean_dec(x_1038);
x_1046 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1047 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1037, x_1046, x_8, x_9, x_10, x_11, x_1045);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1048 = !lean_is_exclusive(x_1047);
if (x_1048 == 0)
{
lean_object* x_1049; 
x_1049 = lean_ctor_get(x_1047, 0);
lean_dec(x_1049);
lean_ctor_set(x_1047, 0, x_3);
return x_1047;
}
else
{
lean_object* x_1050; lean_object* x_1051; 
x_1050 = lean_ctor_get(x_1047, 1);
lean_inc(x_1050);
lean_dec(x_1047);
x_1051 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1051, 0, x_3);
lean_ctor_set(x_1051, 1, x_1050);
return x_1051;
}
}
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; uint8_t x_1056; 
x_1052 = lean_ctor_get(x_1024, 1);
lean_inc(x_1052);
lean_dec(x_1024);
x_1053 = lean_st_ref_get(x_11, x_1052);
x_1054 = lean_ctor_get(x_1053, 0);
lean_inc(x_1054);
x_1055 = lean_ctor_get(x_1054, 3);
lean_inc(x_1055);
lean_dec(x_1054);
x_1056 = lean_ctor_get_uint8(x_1055, sizeof(void*)*1);
lean_dec(x_1055);
if (x_1056 == 0)
{
lean_object* x_1057; uint8_t x_1058; 
x_1057 = lean_ctor_get(x_1053, 1);
lean_inc(x_1057);
lean_dec(x_1053);
x_1058 = 0;
x_1007 = x_1058;
x_1008 = x_1057;
goto block_1017;
}
else
{
lean_object* x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; uint8_t x_1064; 
x_1059 = lean_ctor_get(x_1053, 1);
lean_inc(x_1059);
lean_dec(x_1053);
x_1060 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1061 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1060, x_8, x_9, x_10, x_11, x_1059);
x_1062 = lean_ctor_get(x_1061, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1061, 1);
lean_inc(x_1063);
lean_dec(x_1061);
x_1064 = lean_unbox(x_1062);
lean_dec(x_1062);
x_1007 = x_1064;
x_1008 = x_1063;
goto block_1017;
}
}
}
else
{
uint8_t x_1065; 
lean_dec(x_970);
lean_dec(x_968);
lean_dec(x_965);
lean_dec(x_952);
lean_dec(x_951);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1065 = !lean_is_exclusive(x_1024);
if (x_1065 == 0)
{
lean_object* x_1066; 
x_1066 = lean_ctor_get(x_1024, 0);
lean_dec(x_1066);
lean_ctor_set_tag(x_1024, 0);
lean_ctor_set(x_1024, 0, x_3);
return x_1024;
}
else
{
lean_object* x_1067; lean_object* x_1068; 
x_1067 = lean_ctor_get(x_1024, 1);
lean_inc(x_1067);
lean_dec(x_1024);
x_1068 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1068, 0, x_3);
lean_ctor_set(x_1068, 1, x_1067);
return x_1068;
}
}
}
else
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; uint8_t x_1073; 
x_1069 = lean_ctor_get(x_1018, 1);
lean_inc(x_1069);
lean_dec(x_1018);
x_1070 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1071 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1070, x_8, x_9, x_10, x_11, x_1069);
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_unbox(x_1072);
lean_dec(x_1072);
if (x_1073 == 0)
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
lean_dec(x_1005);
x_1074 = lean_ctor_get(x_1071, 1);
lean_inc(x_1074);
lean_dec(x_1071);
x_1075 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1076 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_971, x_1075, x_8, x_9, x_10, x_11, x_1074);
if (lean_obj_tag(x_1076) == 0)
{
lean_object* x_1077; uint8_t x_1078; 
x_1077 = lean_ctor_get(x_1076, 0);
lean_inc(x_1077);
x_1078 = lean_unbox(x_1077);
lean_dec(x_1077);
if (x_1078 == 0)
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; uint8_t x_1083; 
lean_dec(x_970);
lean_dec(x_968);
lean_dec(x_965);
lean_dec(x_952);
lean_dec(x_951);
x_1079 = lean_ctor_get(x_1076, 1);
lean_inc(x_1079);
lean_dec(x_1076);
x_1080 = lean_st_ref_get(x_11, x_1079);
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1081, 3);
lean_inc(x_1082);
lean_dec(x_1081);
x_1083 = lean_ctor_get_uint8(x_1082, sizeof(void*)*1);
lean_dec(x_1082);
if (x_1083 == 0)
{
uint8_t x_1084; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1084 = !lean_is_exclusive(x_1080);
if (x_1084 == 0)
{
lean_object* x_1085; 
x_1085 = lean_ctor_get(x_1080, 0);
lean_dec(x_1085);
lean_ctor_set(x_1080, 0, x_3);
return x_1080;
}
else
{
lean_object* x_1086; lean_object* x_1087; 
x_1086 = lean_ctor_get(x_1080, 1);
lean_inc(x_1086);
lean_dec(x_1080);
x_1087 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1087, 0, x_3);
lean_ctor_set(x_1087, 1, x_1086);
return x_1087;
}
}
else
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; uint8_t x_1091; 
x_1088 = lean_ctor_get(x_1080, 1);
lean_inc(x_1088);
lean_dec(x_1080);
x_1089 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1070, x_8, x_9, x_10, x_11, x_1088);
x_1090 = lean_ctor_get(x_1089, 0);
lean_inc(x_1090);
x_1091 = lean_unbox(x_1090);
lean_dec(x_1090);
if (x_1091 == 0)
{
uint8_t x_1092; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1092 = !lean_is_exclusive(x_1089);
if (x_1092 == 0)
{
lean_object* x_1093; 
x_1093 = lean_ctor_get(x_1089, 0);
lean_dec(x_1093);
lean_ctor_set(x_1089, 0, x_3);
return x_1089;
}
else
{
lean_object* x_1094; lean_object* x_1095; 
x_1094 = lean_ctor_get(x_1089, 1);
lean_inc(x_1094);
lean_dec(x_1089);
x_1095 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1095, 0, x_3);
lean_ctor_set(x_1095, 1, x_1094);
return x_1095;
}
}
else
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; uint8_t x_1099; 
x_1096 = lean_ctor_get(x_1089, 1);
lean_inc(x_1096);
lean_dec(x_1089);
x_1097 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1098 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1070, x_1097, x_8, x_9, x_10, x_11, x_1096);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1099 = !lean_is_exclusive(x_1098);
if (x_1099 == 0)
{
lean_object* x_1100; 
x_1100 = lean_ctor_get(x_1098, 0);
lean_dec(x_1100);
lean_ctor_set(x_1098, 0, x_3);
return x_1098;
}
else
{
lean_object* x_1101; lean_object* x_1102; 
x_1101 = lean_ctor_get(x_1098, 1);
lean_inc(x_1101);
lean_dec(x_1098);
x_1102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1102, 0, x_3);
lean_ctor_set(x_1102, 1, x_1101);
return x_1102;
}
}
}
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; uint8_t x_1107; 
x_1103 = lean_ctor_get(x_1076, 1);
lean_inc(x_1103);
lean_dec(x_1076);
x_1104 = lean_st_ref_get(x_11, x_1103);
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1105, 3);
lean_inc(x_1106);
lean_dec(x_1105);
x_1107 = lean_ctor_get_uint8(x_1106, sizeof(void*)*1);
lean_dec(x_1106);
if (x_1107 == 0)
{
lean_object* x_1108; uint8_t x_1109; 
x_1108 = lean_ctor_get(x_1104, 1);
lean_inc(x_1108);
lean_dec(x_1104);
x_1109 = 0;
x_1007 = x_1109;
x_1008 = x_1108;
goto block_1017;
}
else
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; uint8_t x_1114; 
x_1110 = lean_ctor_get(x_1104, 1);
lean_inc(x_1110);
lean_dec(x_1104);
x_1111 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1070, x_8, x_9, x_10, x_11, x_1110);
x_1112 = lean_ctor_get(x_1111, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1111, 1);
lean_inc(x_1113);
lean_dec(x_1111);
x_1114 = lean_unbox(x_1112);
lean_dec(x_1112);
x_1007 = x_1114;
x_1008 = x_1113;
goto block_1017;
}
}
}
else
{
uint8_t x_1115; 
lean_dec(x_970);
lean_dec(x_968);
lean_dec(x_965);
lean_dec(x_952);
lean_dec(x_951);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1115 = !lean_is_exclusive(x_1076);
if (x_1115 == 0)
{
lean_object* x_1116; 
x_1116 = lean_ctor_get(x_1076, 0);
lean_dec(x_1116);
lean_ctor_set_tag(x_1076, 0);
lean_ctor_set(x_1076, 0, x_3);
return x_1076;
}
else
{
lean_object* x_1117; lean_object* x_1118; 
x_1117 = lean_ctor_get(x_1076, 1);
lean_inc(x_1117);
lean_dec(x_1076);
x_1118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1118, 0, x_3);
lean_ctor_set(x_1118, 1, x_1117);
return x_1118;
}
}
}
else
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1119 = lean_ctor_get(x_1071, 1);
lean_inc(x_1119);
lean_dec(x_1071);
x_1120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1120, 0, x_1005);
x_1121 = l_Lean_KernelException_toMessageData___closed__15;
x_1122 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1122, 0, x_1121);
lean_ctor_set(x_1122, 1, x_1120);
x_1123 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1123, 0, x_1122);
lean_ctor_set(x_1123, 1, x_1121);
x_1124 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1070, x_1123, x_8, x_9, x_10, x_11, x_1119);
x_1125 = lean_ctor_get(x_1124, 1);
lean_inc(x_1125);
lean_dec(x_1124);
x_1126 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1127 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_971, x_1126, x_8, x_9, x_10, x_11, x_1125);
if (lean_obj_tag(x_1127) == 0)
{
lean_object* x_1128; uint8_t x_1129; 
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
x_1129 = lean_unbox(x_1128);
lean_dec(x_1128);
if (x_1129 == 0)
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; 
lean_dec(x_970);
lean_dec(x_968);
lean_dec(x_965);
lean_dec(x_952);
lean_dec(x_951);
x_1130 = lean_ctor_get(x_1127, 1);
lean_inc(x_1130);
lean_dec(x_1127);
x_1131 = lean_st_ref_get(x_11, x_1130);
x_1132 = lean_ctor_get(x_1131, 0);
lean_inc(x_1132);
x_1133 = lean_ctor_get(x_1132, 3);
lean_inc(x_1133);
lean_dec(x_1132);
x_1134 = lean_ctor_get_uint8(x_1133, sizeof(void*)*1);
lean_dec(x_1133);
if (x_1134 == 0)
{
uint8_t x_1135; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1135 = !lean_is_exclusive(x_1131);
if (x_1135 == 0)
{
lean_object* x_1136; 
x_1136 = lean_ctor_get(x_1131, 0);
lean_dec(x_1136);
lean_ctor_set(x_1131, 0, x_3);
return x_1131;
}
else
{
lean_object* x_1137; lean_object* x_1138; 
x_1137 = lean_ctor_get(x_1131, 1);
lean_inc(x_1137);
lean_dec(x_1131);
x_1138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1138, 0, x_3);
lean_ctor_set(x_1138, 1, x_1137);
return x_1138;
}
}
else
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; uint8_t x_1142; 
x_1139 = lean_ctor_get(x_1131, 1);
lean_inc(x_1139);
lean_dec(x_1131);
x_1140 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1070, x_8, x_9, x_10, x_11, x_1139);
x_1141 = lean_ctor_get(x_1140, 0);
lean_inc(x_1141);
x_1142 = lean_unbox(x_1141);
lean_dec(x_1141);
if (x_1142 == 0)
{
uint8_t x_1143; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1143 = !lean_is_exclusive(x_1140);
if (x_1143 == 0)
{
lean_object* x_1144; 
x_1144 = lean_ctor_get(x_1140, 0);
lean_dec(x_1144);
lean_ctor_set(x_1140, 0, x_3);
return x_1140;
}
else
{
lean_object* x_1145; lean_object* x_1146; 
x_1145 = lean_ctor_get(x_1140, 1);
lean_inc(x_1145);
lean_dec(x_1140);
x_1146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1146, 0, x_3);
lean_ctor_set(x_1146, 1, x_1145);
return x_1146;
}
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; uint8_t x_1150; 
x_1147 = lean_ctor_get(x_1140, 1);
lean_inc(x_1147);
lean_dec(x_1140);
x_1148 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1149 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1070, x_1148, x_8, x_9, x_10, x_11, x_1147);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1150 = !lean_is_exclusive(x_1149);
if (x_1150 == 0)
{
lean_object* x_1151; 
x_1151 = lean_ctor_get(x_1149, 0);
lean_dec(x_1151);
lean_ctor_set(x_1149, 0, x_3);
return x_1149;
}
else
{
lean_object* x_1152; lean_object* x_1153; 
x_1152 = lean_ctor_get(x_1149, 1);
lean_inc(x_1152);
lean_dec(x_1149);
x_1153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1153, 0, x_3);
lean_ctor_set(x_1153, 1, x_1152);
return x_1153;
}
}
}
}
else
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; uint8_t x_1158; 
x_1154 = lean_ctor_get(x_1127, 1);
lean_inc(x_1154);
lean_dec(x_1127);
x_1155 = lean_st_ref_get(x_11, x_1154);
x_1156 = lean_ctor_get(x_1155, 0);
lean_inc(x_1156);
x_1157 = lean_ctor_get(x_1156, 3);
lean_inc(x_1157);
lean_dec(x_1156);
x_1158 = lean_ctor_get_uint8(x_1157, sizeof(void*)*1);
lean_dec(x_1157);
if (x_1158 == 0)
{
lean_object* x_1159; uint8_t x_1160; 
x_1159 = lean_ctor_get(x_1155, 1);
lean_inc(x_1159);
lean_dec(x_1155);
x_1160 = 0;
x_1007 = x_1160;
x_1008 = x_1159;
goto block_1017;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; uint8_t x_1165; 
x_1161 = lean_ctor_get(x_1155, 1);
lean_inc(x_1161);
lean_dec(x_1155);
x_1162 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1070, x_8, x_9, x_10, x_11, x_1161);
x_1163 = lean_ctor_get(x_1162, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1162, 1);
lean_inc(x_1164);
lean_dec(x_1162);
x_1165 = lean_unbox(x_1163);
lean_dec(x_1163);
x_1007 = x_1165;
x_1008 = x_1164;
goto block_1017;
}
}
}
else
{
uint8_t x_1166; 
lean_dec(x_970);
lean_dec(x_968);
lean_dec(x_965);
lean_dec(x_952);
lean_dec(x_951);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1166 = !lean_is_exclusive(x_1127);
if (x_1166 == 0)
{
lean_object* x_1167; 
x_1167 = lean_ctor_get(x_1127, 0);
lean_dec(x_1167);
lean_ctor_set_tag(x_1127, 0);
lean_ctor_set(x_1127, 0, x_3);
return x_1127;
}
else
{
lean_object* x_1168; lean_object* x_1169; 
x_1168 = lean_ctor_get(x_1127, 1);
lean_inc(x_1168);
lean_dec(x_1127);
x_1169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1169, 0, x_3);
lean_ctor_set(x_1169, 1, x_1168);
return x_1169;
}
}
}
}
block_1017:
{
if (x_1007 == 0)
{
x_972 = x_1008;
goto block_1003;
}
else
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
lean_inc(x_968);
x_1009 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1009, 0, x_968);
x_1010 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_1011 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1011, 0, x_1010);
lean_ctor_set(x_1011, 1, x_1009);
x_1012 = l_Lean_KernelException_toMessageData___closed__15;
x_1013 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_1012);
x_1014 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1015 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1014, x_1013, x_8, x_9, x_10, x_11, x_1008);
x_1016 = lean_ctor_get(x_1015, 1);
lean_inc(x_1016);
lean_dec(x_1015);
x_972 = x_1016;
goto block_1003;
}
}
}
else
{
uint8_t x_1170; 
lean_dec(x_971);
lean_dec(x_970);
lean_dec(x_968);
lean_dec(x_965);
lean_dec(x_952);
lean_dec(x_951);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1170 = !lean_is_exclusive(x_1004);
if (x_1170 == 0)
{
lean_object* x_1171; 
x_1171 = lean_ctor_get(x_1004, 0);
lean_dec(x_1171);
lean_ctor_set_tag(x_1004, 0);
lean_ctor_set(x_1004, 0, x_3);
return x_1004;
}
else
{
lean_object* x_1172; lean_object* x_1173; 
x_1172 = lean_ctor_get(x_1004, 1);
lean_inc(x_1172);
lean_dec(x_1004);
x_1173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1173, 0, x_3);
lean_ctor_set(x_1173, 1, x_1172);
return x_1173;
}
}
block_1003:
{
lean_object* x_973; uint8_t x_974; 
x_973 = lean_array_get_size(x_1);
x_974 = lean_nat_dec_lt(x_948, x_973);
if (x_974 == 0)
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; 
lean_dec(x_973);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_965)) {
 x_975 = lean_alloc_ctor(0, 2, 0);
} else {
 x_975 = x_965;
}
lean_ctor_set(x_975, 0, x_968);
lean_ctor_set(x_975, 1, x_951);
if (lean_is_scalar(x_952)) {
 x_976 = lean_alloc_ctor(1, 1, 0);
} else {
 x_976 = x_952;
}
lean_ctor_set(x_976, 0, x_975);
if (lean_is_scalar(x_970)) {
 x_977 = lean_alloc_ctor(0, 2, 0);
} else {
 x_977 = x_970;
}
lean_ctor_set(x_977, 0, x_976);
lean_ctor_set(x_977, 1, x_972);
return x_977;
}
else
{
uint8_t x_978; 
x_978 = lean_nat_dec_le(x_973, x_973);
if (x_978 == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; 
lean_dec(x_973);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_965)) {
 x_979 = lean_alloc_ctor(0, 2, 0);
} else {
 x_979 = x_965;
}
lean_ctor_set(x_979, 0, x_968);
lean_ctor_set(x_979, 1, x_951);
if (lean_is_scalar(x_952)) {
 x_980 = lean_alloc_ctor(1, 1, 0);
} else {
 x_980 = x_952;
}
lean_ctor_set(x_980, 0, x_979);
if (lean_is_scalar(x_970)) {
 x_981 = lean_alloc_ctor(0, 2, 0);
} else {
 x_981 = x_970;
}
lean_ctor_set(x_981, 0, x_980);
lean_ctor_set(x_981, 1, x_972);
return x_981;
}
else
{
size_t x_982; size_t x_983; lean_object* x_984; 
lean_dec(x_970);
x_982 = 0;
x_983 = lean_usize_of_nat(x_973);
lean_dec(x_973);
lean_inc(x_968);
x_984 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_968, x_1, x_982, x_983, x_8, x_9, x_10, x_11, x_972);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; uint8_t x_986; 
x_985 = lean_ctor_get(x_984, 0);
lean_inc(x_985);
x_986 = lean_unbox(x_985);
lean_dec(x_985);
if (x_986 == 0)
{
uint8_t x_987; 
lean_dec(x_3);
x_987 = !lean_is_exclusive(x_984);
if (x_987 == 0)
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_988 = lean_ctor_get(x_984, 0);
lean_dec(x_988);
if (lean_is_scalar(x_965)) {
 x_989 = lean_alloc_ctor(0, 2, 0);
} else {
 x_989 = x_965;
}
lean_ctor_set(x_989, 0, x_968);
lean_ctor_set(x_989, 1, x_951);
if (lean_is_scalar(x_952)) {
 x_990 = lean_alloc_ctor(1, 1, 0);
} else {
 x_990 = x_952;
}
lean_ctor_set(x_990, 0, x_989);
lean_ctor_set(x_984, 0, x_990);
return x_984;
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_991 = lean_ctor_get(x_984, 1);
lean_inc(x_991);
lean_dec(x_984);
if (lean_is_scalar(x_965)) {
 x_992 = lean_alloc_ctor(0, 2, 0);
} else {
 x_992 = x_965;
}
lean_ctor_set(x_992, 0, x_968);
lean_ctor_set(x_992, 1, x_951);
if (lean_is_scalar(x_952)) {
 x_993 = lean_alloc_ctor(1, 1, 0);
} else {
 x_993 = x_952;
}
lean_ctor_set(x_993, 0, x_992);
x_994 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_994, 0, x_993);
lean_ctor_set(x_994, 1, x_991);
return x_994;
}
}
else
{
uint8_t x_995; 
lean_dec(x_968);
lean_dec(x_965);
lean_dec(x_952);
lean_dec(x_951);
x_995 = !lean_is_exclusive(x_984);
if (x_995 == 0)
{
lean_object* x_996; 
x_996 = lean_ctor_get(x_984, 0);
lean_dec(x_996);
lean_ctor_set(x_984, 0, x_3);
return x_984;
}
else
{
lean_object* x_997; lean_object* x_998; 
x_997 = lean_ctor_get(x_984, 1);
lean_inc(x_997);
lean_dec(x_984);
x_998 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_998, 0, x_3);
lean_ctor_set(x_998, 1, x_997);
return x_998;
}
}
}
else
{
uint8_t x_999; 
lean_dec(x_968);
lean_dec(x_965);
lean_dec(x_952);
lean_dec(x_951);
x_999 = !lean_is_exclusive(x_984);
if (x_999 == 0)
{
lean_object* x_1000; 
x_1000 = lean_ctor_get(x_984, 0);
lean_dec(x_1000);
lean_ctor_set_tag(x_984, 0);
lean_ctor_set(x_984, 0, x_3);
return x_984;
}
else
{
lean_object* x_1001; lean_object* x_1002; 
x_1001 = lean_ctor_get(x_984, 1);
lean_inc(x_1001);
lean_dec(x_984);
x_1002 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1002, 0, x_3);
lean_ctor_set(x_1002, 1, x_1001);
return x_1002;
}
}
}
}
}
}
else
{
uint8_t x_1174; 
lean_dec(x_952);
lean_dec(x_951);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_1174 = !lean_is_exclusive(x_961);
if (x_1174 == 0)
{
return x_961;
}
else
{
lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; 
x_1175 = lean_ctor_get(x_961, 0);
x_1176 = lean_ctor_get(x_961, 1);
lean_inc(x_1176);
lean_inc(x_1175);
lean_dec(x_961);
x_1177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1177, 0, x_1175);
lean_ctor_set(x_1177, 1, x_1176);
return x_1177;
}
}
}
}
}
}
case 5:
{
lean_object* x_1178; lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1178 = lean_ctor_get(x_5, 0);
lean_inc(x_1178);
x_1179 = lean_ctor_get(x_5, 1);
lean_inc(x_1179);
lean_dec(x_5);
x_1180 = lean_array_set(x_6, x_7, x_1179);
x_1181 = lean_unsigned_to_nat(1u);
x_1182 = lean_nat_sub(x_7, x_1181);
lean_dec(x_7);
x_5 = x_1178;
x_6 = x_1180;
x_7 = x_1182;
goto _start;
}
case 6:
{
lean_object* x_1184; 
lean_dec(x_7);
lean_dec(x_6);
x_1184 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_1184) == 0)
{
lean_object* x_1185; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1185, 0, x_3);
lean_ctor_set(x_1185, 1, x_12);
return x_1185;
}
else
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; 
x_1186 = lean_ctor_get(x_1184, 0);
lean_inc(x_1186);
lean_dec(x_1184);
x_1187 = lean_unsigned_to_nat(0u);
x_1188 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_1187);
if (lean_obj_tag(x_1188) == 0)
{
lean_object* x_1189; 
lean_dec(x_1186);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1189, 0, x_3);
lean_ctor_set(x_1189, 1, x_12);
return x_1189;
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; uint8_t x_1194; 
x_1190 = lean_ctor_get(x_1188, 0);
lean_inc(x_1190);
if (lean_is_exclusive(x_1188)) {
 lean_ctor_release(x_1188, 0);
 x_1191 = x_1188;
} else {
 lean_dec_ref(x_1188);
 x_1191 = lean_box(0);
}
x_1192 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1186, x_8, x_9, x_10, x_11, x_12);
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
x_1194 = lean_unbox(x_1193);
lean_dec(x_1193);
if (x_1194 == 0)
{
uint8_t x_1195; 
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1195 = !lean_is_exclusive(x_1192);
if (x_1195 == 0)
{
lean_object* x_1196; 
x_1196 = lean_ctor_get(x_1192, 0);
lean_dec(x_1196);
lean_ctor_set(x_1192, 0, x_3);
return x_1192;
}
else
{
lean_object* x_1197; lean_object* x_1198; 
x_1197 = lean_ctor_get(x_1192, 1);
lean_inc(x_1197);
lean_dec(x_1192);
x_1198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1198, 0, x_3);
lean_ctor_set(x_1198, 1, x_1197);
return x_1198;
}
}
else
{
lean_object* x_1199; lean_object* x_1200; 
x_1199 = lean_ctor_get(x_1192, 1);
lean_inc(x_1199);
lean_dec(x_1192);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1200 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_1190, x_8, x_9, x_10, x_11, x_1199);
if (lean_obj_tag(x_1200) == 0)
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1243; 
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1200, 1);
lean_inc(x_1202);
lean_dec(x_1200);
x_1203 = lean_ctor_get(x_1201, 1);
lean_inc(x_1203);
if (lean_is_exclusive(x_1201)) {
 lean_ctor_release(x_1201, 0);
 lean_ctor_release(x_1201, 1);
 x_1204 = x_1201;
} else {
 lean_dec_ref(x_1201);
 x_1204 = lean_box(0);
}
x_1205 = lean_box(0);
lean_inc(x_8);
x_1206 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1203, x_1205, x_8, x_9, x_10, x_11, x_1202);
x_1207 = lean_ctor_get(x_1206, 0);
lean_inc(x_1207);
x_1208 = lean_ctor_get(x_1206, 1);
lean_inc(x_1208);
if (lean_is_exclusive(x_1206)) {
 lean_ctor_release(x_1206, 0);
 lean_ctor_release(x_1206, 1);
 x_1209 = x_1206;
} else {
 lean_dec_ref(x_1206);
 x_1209 = lean_box(0);
}
x_1210 = l_Lean_Expr_mvarId_x21(x_1207);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1243 = l_Lean_Meta_ppGoal(x_1210, x_8, x_9, x_10, x_11, x_1208);
if (lean_obj_tag(x_1243) == 0)
{
lean_object* x_1244; lean_object* x_1245; uint8_t x_1246; lean_object* x_1247; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; uint8_t x_1260; 
x_1244 = lean_ctor_get(x_1243, 0);
lean_inc(x_1244);
x_1245 = lean_ctor_get(x_1243, 1);
lean_inc(x_1245);
lean_dec(x_1243);
x_1257 = lean_st_ref_get(x_11, x_1245);
x_1258 = lean_ctor_get(x_1257, 0);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_1258, 3);
lean_inc(x_1259);
lean_dec(x_1258);
x_1260 = lean_ctor_get_uint8(x_1259, sizeof(void*)*1);
lean_dec(x_1259);
if (x_1260 == 0)
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; 
lean_dec(x_1244);
x_1261 = lean_ctor_get(x_1257, 1);
lean_inc(x_1261);
lean_dec(x_1257);
x_1262 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1263 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1210, x_1262, x_8, x_9, x_10, x_11, x_1261);
if (lean_obj_tag(x_1263) == 0)
{
lean_object* x_1264; uint8_t x_1265; 
x_1264 = lean_ctor_get(x_1263, 0);
lean_inc(x_1264);
x_1265 = lean_unbox(x_1264);
lean_dec(x_1264);
if (x_1265 == 0)
{
lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; uint8_t x_1270; 
lean_dec(x_1209);
lean_dec(x_1207);
lean_dec(x_1204);
lean_dec(x_1191);
lean_dec(x_1190);
x_1266 = lean_ctor_get(x_1263, 1);
lean_inc(x_1266);
lean_dec(x_1263);
x_1267 = lean_st_ref_get(x_11, x_1266);
x_1268 = lean_ctor_get(x_1267, 0);
lean_inc(x_1268);
x_1269 = lean_ctor_get(x_1268, 3);
lean_inc(x_1269);
lean_dec(x_1268);
x_1270 = lean_ctor_get_uint8(x_1269, sizeof(void*)*1);
lean_dec(x_1269);
if (x_1270 == 0)
{
uint8_t x_1271; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1271 = !lean_is_exclusive(x_1267);
if (x_1271 == 0)
{
lean_object* x_1272; 
x_1272 = lean_ctor_get(x_1267, 0);
lean_dec(x_1272);
lean_ctor_set(x_1267, 0, x_3);
return x_1267;
}
else
{
lean_object* x_1273; lean_object* x_1274; 
x_1273 = lean_ctor_get(x_1267, 1);
lean_inc(x_1273);
lean_dec(x_1267);
x_1274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1274, 0, x_3);
lean_ctor_set(x_1274, 1, x_1273);
return x_1274;
}
}
else
{
lean_object* x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; uint8_t x_1279; 
x_1275 = lean_ctor_get(x_1267, 1);
lean_inc(x_1275);
lean_dec(x_1267);
x_1276 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1277 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1276, x_8, x_9, x_10, x_11, x_1275);
x_1278 = lean_ctor_get(x_1277, 0);
lean_inc(x_1278);
x_1279 = lean_unbox(x_1278);
lean_dec(x_1278);
if (x_1279 == 0)
{
uint8_t x_1280; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1280 = !lean_is_exclusive(x_1277);
if (x_1280 == 0)
{
lean_object* x_1281; 
x_1281 = lean_ctor_get(x_1277, 0);
lean_dec(x_1281);
lean_ctor_set(x_1277, 0, x_3);
return x_1277;
}
else
{
lean_object* x_1282; lean_object* x_1283; 
x_1282 = lean_ctor_get(x_1277, 1);
lean_inc(x_1282);
lean_dec(x_1277);
x_1283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1283, 0, x_3);
lean_ctor_set(x_1283, 1, x_1282);
return x_1283;
}
}
else
{
lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; uint8_t x_1287; 
x_1284 = lean_ctor_get(x_1277, 1);
lean_inc(x_1284);
lean_dec(x_1277);
x_1285 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1286 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1276, x_1285, x_8, x_9, x_10, x_11, x_1284);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1287 = !lean_is_exclusive(x_1286);
if (x_1287 == 0)
{
lean_object* x_1288; 
x_1288 = lean_ctor_get(x_1286, 0);
lean_dec(x_1288);
lean_ctor_set(x_1286, 0, x_3);
return x_1286;
}
else
{
lean_object* x_1289; lean_object* x_1290; 
x_1289 = lean_ctor_get(x_1286, 1);
lean_inc(x_1289);
lean_dec(x_1286);
x_1290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1290, 0, x_3);
lean_ctor_set(x_1290, 1, x_1289);
return x_1290;
}
}
}
}
else
{
lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; uint8_t x_1295; 
x_1291 = lean_ctor_get(x_1263, 1);
lean_inc(x_1291);
lean_dec(x_1263);
x_1292 = lean_st_ref_get(x_11, x_1291);
x_1293 = lean_ctor_get(x_1292, 0);
lean_inc(x_1293);
x_1294 = lean_ctor_get(x_1293, 3);
lean_inc(x_1294);
lean_dec(x_1293);
x_1295 = lean_ctor_get_uint8(x_1294, sizeof(void*)*1);
lean_dec(x_1294);
if (x_1295 == 0)
{
lean_object* x_1296; uint8_t x_1297; 
x_1296 = lean_ctor_get(x_1292, 1);
lean_inc(x_1296);
lean_dec(x_1292);
x_1297 = 0;
x_1246 = x_1297;
x_1247 = x_1296;
goto block_1256;
}
else
{
lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; uint8_t x_1303; 
x_1298 = lean_ctor_get(x_1292, 1);
lean_inc(x_1298);
lean_dec(x_1292);
x_1299 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1300 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1299, x_8, x_9, x_10, x_11, x_1298);
x_1301 = lean_ctor_get(x_1300, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_1300, 1);
lean_inc(x_1302);
lean_dec(x_1300);
x_1303 = lean_unbox(x_1301);
lean_dec(x_1301);
x_1246 = x_1303;
x_1247 = x_1302;
goto block_1256;
}
}
}
else
{
uint8_t x_1304; 
lean_dec(x_1209);
lean_dec(x_1207);
lean_dec(x_1204);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1304 = !lean_is_exclusive(x_1263);
if (x_1304 == 0)
{
lean_object* x_1305; 
x_1305 = lean_ctor_get(x_1263, 0);
lean_dec(x_1305);
lean_ctor_set_tag(x_1263, 0);
lean_ctor_set(x_1263, 0, x_3);
return x_1263;
}
else
{
lean_object* x_1306; lean_object* x_1307; 
x_1306 = lean_ctor_get(x_1263, 1);
lean_inc(x_1306);
lean_dec(x_1263);
x_1307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1307, 0, x_3);
lean_ctor_set(x_1307, 1, x_1306);
return x_1307;
}
}
}
else
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; uint8_t x_1312; 
x_1308 = lean_ctor_get(x_1257, 1);
lean_inc(x_1308);
lean_dec(x_1257);
x_1309 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1310 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1309, x_8, x_9, x_10, x_11, x_1308);
x_1311 = lean_ctor_get(x_1310, 0);
lean_inc(x_1311);
x_1312 = lean_unbox(x_1311);
lean_dec(x_1311);
if (x_1312 == 0)
{
lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; 
lean_dec(x_1244);
x_1313 = lean_ctor_get(x_1310, 1);
lean_inc(x_1313);
lean_dec(x_1310);
x_1314 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1315 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1210, x_1314, x_8, x_9, x_10, x_11, x_1313);
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1316; uint8_t x_1317; 
x_1316 = lean_ctor_get(x_1315, 0);
lean_inc(x_1316);
x_1317 = lean_unbox(x_1316);
lean_dec(x_1316);
if (x_1317 == 0)
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; uint8_t x_1322; 
lean_dec(x_1209);
lean_dec(x_1207);
lean_dec(x_1204);
lean_dec(x_1191);
lean_dec(x_1190);
x_1318 = lean_ctor_get(x_1315, 1);
lean_inc(x_1318);
lean_dec(x_1315);
x_1319 = lean_st_ref_get(x_11, x_1318);
x_1320 = lean_ctor_get(x_1319, 0);
lean_inc(x_1320);
x_1321 = lean_ctor_get(x_1320, 3);
lean_inc(x_1321);
lean_dec(x_1320);
x_1322 = lean_ctor_get_uint8(x_1321, sizeof(void*)*1);
lean_dec(x_1321);
if (x_1322 == 0)
{
uint8_t x_1323; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1323 = !lean_is_exclusive(x_1319);
if (x_1323 == 0)
{
lean_object* x_1324; 
x_1324 = lean_ctor_get(x_1319, 0);
lean_dec(x_1324);
lean_ctor_set(x_1319, 0, x_3);
return x_1319;
}
else
{
lean_object* x_1325; lean_object* x_1326; 
x_1325 = lean_ctor_get(x_1319, 1);
lean_inc(x_1325);
lean_dec(x_1319);
x_1326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1326, 0, x_3);
lean_ctor_set(x_1326, 1, x_1325);
return x_1326;
}
}
else
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; uint8_t x_1330; 
x_1327 = lean_ctor_get(x_1319, 1);
lean_inc(x_1327);
lean_dec(x_1319);
x_1328 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1309, x_8, x_9, x_10, x_11, x_1327);
x_1329 = lean_ctor_get(x_1328, 0);
lean_inc(x_1329);
x_1330 = lean_unbox(x_1329);
lean_dec(x_1329);
if (x_1330 == 0)
{
uint8_t x_1331; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1331 = !lean_is_exclusive(x_1328);
if (x_1331 == 0)
{
lean_object* x_1332; 
x_1332 = lean_ctor_get(x_1328, 0);
lean_dec(x_1332);
lean_ctor_set(x_1328, 0, x_3);
return x_1328;
}
else
{
lean_object* x_1333; lean_object* x_1334; 
x_1333 = lean_ctor_get(x_1328, 1);
lean_inc(x_1333);
lean_dec(x_1328);
x_1334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1334, 0, x_3);
lean_ctor_set(x_1334, 1, x_1333);
return x_1334;
}
}
else
{
lean_object* x_1335; lean_object* x_1336; lean_object* x_1337; uint8_t x_1338; 
x_1335 = lean_ctor_get(x_1328, 1);
lean_inc(x_1335);
lean_dec(x_1328);
x_1336 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1337 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1309, x_1336, x_8, x_9, x_10, x_11, x_1335);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1338 = !lean_is_exclusive(x_1337);
if (x_1338 == 0)
{
lean_object* x_1339; 
x_1339 = lean_ctor_get(x_1337, 0);
lean_dec(x_1339);
lean_ctor_set(x_1337, 0, x_3);
return x_1337;
}
else
{
lean_object* x_1340; lean_object* x_1341; 
x_1340 = lean_ctor_get(x_1337, 1);
lean_inc(x_1340);
lean_dec(x_1337);
x_1341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1341, 0, x_3);
lean_ctor_set(x_1341, 1, x_1340);
return x_1341;
}
}
}
}
else
{
lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; uint8_t x_1346; 
x_1342 = lean_ctor_get(x_1315, 1);
lean_inc(x_1342);
lean_dec(x_1315);
x_1343 = lean_st_ref_get(x_11, x_1342);
x_1344 = lean_ctor_get(x_1343, 0);
lean_inc(x_1344);
x_1345 = lean_ctor_get(x_1344, 3);
lean_inc(x_1345);
lean_dec(x_1344);
x_1346 = lean_ctor_get_uint8(x_1345, sizeof(void*)*1);
lean_dec(x_1345);
if (x_1346 == 0)
{
lean_object* x_1347; uint8_t x_1348; 
x_1347 = lean_ctor_get(x_1343, 1);
lean_inc(x_1347);
lean_dec(x_1343);
x_1348 = 0;
x_1246 = x_1348;
x_1247 = x_1347;
goto block_1256;
}
else
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; uint8_t x_1353; 
x_1349 = lean_ctor_get(x_1343, 1);
lean_inc(x_1349);
lean_dec(x_1343);
x_1350 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1309, x_8, x_9, x_10, x_11, x_1349);
x_1351 = lean_ctor_get(x_1350, 0);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_1350, 1);
lean_inc(x_1352);
lean_dec(x_1350);
x_1353 = lean_unbox(x_1351);
lean_dec(x_1351);
x_1246 = x_1353;
x_1247 = x_1352;
goto block_1256;
}
}
}
else
{
uint8_t x_1354; 
lean_dec(x_1209);
lean_dec(x_1207);
lean_dec(x_1204);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1354 = !lean_is_exclusive(x_1315);
if (x_1354 == 0)
{
lean_object* x_1355; 
x_1355 = lean_ctor_get(x_1315, 0);
lean_dec(x_1355);
lean_ctor_set_tag(x_1315, 0);
lean_ctor_set(x_1315, 0, x_3);
return x_1315;
}
else
{
lean_object* x_1356; lean_object* x_1357; 
x_1356 = lean_ctor_get(x_1315, 1);
lean_inc(x_1356);
lean_dec(x_1315);
x_1357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1357, 0, x_3);
lean_ctor_set(x_1357, 1, x_1356);
return x_1357;
}
}
}
else
{
lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
x_1358 = lean_ctor_get(x_1310, 1);
lean_inc(x_1358);
lean_dec(x_1310);
x_1359 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1359, 0, x_1244);
x_1360 = l_Lean_KernelException_toMessageData___closed__15;
x_1361 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1361, 0, x_1360);
lean_ctor_set(x_1361, 1, x_1359);
x_1362 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1362, 0, x_1361);
lean_ctor_set(x_1362, 1, x_1360);
x_1363 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1309, x_1362, x_8, x_9, x_10, x_11, x_1358);
x_1364 = lean_ctor_get(x_1363, 1);
lean_inc(x_1364);
lean_dec(x_1363);
x_1365 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1366 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1210, x_1365, x_8, x_9, x_10, x_11, x_1364);
if (lean_obj_tag(x_1366) == 0)
{
lean_object* x_1367; uint8_t x_1368; 
x_1367 = lean_ctor_get(x_1366, 0);
lean_inc(x_1367);
x_1368 = lean_unbox(x_1367);
lean_dec(x_1367);
if (x_1368 == 0)
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; uint8_t x_1373; 
lean_dec(x_1209);
lean_dec(x_1207);
lean_dec(x_1204);
lean_dec(x_1191);
lean_dec(x_1190);
x_1369 = lean_ctor_get(x_1366, 1);
lean_inc(x_1369);
lean_dec(x_1366);
x_1370 = lean_st_ref_get(x_11, x_1369);
x_1371 = lean_ctor_get(x_1370, 0);
lean_inc(x_1371);
x_1372 = lean_ctor_get(x_1371, 3);
lean_inc(x_1372);
lean_dec(x_1371);
x_1373 = lean_ctor_get_uint8(x_1372, sizeof(void*)*1);
lean_dec(x_1372);
if (x_1373 == 0)
{
uint8_t x_1374; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1374 = !lean_is_exclusive(x_1370);
if (x_1374 == 0)
{
lean_object* x_1375; 
x_1375 = lean_ctor_get(x_1370, 0);
lean_dec(x_1375);
lean_ctor_set(x_1370, 0, x_3);
return x_1370;
}
else
{
lean_object* x_1376; lean_object* x_1377; 
x_1376 = lean_ctor_get(x_1370, 1);
lean_inc(x_1376);
lean_dec(x_1370);
x_1377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1377, 0, x_3);
lean_ctor_set(x_1377, 1, x_1376);
return x_1377;
}
}
else
{
lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; uint8_t x_1381; 
x_1378 = lean_ctor_get(x_1370, 1);
lean_inc(x_1378);
lean_dec(x_1370);
x_1379 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1309, x_8, x_9, x_10, x_11, x_1378);
x_1380 = lean_ctor_get(x_1379, 0);
lean_inc(x_1380);
x_1381 = lean_unbox(x_1380);
lean_dec(x_1380);
if (x_1381 == 0)
{
uint8_t x_1382; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1382 = !lean_is_exclusive(x_1379);
if (x_1382 == 0)
{
lean_object* x_1383; 
x_1383 = lean_ctor_get(x_1379, 0);
lean_dec(x_1383);
lean_ctor_set(x_1379, 0, x_3);
return x_1379;
}
else
{
lean_object* x_1384; lean_object* x_1385; 
x_1384 = lean_ctor_get(x_1379, 1);
lean_inc(x_1384);
lean_dec(x_1379);
x_1385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1385, 0, x_3);
lean_ctor_set(x_1385, 1, x_1384);
return x_1385;
}
}
else
{
lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; uint8_t x_1389; 
x_1386 = lean_ctor_get(x_1379, 1);
lean_inc(x_1386);
lean_dec(x_1379);
x_1387 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1388 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1309, x_1387, x_8, x_9, x_10, x_11, x_1386);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1389 = !lean_is_exclusive(x_1388);
if (x_1389 == 0)
{
lean_object* x_1390; 
x_1390 = lean_ctor_get(x_1388, 0);
lean_dec(x_1390);
lean_ctor_set(x_1388, 0, x_3);
return x_1388;
}
else
{
lean_object* x_1391; lean_object* x_1392; 
x_1391 = lean_ctor_get(x_1388, 1);
lean_inc(x_1391);
lean_dec(x_1388);
x_1392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1392, 0, x_3);
lean_ctor_set(x_1392, 1, x_1391);
return x_1392;
}
}
}
}
else
{
lean_object* x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; uint8_t x_1397; 
x_1393 = lean_ctor_get(x_1366, 1);
lean_inc(x_1393);
lean_dec(x_1366);
x_1394 = lean_st_ref_get(x_11, x_1393);
x_1395 = lean_ctor_get(x_1394, 0);
lean_inc(x_1395);
x_1396 = lean_ctor_get(x_1395, 3);
lean_inc(x_1396);
lean_dec(x_1395);
x_1397 = lean_ctor_get_uint8(x_1396, sizeof(void*)*1);
lean_dec(x_1396);
if (x_1397 == 0)
{
lean_object* x_1398; uint8_t x_1399; 
x_1398 = lean_ctor_get(x_1394, 1);
lean_inc(x_1398);
lean_dec(x_1394);
x_1399 = 0;
x_1246 = x_1399;
x_1247 = x_1398;
goto block_1256;
}
else
{
lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; uint8_t x_1404; 
x_1400 = lean_ctor_get(x_1394, 1);
lean_inc(x_1400);
lean_dec(x_1394);
x_1401 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1309, x_8, x_9, x_10, x_11, x_1400);
x_1402 = lean_ctor_get(x_1401, 0);
lean_inc(x_1402);
x_1403 = lean_ctor_get(x_1401, 1);
lean_inc(x_1403);
lean_dec(x_1401);
x_1404 = lean_unbox(x_1402);
lean_dec(x_1402);
x_1246 = x_1404;
x_1247 = x_1403;
goto block_1256;
}
}
}
else
{
uint8_t x_1405; 
lean_dec(x_1209);
lean_dec(x_1207);
lean_dec(x_1204);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1405 = !lean_is_exclusive(x_1366);
if (x_1405 == 0)
{
lean_object* x_1406; 
x_1406 = lean_ctor_get(x_1366, 0);
lean_dec(x_1406);
lean_ctor_set_tag(x_1366, 0);
lean_ctor_set(x_1366, 0, x_3);
return x_1366;
}
else
{
lean_object* x_1407; lean_object* x_1408; 
x_1407 = lean_ctor_get(x_1366, 1);
lean_inc(x_1407);
lean_dec(x_1366);
x_1408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1408, 0, x_3);
lean_ctor_set(x_1408, 1, x_1407);
return x_1408;
}
}
}
}
block_1256:
{
if (x_1246 == 0)
{
x_1211 = x_1247;
goto block_1242;
}
else
{
lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
lean_inc(x_1207);
x_1248 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1248, 0, x_1207);
x_1249 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_1250 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1250, 0, x_1249);
lean_ctor_set(x_1250, 1, x_1248);
x_1251 = l_Lean_KernelException_toMessageData___closed__15;
x_1252 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1252, 0, x_1250);
lean_ctor_set(x_1252, 1, x_1251);
x_1253 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1254 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1253, x_1252, x_8, x_9, x_10, x_11, x_1247);
x_1255 = lean_ctor_get(x_1254, 1);
lean_inc(x_1255);
lean_dec(x_1254);
x_1211 = x_1255;
goto block_1242;
}
}
}
else
{
uint8_t x_1409; 
lean_dec(x_1210);
lean_dec(x_1209);
lean_dec(x_1207);
lean_dec(x_1204);
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1409 = !lean_is_exclusive(x_1243);
if (x_1409 == 0)
{
lean_object* x_1410; 
x_1410 = lean_ctor_get(x_1243, 0);
lean_dec(x_1410);
lean_ctor_set_tag(x_1243, 0);
lean_ctor_set(x_1243, 0, x_3);
return x_1243;
}
else
{
lean_object* x_1411; lean_object* x_1412; 
x_1411 = lean_ctor_get(x_1243, 1);
lean_inc(x_1411);
lean_dec(x_1243);
x_1412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1412, 0, x_3);
lean_ctor_set(x_1412, 1, x_1411);
return x_1412;
}
}
block_1242:
{
lean_object* x_1212; uint8_t x_1213; 
x_1212 = lean_array_get_size(x_1);
x_1213 = lean_nat_dec_lt(x_1187, x_1212);
if (x_1213 == 0)
{
lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
lean_dec(x_1212);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1204)) {
 x_1214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1214 = x_1204;
}
lean_ctor_set(x_1214, 0, x_1207);
lean_ctor_set(x_1214, 1, x_1190);
if (lean_is_scalar(x_1191)) {
 x_1215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1215 = x_1191;
}
lean_ctor_set(x_1215, 0, x_1214);
if (lean_is_scalar(x_1209)) {
 x_1216 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1216 = x_1209;
}
lean_ctor_set(x_1216, 0, x_1215);
lean_ctor_set(x_1216, 1, x_1211);
return x_1216;
}
else
{
uint8_t x_1217; 
x_1217 = lean_nat_dec_le(x_1212, x_1212);
if (x_1217 == 0)
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
lean_dec(x_1212);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1204)) {
 x_1218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1218 = x_1204;
}
lean_ctor_set(x_1218, 0, x_1207);
lean_ctor_set(x_1218, 1, x_1190);
if (lean_is_scalar(x_1191)) {
 x_1219 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1219 = x_1191;
}
lean_ctor_set(x_1219, 0, x_1218);
if (lean_is_scalar(x_1209)) {
 x_1220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1220 = x_1209;
}
lean_ctor_set(x_1220, 0, x_1219);
lean_ctor_set(x_1220, 1, x_1211);
return x_1220;
}
else
{
size_t x_1221; size_t x_1222; lean_object* x_1223; 
lean_dec(x_1209);
x_1221 = 0;
x_1222 = lean_usize_of_nat(x_1212);
lean_dec(x_1212);
lean_inc(x_1207);
x_1223 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1207, x_1, x_1221, x_1222, x_8, x_9, x_10, x_11, x_1211);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; uint8_t x_1225; 
x_1224 = lean_ctor_get(x_1223, 0);
lean_inc(x_1224);
x_1225 = lean_unbox(x_1224);
lean_dec(x_1224);
if (x_1225 == 0)
{
uint8_t x_1226; 
lean_dec(x_3);
x_1226 = !lean_is_exclusive(x_1223);
if (x_1226 == 0)
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; 
x_1227 = lean_ctor_get(x_1223, 0);
lean_dec(x_1227);
if (lean_is_scalar(x_1204)) {
 x_1228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1228 = x_1204;
}
lean_ctor_set(x_1228, 0, x_1207);
lean_ctor_set(x_1228, 1, x_1190);
if (lean_is_scalar(x_1191)) {
 x_1229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1229 = x_1191;
}
lean_ctor_set(x_1229, 0, x_1228);
lean_ctor_set(x_1223, 0, x_1229);
return x_1223;
}
else
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; 
x_1230 = lean_ctor_get(x_1223, 1);
lean_inc(x_1230);
lean_dec(x_1223);
if (lean_is_scalar(x_1204)) {
 x_1231 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1231 = x_1204;
}
lean_ctor_set(x_1231, 0, x_1207);
lean_ctor_set(x_1231, 1, x_1190);
if (lean_is_scalar(x_1191)) {
 x_1232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1232 = x_1191;
}
lean_ctor_set(x_1232, 0, x_1231);
x_1233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1233, 0, x_1232);
lean_ctor_set(x_1233, 1, x_1230);
return x_1233;
}
}
else
{
uint8_t x_1234; 
lean_dec(x_1207);
lean_dec(x_1204);
lean_dec(x_1191);
lean_dec(x_1190);
x_1234 = !lean_is_exclusive(x_1223);
if (x_1234 == 0)
{
lean_object* x_1235; 
x_1235 = lean_ctor_get(x_1223, 0);
lean_dec(x_1235);
lean_ctor_set(x_1223, 0, x_3);
return x_1223;
}
else
{
lean_object* x_1236; lean_object* x_1237; 
x_1236 = lean_ctor_get(x_1223, 1);
lean_inc(x_1236);
lean_dec(x_1223);
x_1237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1237, 0, x_3);
lean_ctor_set(x_1237, 1, x_1236);
return x_1237;
}
}
}
else
{
uint8_t x_1238; 
lean_dec(x_1207);
lean_dec(x_1204);
lean_dec(x_1191);
lean_dec(x_1190);
x_1238 = !lean_is_exclusive(x_1223);
if (x_1238 == 0)
{
lean_object* x_1239; 
x_1239 = lean_ctor_get(x_1223, 0);
lean_dec(x_1239);
lean_ctor_set_tag(x_1223, 0);
lean_ctor_set(x_1223, 0, x_3);
return x_1223;
}
else
{
lean_object* x_1240; lean_object* x_1241; 
x_1240 = lean_ctor_get(x_1223, 1);
lean_inc(x_1240);
lean_dec(x_1223);
x_1241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1241, 0, x_3);
lean_ctor_set(x_1241, 1, x_1240);
return x_1241;
}
}
}
}
}
}
else
{
uint8_t x_1413; 
lean_dec(x_1191);
lean_dec(x_1190);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_1413 = !lean_is_exclusive(x_1200);
if (x_1413 == 0)
{
return x_1200;
}
else
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; 
x_1414 = lean_ctor_get(x_1200, 0);
x_1415 = lean_ctor_get(x_1200, 1);
lean_inc(x_1415);
lean_inc(x_1414);
lean_dec(x_1200);
x_1416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1416, 0, x_1414);
lean_ctor_set(x_1416, 1, x_1415);
return x_1416;
}
}
}
}
}
}
case 7:
{
lean_object* x_1417; 
lean_dec(x_7);
lean_dec(x_6);
x_1417 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_1417) == 0)
{
lean_object* x_1418; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1418, 0, x_3);
lean_ctor_set(x_1418, 1, x_12);
return x_1418;
}
else
{
lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; 
x_1419 = lean_ctor_get(x_1417, 0);
lean_inc(x_1419);
lean_dec(x_1417);
x_1420 = lean_unsigned_to_nat(0u);
x_1421 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_1420);
if (lean_obj_tag(x_1421) == 0)
{
lean_object* x_1422; 
lean_dec(x_1419);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1422, 0, x_3);
lean_ctor_set(x_1422, 1, x_12);
return x_1422;
}
else
{
lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; uint8_t x_1427; 
x_1423 = lean_ctor_get(x_1421, 0);
lean_inc(x_1423);
if (lean_is_exclusive(x_1421)) {
 lean_ctor_release(x_1421, 0);
 x_1424 = x_1421;
} else {
 lean_dec_ref(x_1421);
 x_1424 = lean_box(0);
}
x_1425 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1419, x_8, x_9, x_10, x_11, x_12);
x_1426 = lean_ctor_get(x_1425, 0);
lean_inc(x_1426);
x_1427 = lean_unbox(x_1426);
lean_dec(x_1426);
if (x_1427 == 0)
{
uint8_t x_1428; 
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1428 = !lean_is_exclusive(x_1425);
if (x_1428 == 0)
{
lean_object* x_1429; 
x_1429 = lean_ctor_get(x_1425, 0);
lean_dec(x_1429);
lean_ctor_set(x_1425, 0, x_3);
return x_1425;
}
else
{
lean_object* x_1430; lean_object* x_1431; 
x_1430 = lean_ctor_get(x_1425, 1);
lean_inc(x_1430);
lean_dec(x_1425);
x_1431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1431, 0, x_3);
lean_ctor_set(x_1431, 1, x_1430);
return x_1431;
}
}
else
{
lean_object* x_1432; lean_object* x_1433; 
x_1432 = lean_ctor_get(x_1425, 1);
lean_inc(x_1432);
lean_dec(x_1425);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1433 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_1423, x_8, x_9, x_10, x_11, x_1432);
if (lean_obj_tag(x_1433) == 0)
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1476; 
x_1434 = lean_ctor_get(x_1433, 0);
lean_inc(x_1434);
x_1435 = lean_ctor_get(x_1433, 1);
lean_inc(x_1435);
lean_dec(x_1433);
x_1436 = lean_ctor_get(x_1434, 1);
lean_inc(x_1436);
if (lean_is_exclusive(x_1434)) {
 lean_ctor_release(x_1434, 0);
 lean_ctor_release(x_1434, 1);
 x_1437 = x_1434;
} else {
 lean_dec_ref(x_1434);
 x_1437 = lean_box(0);
}
x_1438 = lean_box(0);
lean_inc(x_8);
x_1439 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1436, x_1438, x_8, x_9, x_10, x_11, x_1435);
x_1440 = lean_ctor_get(x_1439, 0);
lean_inc(x_1440);
x_1441 = lean_ctor_get(x_1439, 1);
lean_inc(x_1441);
if (lean_is_exclusive(x_1439)) {
 lean_ctor_release(x_1439, 0);
 lean_ctor_release(x_1439, 1);
 x_1442 = x_1439;
} else {
 lean_dec_ref(x_1439);
 x_1442 = lean_box(0);
}
x_1443 = l_Lean_Expr_mvarId_x21(x_1440);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1476 = l_Lean_Meta_ppGoal(x_1443, x_8, x_9, x_10, x_11, x_1441);
if (lean_obj_tag(x_1476) == 0)
{
lean_object* x_1477; lean_object* x_1478; uint8_t x_1479; lean_object* x_1480; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; uint8_t x_1493; 
x_1477 = lean_ctor_get(x_1476, 0);
lean_inc(x_1477);
x_1478 = lean_ctor_get(x_1476, 1);
lean_inc(x_1478);
lean_dec(x_1476);
x_1490 = lean_st_ref_get(x_11, x_1478);
x_1491 = lean_ctor_get(x_1490, 0);
lean_inc(x_1491);
x_1492 = lean_ctor_get(x_1491, 3);
lean_inc(x_1492);
lean_dec(x_1491);
x_1493 = lean_ctor_get_uint8(x_1492, sizeof(void*)*1);
lean_dec(x_1492);
if (x_1493 == 0)
{
lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; 
lean_dec(x_1477);
x_1494 = lean_ctor_get(x_1490, 1);
lean_inc(x_1494);
lean_dec(x_1490);
x_1495 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1496 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1443, x_1495, x_8, x_9, x_10, x_11, x_1494);
if (lean_obj_tag(x_1496) == 0)
{
lean_object* x_1497; uint8_t x_1498; 
x_1497 = lean_ctor_get(x_1496, 0);
lean_inc(x_1497);
x_1498 = lean_unbox(x_1497);
lean_dec(x_1497);
if (x_1498 == 0)
{
lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; uint8_t x_1503; 
lean_dec(x_1442);
lean_dec(x_1440);
lean_dec(x_1437);
lean_dec(x_1424);
lean_dec(x_1423);
x_1499 = lean_ctor_get(x_1496, 1);
lean_inc(x_1499);
lean_dec(x_1496);
x_1500 = lean_st_ref_get(x_11, x_1499);
x_1501 = lean_ctor_get(x_1500, 0);
lean_inc(x_1501);
x_1502 = lean_ctor_get(x_1501, 3);
lean_inc(x_1502);
lean_dec(x_1501);
x_1503 = lean_ctor_get_uint8(x_1502, sizeof(void*)*1);
lean_dec(x_1502);
if (x_1503 == 0)
{
uint8_t x_1504; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1504 = !lean_is_exclusive(x_1500);
if (x_1504 == 0)
{
lean_object* x_1505; 
x_1505 = lean_ctor_get(x_1500, 0);
lean_dec(x_1505);
lean_ctor_set(x_1500, 0, x_3);
return x_1500;
}
else
{
lean_object* x_1506; lean_object* x_1507; 
x_1506 = lean_ctor_get(x_1500, 1);
lean_inc(x_1506);
lean_dec(x_1500);
x_1507 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1507, 0, x_3);
lean_ctor_set(x_1507, 1, x_1506);
return x_1507;
}
}
else
{
lean_object* x_1508; lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; uint8_t x_1512; 
x_1508 = lean_ctor_get(x_1500, 1);
lean_inc(x_1508);
lean_dec(x_1500);
x_1509 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1510 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1509, x_8, x_9, x_10, x_11, x_1508);
x_1511 = lean_ctor_get(x_1510, 0);
lean_inc(x_1511);
x_1512 = lean_unbox(x_1511);
lean_dec(x_1511);
if (x_1512 == 0)
{
uint8_t x_1513; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1513 = !lean_is_exclusive(x_1510);
if (x_1513 == 0)
{
lean_object* x_1514; 
x_1514 = lean_ctor_get(x_1510, 0);
lean_dec(x_1514);
lean_ctor_set(x_1510, 0, x_3);
return x_1510;
}
else
{
lean_object* x_1515; lean_object* x_1516; 
x_1515 = lean_ctor_get(x_1510, 1);
lean_inc(x_1515);
lean_dec(x_1510);
x_1516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1516, 0, x_3);
lean_ctor_set(x_1516, 1, x_1515);
return x_1516;
}
}
else
{
lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; uint8_t x_1520; 
x_1517 = lean_ctor_get(x_1510, 1);
lean_inc(x_1517);
lean_dec(x_1510);
x_1518 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1519 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1509, x_1518, x_8, x_9, x_10, x_11, x_1517);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1520 = !lean_is_exclusive(x_1519);
if (x_1520 == 0)
{
lean_object* x_1521; 
x_1521 = lean_ctor_get(x_1519, 0);
lean_dec(x_1521);
lean_ctor_set(x_1519, 0, x_3);
return x_1519;
}
else
{
lean_object* x_1522; lean_object* x_1523; 
x_1522 = lean_ctor_get(x_1519, 1);
lean_inc(x_1522);
lean_dec(x_1519);
x_1523 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1523, 0, x_3);
lean_ctor_set(x_1523, 1, x_1522);
return x_1523;
}
}
}
}
else
{
lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; uint8_t x_1528; 
x_1524 = lean_ctor_get(x_1496, 1);
lean_inc(x_1524);
lean_dec(x_1496);
x_1525 = lean_st_ref_get(x_11, x_1524);
x_1526 = lean_ctor_get(x_1525, 0);
lean_inc(x_1526);
x_1527 = lean_ctor_get(x_1526, 3);
lean_inc(x_1527);
lean_dec(x_1526);
x_1528 = lean_ctor_get_uint8(x_1527, sizeof(void*)*1);
lean_dec(x_1527);
if (x_1528 == 0)
{
lean_object* x_1529; uint8_t x_1530; 
x_1529 = lean_ctor_get(x_1525, 1);
lean_inc(x_1529);
lean_dec(x_1525);
x_1530 = 0;
x_1479 = x_1530;
x_1480 = x_1529;
goto block_1489;
}
else
{
lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; uint8_t x_1536; 
x_1531 = lean_ctor_get(x_1525, 1);
lean_inc(x_1531);
lean_dec(x_1525);
x_1532 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1533 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1532, x_8, x_9, x_10, x_11, x_1531);
x_1534 = lean_ctor_get(x_1533, 0);
lean_inc(x_1534);
x_1535 = lean_ctor_get(x_1533, 1);
lean_inc(x_1535);
lean_dec(x_1533);
x_1536 = lean_unbox(x_1534);
lean_dec(x_1534);
x_1479 = x_1536;
x_1480 = x_1535;
goto block_1489;
}
}
}
else
{
uint8_t x_1537; 
lean_dec(x_1442);
lean_dec(x_1440);
lean_dec(x_1437);
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1537 = !lean_is_exclusive(x_1496);
if (x_1537 == 0)
{
lean_object* x_1538; 
x_1538 = lean_ctor_get(x_1496, 0);
lean_dec(x_1538);
lean_ctor_set_tag(x_1496, 0);
lean_ctor_set(x_1496, 0, x_3);
return x_1496;
}
else
{
lean_object* x_1539; lean_object* x_1540; 
x_1539 = lean_ctor_get(x_1496, 1);
lean_inc(x_1539);
lean_dec(x_1496);
x_1540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1540, 0, x_3);
lean_ctor_set(x_1540, 1, x_1539);
return x_1540;
}
}
}
else
{
lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; uint8_t x_1545; 
x_1541 = lean_ctor_get(x_1490, 1);
lean_inc(x_1541);
lean_dec(x_1490);
x_1542 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1543 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1542, x_8, x_9, x_10, x_11, x_1541);
x_1544 = lean_ctor_get(x_1543, 0);
lean_inc(x_1544);
x_1545 = lean_unbox(x_1544);
lean_dec(x_1544);
if (x_1545 == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; 
lean_dec(x_1477);
x_1546 = lean_ctor_get(x_1543, 1);
lean_inc(x_1546);
lean_dec(x_1543);
x_1547 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1548 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1443, x_1547, x_8, x_9, x_10, x_11, x_1546);
if (lean_obj_tag(x_1548) == 0)
{
lean_object* x_1549; uint8_t x_1550; 
x_1549 = lean_ctor_get(x_1548, 0);
lean_inc(x_1549);
x_1550 = lean_unbox(x_1549);
lean_dec(x_1549);
if (x_1550 == 0)
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; uint8_t x_1555; 
lean_dec(x_1442);
lean_dec(x_1440);
lean_dec(x_1437);
lean_dec(x_1424);
lean_dec(x_1423);
x_1551 = lean_ctor_get(x_1548, 1);
lean_inc(x_1551);
lean_dec(x_1548);
x_1552 = lean_st_ref_get(x_11, x_1551);
x_1553 = lean_ctor_get(x_1552, 0);
lean_inc(x_1553);
x_1554 = lean_ctor_get(x_1553, 3);
lean_inc(x_1554);
lean_dec(x_1553);
x_1555 = lean_ctor_get_uint8(x_1554, sizeof(void*)*1);
lean_dec(x_1554);
if (x_1555 == 0)
{
uint8_t x_1556; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1556 = !lean_is_exclusive(x_1552);
if (x_1556 == 0)
{
lean_object* x_1557; 
x_1557 = lean_ctor_get(x_1552, 0);
lean_dec(x_1557);
lean_ctor_set(x_1552, 0, x_3);
return x_1552;
}
else
{
lean_object* x_1558; lean_object* x_1559; 
x_1558 = lean_ctor_get(x_1552, 1);
lean_inc(x_1558);
lean_dec(x_1552);
x_1559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1559, 0, x_3);
lean_ctor_set(x_1559, 1, x_1558);
return x_1559;
}
}
else
{
lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; uint8_t x_1563; 
x_1560 = lean_ctor_get(x_1552, 1);
lean_inc(x_1560);
lean_dec(x_1552);
x_1561 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1542, x_8, x_9, x_10, x_11, x_1560);
x_1562 = lean_ctor_get(x_1561, 0);
lean_inc(x_1562);
x_1563 = lean_unbox(x_1562);
lean_dec(x_1562);
if (x_1563 == 0)
{
uint8_t x_1564; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1564 = !lean_is_exclusive(x_1561);
if (x_1564 == 0)
{
lean_object* x_1565; 
x_1565 = lean_ctor_get(x_1561, 0);
lean_dec(x_1565);
lean_ctor_set(x_1561, 0, x_3);
return x_1561;
}
else
{
lean_object* x_1566; lean_object* x_1567; 
x_1566 = lean_ctor_get(x_1561, 1);
lean_inc(x_1566);
lean_dec(x_1561);
x_1567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1567, 0, x_3);
lean_ctor_set(x_1567, 1, x_1566);
return x_1567;
}
}
else
{
lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; uint8_t x_1571; 
x_1568 = lean_ctor_get(x_1561, 1);
lean_inc(x_1568);
lean_dec(x_1561);
x_1569 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1570 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1542, x_1569, x_8, x_9, x_10, x_11, x_1568);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1571 = !lean_is_exclusive(x_1570);
if (x_1571 == 0)
{
lean_object* x_1572; 
x_1572 = lean_ctor_get(x_1570, 0);
lean_dec(x_1572);
lean_ctor_set(x_1570, 0, x_3);
return x_1570;
}
else
{
lean_object* x_1573; lean_object* x_1574; 
x_1573 = lean_ctor_get(x_1570, 1);
lean_inc(x_1573);
lean_dec(x_1570);
x_1574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1574, 0, x_3);
lean_ctor_set(x_1574, 1, x_1573);
return x_1574;
}
}
}
}
else
{
lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; uint8_t x_1579; 
x_1575 = lean_ctor_get(x_1548, 1);
lean_inc(x_1575);
lean_dec(x_1548);
x_1576 = lean_st_ref_get(x_11, x_1575);
x_1577 = lean_ctor_get(x_1576, 0);
lean_inc(x_1577);
x_1578 = lean_ctor_get(x_1577, 3);
lean_inc(x_1578);
lean_dec(x_1577);
x_1579 = lean_ctor_get_uint8(x_1578, sizeof(void*)*1);
lean_dec(x_1578);
if (x_1579 == 0)
{
lean_object* x_1580; uint8_t x_1581; 
x_1580 = lean_ctor_get(x_1576, 1);
lean_inc(x_1580);
lean_dec(x_1576);
x_1581 = 0;
x_1479 = x_1581;
x_1480 = x_1580;
goto block_1489;
}
else
{
lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; uint8_t x_1586; 
x_1582 = lean_ctor_get(x_1576, 1);
lean_inc(x_1582);
lean_dec(x_1576);
x_1583 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1542, x_8, x_9, x_10, x_11, x_1582);
x_1584 = lean_ctor_get(x_1583, 0);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_1583, 1);
lean_inc(x_1585);
lean_dec(x_1583);
x_1586 = lean_unbox(x_1584);
lean_dec(x_1584);
x_1479 = x_1586;
x_1480 = x_1585;
goto block_1489;
}
}
}
else
{
uint8_t x_1587; 
lean_dec(x_1442);
lean_dec(x_1440);
lean_dec(x_1437);
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1587 = !lean_is_exclusive(x_1548);
if (x_1587 == 0)
{
lean_object* x_1588; 
x_1588 = lean_ctor_get(x_1548, 0);
lean_dec(x_1588);
lean_ctor_set_tag(x_1548, 0);
lean_ctor_set(x_1548, 0, x_3);
return x_1548;
}
else
{
lean_object* x_1589; lean_object* x_1590; 
x_1589 = lean_ctor_get(x_1548, 1);
lean_inc(x_1589);
lean_dec(x_1548);
x_1590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1590, 0, x_3);
lean_ctor_set(x_1590, 1, x_1589);
return x_1590;
}
}
}
else
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
x_1591 = lean_ctor_get(x_1543, 1);
lean_inc(x_1591);
lean_dec(x_1543);
x_1592 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1592, 0, x_1477);
x_1593 = l_Lean_KernelException_toMessageData___closed__15;
x_1594 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1594, 0, x_1593);
lean_ctor_set(x_1594, 1, x_1592);
x_1595 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1595, 0, x_1594);
lean_ctor_set(x_1595, 1, x_1593);
x_1596 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1542, x_1595, x_8, x_9, x_10, x_11, x_1591);
x_1597 = lean_ctor_get(x_1596, 1);
lean_inc(x_1597);
lean_dec(x_1596);
x_1598 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1599 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1443, x_1598, x_8, x_9, x_10, x_11, x_1597);
if (lean_obj_tag(x_1599) == 0)
{
lean_object* x_1600; uint8_t x_1601; 
x_1600 = lean_ctor_get(x_1599, 0);
lean_inc(x_1600);
x_1601 = lean_unbox(x_1600);
lean_dec(x_1600);
if (x_1601 == 0)
{
lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; uint8_t x_1606; 
lean_dec(x_1442);
lean_dec(x_1440);
lean_dec(x_1437);
lean_dec(x_1424);
lean_dec(x_1423);
x_1602 = lean_ctor_get(x_1599, 1);
lean_inc(x_1602);
lean_dec(x_1599);
x_1603 = lean_st_ref_get(x_11, x_1602);
x_1604 = lean_ctor_get(x_1603, 0);
lean_inc(x_1604);
x_1605 = lean_ctor_get(x_1604, 3);
lean_inc(x_1605);
lean_dec(x_1604);
x_1606 = lean_ctor_get_uint8(x_1605, sizeof(void*)*1);
lean_dec(x_1605);
if (x_1606 == 0)
{
uint8_t x_1607; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1607 = !lean_is_exclusive(x_1603);
if (x_1607 == 0)
{
lean_object* x_1608; 
x_1608 = lean_ctor_get(x_1603, 0);
lean_dec(x_1608);
lean_ctor_set(x_1603, 0, x_3);
return x_1603;
}
else
{
lean_object* x_1609; lean_object* x_1610; 
x_1609 = lean_ctor_get(x_1603, 1);
lean_inc(x_1609);
lean_dec(x_1603);
x_1610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1610, 0, x_3);
lean_ctor_set(x_1610, 1, x_1609);
return x_1610;
}
}
else
{
lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; uint8_t x_1614; 
x_1611 = lean_ctor_get(x_1603, 1);
lean_inc(x_1611);
lean_dec(x_1603);
x_1612 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1542, x_8, x_9, x_10, x_11, x_1611);
x_1613 = lean_ctor_get(x_1612, 0);
lean_inc(x_1613);
x_1614 = lean_unbox(x_1613);
lean_dec(x_1613);
if (x_1614 == 0)
{
uint8_t x_1615; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1615 = !lean_is_exclusive(x_1612);
if (x_1615 == 0)
{
lean_object* x_1616; 
x_1616 = lean_ctor_get(x_1612, 0);
lean_dec(x_1616);
lean_ctor_set(x_1612, 0, x_3);
return x_1612;
}
else
{
lean_object* x_1617; lean_object* x_1618; 
x_1617 = lean_ctor_get(x_1612, 1);
lean_inc(x_1617);
lean_dec(x_1612);
x_1618 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1618, 0, x_3);
lean_ctor_set(x_1618, 1, x_1617);
return x_1618;
}
}
else
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; uint8_t x_1622; 
x_1619 = lean_ctor_get(x_1612, 1);
lean_inc(x_1619);
lean_dec(x_1612);
x_1620 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1621 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1542, x_1620, x_8, x_9, x_10, x_11, x_1619);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1622 = !lean_is_exclusive(x_1621);
if (x_1622 == 0)
{
lean_object* x_1623; 
x_1623 = lean_ctor_get(x_1621, 0);
lean_dec(x_1623);
lean_ctor_set(x_1621, 0, x_3);
return x_1621;
}
else
{
lean_object* x_1624; lean_object* x_1625; 
x_1624 = lean_ctor_get(x_1621, 1);
lean_inc(x_1624);
lean_dec(x_1621);
x_1625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1625, 0, x_3);
lean_ctor_set(x_1625, 1, x_1624);
return x_1625;
}
}
}
}
else
{
lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; uint8_t x_1630; 
x_1626 = lean_ctor_get(x_1599, 1);
lean_inc(x_1626);
lean_dec(x_1599);
x_1627 = lean_st_ref_get(x_11, x_1626);
x_1628 = lean_ctor_get(x_1627, 0);
lean_inc(x_1628);
x_1629 = lean_ctor_get(x_1628, 3);
lean_inc(x_1629);
lean_dec(x_1628);
x_1630 = lean_ctor_get_uint8(x_1629, sizeof(void*)*1);
lean_dec(x_1629);
if (x_1630 == 0)
{
lean_object* x_1631; uint8_t x_1632; 
x_1631 = lean_ctor_get(x_1627, 1);
lean_inc(x_1631);
lean_dec(x_1627);
x_1632 = 0;
x_1479 = x_1632;
x_1480 = x_1631;
goto block_1489;
}
else
{
lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; uint8_t x_1637; 
x_1633 = lean_ctor_get(x_1627, 1);
lean_inc(x_1633);
lean_dec(x_1627);
x_1634 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1542, x_8, x_9, x_10, x_11, x_1633);
x_1635 = lean_ctor_get(x_1634, 0);
lean_inc(x_1635);
x_1636 = lean_ctor_get(x_1634, 1);
lean_inc(x_1636);
lean_dec(x_1634);
x_1637 = lean_unbox(x_1635);
lean_dec(x_1635);
x_1479 = x_1637;
x_1480 = x_1636;
goto block_1489;
}
}
}
else
{
uint8_t x_1638; 
lean_dec(x_1442);
lean_dec(x_1440);
lean_dec(x_1437);
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1638 = !lean_is_exclusive(x_1599);
if (x_1638 == 0)
{
lean_object* x_1639; 
x_1639 = lean_ctor_get(x_1599, 0);
lean_dec(x_1639);
lean_ctor_set_tag(x_1599, 0);
lean_ctor_set(x_1599, 0, x_3);
return x_1599;
}
else
{
lean_object* x_1640; lean_object* x_1641; 
x_1640 = lean_ctor_get(x_1599, 1);
lean_inc(x_1640);
lean_dec(x_1599);
x_1641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1641, 0, x_3);
lean_ctor_set(x_1641, 1, x_1640);
return x_1641;
}
}
}
}
block_1489:
{
if (x_1479 == 0)
{
x_1444 = x_1480;
goto block_1475;
}
else
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; 
lean_inc(x_1440);
x_1481 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1481, 0, x_1440);
x_1482 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_1483 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1483, 0, x_1482);
lean_ctor_set(x_1483, 1, x_1481);
x_1484 = l_Lean_KernelException_toMessageData___closed__15;
x_1485 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1485, 0, x_1483);
lean_ctor_set(x_1485, 1, x_1484);
x_1486 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1487 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1486, x_1485, x_8, x_9, x_10, x_11, x_1480);
x_1488 = lean_ctor_get(x_1487, 1);
lean_inc(x_1488);
lean_dec(x_1487);
x_1444 = x_1488;
goto block_1475;
}
}
}
else
{
uint8_t x_1642; 
lean_dec(x_1443);
lean_dec(x_1442);
lean_dec(x_1440);
lean_dec(x_1437);
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1642 = !lean_is_exclusive(x_1476);
if (x_1642 == 0)
{
lean_object* x_1643; 
x_1643 = lean_ctor_get(x_1476, 0);
lean_dec(x_1643);
lean_ctor_set_tag(x_1476, 0);
lean_ctor_set(x_1476, 0, x_3);
return x_1476;
}
else
{
lean_object* x_1644; lean_object* x_1645; 
x_1644 = lean_ctor_get(x_1476, 1);
lean_inc(x_1644);
lean_dec(x_1476);
x_1645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1645, 0, x_3);
lean_ctor_set(x_1645, 1, x_1644);
return x_1645;
}
}
block_1475:
{
lean_object* x_1445; uint8_t x_1446; 
x_1445 = lean_array_get_size(x_1);
x_1446 = lean_nat_dec_lt(x_1420, x_1445);
if (x_1446 == 0)
{
lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; 
lean_dec(x_1445);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1437)) {
 x_1447 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1447 = x_1437;
}
lean_ctor_set(x_1447, 0, x_1440);
lean_ctor_set(x_1447, 1, x_1423);
if (lean_is_scalar(x_1424)) {
 x_1448 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1448 = x_1424;
}
lean_ctor_set(x_1448, 0, x_1447);
if (lean_is_scalar(x_1442)) {
 x_1449 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1449 = x_1442;
}
lean_ctor_set(x_1449, 0, x_1448);
lean_ctor_set(x_1449, 1, x_1444);
return x_1449;
}
else
{
uint8_t x_1450; 
x_1450 = lean_nat_dec_le(x_1445, x_1445);
if (x_1450 == 0)
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; 
lean_dec(x_1445);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1437)) {
 x_1451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1451 = x_1437;
}
lean_ctor_set(x_1451, 0, x_1440);
lean_ctor_set(x_1451, 1, x_1423);
if (lean_is_scalar(x_1424)) {
 x_1452 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1452 = x_1424;
}
lean_ctor_set(x_1452, 0, x_1451);
if (lean_is_scalar(x_1442)) {
 x_1453 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1453 = x_1442;
}
lean_ctor_set(x_1453, 0, x_1452);
lean_ctor_set(x_1453, 1, x_1444);
return x_1453;
}
else
{
size_t x_1454; size_t x_1455; lean_object* x_1456; 
lean_dec(x_1442);
x_1454 = 0;
x_1455 = lean_usize_of_nat(x_1445);
lean_dec(x_1445);
lean_inc(x_1440);
x_1456 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1440, x_1, x_1454, x_1455, x_8, x_9, x_10, x_11, x_1444);
if (lean_obj_tag(x_1456) == 0)
{
lean_object* x_1457; uint8_t x_1458; 
x_1457 = lean_ctor_get(x_1456, 0);
lean_inc(x_1457);
x_1458 = lean_unbox(x_1457);
lean_dec(x_1457);
if (x_1458 == 0)
{
uint8_t x_1459; 
lean_dec(x_3);
x_1459 = !lean_is_exclusive(x_1456);
if (x_1459 == 0)
{
lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; 
x_1460 = lean_ctor_get(x_1456, 0);
lean_dec(x_1460);
if (lean_is_scalar(x_1437)) {
 x_1461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1461 = x_1437;
}
lean_ctor_set(x_1461, 0, x_1440);
lean_ctor_set(x_1461, 1, x_1423);
if (lean_is_scalar(x_1424)) {
 x_1462 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1462 = x_1424;
}
lean_ctor_set(x_1462, 0, x_1461);
lean_ctor_set(x_1456, 0, x_1462);
return x_1456;
}
else
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; 
x_1463 = lean_ctor_get(x_1456, 1);
lean_inc(x_1463);
lean_dec(x_1456);
if (lean_is_scalar(x_1437)) {
 x_1464 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1464 = x_1437;
}
lean_ctor_set(x_1464, 0, x_1440);
lean_ctor_set(x_1464, 1, x_1423);
if (lean_is_scalar(x_1424)) {
 x_1465 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1465 = x_1424;
}
lean_ctor_set(x_1465, 0, x_1464);
x_1466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1466, 0, x_1465);
lean_ctor_set(x_1466, 1, x_1463);
return x_1466;
}
}
else
{
uint8_t x_1467; 
lean_dec(x_1440);
lean_dec(x_1437);
lean_dec(x_1424);
lean_dec(x_1423);
x_1467 = !lean_is_exclusive(x_1456);
if (x_1467 == 0)
{
lean_object* x_1468; 
x_1468 = lean_ctor_get(x_1456, 0);
lean_dec(x_1468);
lean_ctor_set(x_1456, 0, x_3);
return x_1456;
}
else
{
lean_object* x_1469; lean_object* x_1470; 
x_1469 = lean_ctor_get(x_1456, 1);
lean_inc(x_1469);
lean_dec(x_1456);
x_1470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1470, 0, x_3);
lean_ctor_set(x_1470, 1, x_1469);
return x_1470;
}
}
}
else
{
uint8_t x_1471; 
lean_dec(x_1440);
lean_dec(x_1437);
lean_dec(x_1424);
lean_dec(x_1423);
x_1471 = !lean_is_exclusive(x_1456);
if (x_1471 == 0)
{
lean_object* x_1472; 
x_1472 = lean_ctor_get(x_1456, 0);
lean_dec(x_1472);
lean_ctor_set_tag(x_1456, 0);
lean_ctor_set(x_1456, 0, x_3);
return x_1456;
}
else
{
lean_object* x_1473; lean_object* x_1474; 
x_1473 = lean_ctor_get(x_1456, 1);
lean_inc(x_1473);
lean_dec(x_1456);
x_1474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1474, 0, x_3);
lean_ctor_set(x_1474, 1, x_1473);
return x_1474;
}
}
}
}
}
}
else
{
uint8_t x_1646; 
lean_dec(x_1424);
lean_dec(x_1423);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_1646 = !lean_is_exclusive(x_1433);
if (x_1646 == 0)
{
return x_1433;
}
else
{
lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; 
x_1647 = lean_ctor_get(x_1433, 0);
x_1648 = lean_ctor_get(x_1433, 1);
lean_inc(x_1648);
lean_inc(x_1647);
lean_dec(x_1433);
x_1649 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1649, 0, x_1647);
lean_ctor_set(x_1649, 1, x_1648);
return x_1649;
}
}
}
}
}
}
case 8:
{
lean_object* x_1650; 
lean_dec(x_7);
lean_dec(x_6);
x_1650 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_1650) == 0)
{
lean_object* x_1651; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1651, 0, x_3);
lean_ctor_set(x_1651, 1, x_12);
return x_1651;
}
else
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; 
x_1652 = lean_ctor_get(x_1650, 0);
lean_inc(x_1652);
lean_dec(x_1650);
x_1653 = lean_unsigned_to_nat(0u);
x_1654 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_1653);
if (lean_obj_tag(x_1654) == 0)
{
lean_object* x_1655; 
lean_dec(x_1652);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1655, 0, x_3);
lean_ctor_set(x_1655, 1, x_12);
return x_1655;
}
else
{
lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; uint8_t x_1660; 
x_1656 = lean_ctor_get(x_1654, 0);
lean_inc(x_1656);
if (lean_is_exclusive(x_1654)) {
 lean_ctor_release(x_1654, 0);
 x_1657 = x_1654;
} else {
 lean_dec_ref(x_1654);
 x_1657 = lean_box(0);
}
x_1658 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1652, x_8, x_9, x_10, x_11, x_12);
x_1659 = lean_ctor_get(x_1658, 0);
lean_inc(x_1659);
x_1660 = lean_unbox(x_1659);
lean_dec(x_1659);
if (x_1660 == 0)
{
uint8_t x_1661; 
lean_dec(x_1657);
lean_dec(x_1656);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1661 = !lean_is_exclusive(x_1658);
if (x_1661 == 0)
{
lean_object* x_1662; 
x_1662 = lean_ctor_get(x_1658, 0);
lean_dec(x_1662);
lean_ctor_set(x_1658, 0, x_3);
return x_1658;
}
else
{
lean_object* x_1663; lean_object* x_1664; 
x_1663 = lean_ctor_get(x_1658, 1);
lean_inc(x_1663);
lean_dec(x_1658);
x_1664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1664, 0, x_3);
lean_ctor_set(x_1664, 1, x_1663);
return x_1664;
}
}
else
{
lean_object* x_1665; lean_object* x_1666; 
x_1665 = lean_ctor_get(x_1658, 1);
lean_inc(x_1665);
lean_dec(x_1658);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1666 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_1656, x_8, x_9, x_10, x_11, x_1665);
if (lean_obj_tag(x_1666) == 0)
{
lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1709; 
x_1667 = lean_ctor_get(x_1666, 0);
lean_inc(x_1667);
x_1668 = lean_ctor_get(x_1666, 1);
lean_inc(x_1668);
lean_dec(x_1666);
x_1669 = lean_ctor_get(x_1667, 1);
lean_inc(x_1669);
if (lean_is_exclusive(x_1667)) {
 lean_ctor_release(x_1667, 0);
 lean_ctor_release(x_1667, 1);
 x_1670 = x_1667;
} else {
 lean_dec_ref(x_1667);
 x_1670 = lean_box(0);
}
x_1671 = lean_box(0);
lean_inc(x_8);
x_1672 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1669, x_1671, x_8, x_9, x_10, x_11, x_1668);
x_1673 = lean_ctor_get(x_1672, 0);
lean_inc(x_1673);
x_1674 = lean_ctor_get(x_1672, 1);
lean_inc(x_1674);
if (lean_is_exclusive(x_1672)) {
 lean_ctor_release(x_1672, 0);
 lean_ctor_release(x_1672, 1);
 x_1675 = x_1672;
} else {
 lean_dec_ref(x_1672);
 x_1675 = lean_box(0);
}
x_1676 = l_Lean_Expr_mvarId_x21(x_1673);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1709 = l_Lean_Meta_ppGoal(x_1676, x_8, x_9, x_10, x_11, x_1674);
if (lean_obj_tag(x_1709) == 0)
{
lean_object* x_1710; lean_object* x_1711; uint8_t x_1712; lean_object* x_1713; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; uint8_t x_1726; 
x_1710 = lean_ctor_get(x_1709, 0);
lean_inc(x_1710);
x_1711 = lean_ctor_get(x_1709, 1);
lean_inc(x_1711);
lean_dec(x_1709);
x_1723 = lean_st_ref_get(x_11, x_1711);
x_1724 = lean_ctor_get(x_1723, 0);
lean_inc(x_1724);
x_1725 = lean_ctor_get(x_1724, 3);
lean_inc(x_1725);
lean_dec(x_1724);
x_1726 = lean_ctor_get_uint8(x_1725, sizeof(void*)*1);
lean_dec(x_1725);
if (x_1726 == 0)
{
lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; 
lean_dec(x_1710);
x_1727 = lean_ctor_get(x_1723, 1);
lean_inc(x_1727);
lean_dec(x_1723);
x_1728 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1729 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1676, x_1728, x_8, x_9, x_10, x_11, x_1727);
if (lean_obj_tag(x_1729) == 0)
{
lean_object* x_1730; uint8_t x_1731; 
x_1730 = lean_ctor_get(x_1729, 0);
lean_inc(x_1730);
x_1731 = lean_unbox(x_1730);
lean_dec(x_1730);
if (x_1731 == 0)
{
lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; uint8_t x_1736; 
lean_dec(x_1675);
lean_dec(x_1673);
lean_dec(x_1670);
lean_dec(x_1657);
lean_dec(x_1656);
x_1732 = lean_ctor_get(x_1729, 1);
lean_inc(x_1732);
lean_dec(x_1729);
x_1733 = lean_st_ref_get(x_11, x_1732);
x_1734 = lean_ctor_get(x_1733, 0);
lean_inc(x_1734);
x_1735 = lean_ctor_get(x_1734, 3);
lean_inc(x_1735);
lean_dec(x_1734);
x_1736 = lean_ctor_get_uint8(x_1735, sizeof(void*)*1);
lean_dec(x_1735);
if (x_1736 == 0)
{
uint8_t x_1737; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1737 = !lean_is_exclusive(x_1733);
if (x_1737 == 0)
{
lean_object* x_1738; 
x_1738 = lean_ctor_get(x_1733, 0);
lean_dec(x_1738);
lean_ctor_set(x_1733, 0, x_3);
return x_1733;
}
else
{
lean_object* x_1739; lean_object* x_1740; 
x_1739 = lean_ctor_get(x_1733, 1);
lean_inc(x_1739);
lean_dec(x_1733);
x_1740 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1740, 0, x_3);
lean_ctor_set(x_1740, 1, x_1739);
return x_1740;
}
}
else
{
lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; uint8_t x_1745; 
x_1741 = lean_ctor_get(x_1733, 1);
lean_inc(x_1741);
lean_dec(x_1733);
x_1742 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1743 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1742, x_8, x_9, x_10, x_11, x_1741);
x_1744 = lean_ctor_get(x_1743, 0);
lean_inc(x_1744);
x_1745 = lean_unbox(x_1744);
lean_dec(x_1744);
if (x_1745 == 0)
{
uint8_t x_1746; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1746 = !lean_is_exclusive(x_1743);
if (x_1746 == 0)
{
lean_object* x_1747; 
x_1747 = lean_ctor_get(x_1743, 0);
lean_dec(x_1747);
lean_ctor_set(x_1743, 0, x_3);
return x_1743;
}
else
{
lean_object* x_1748; lean_object* x_1749; 
x_1748 = lean_ctor_get(x_1743, 1);
lean_inc(x_1748);
lean_dec(x_1743);
x_1749 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1749, 0, x_3);
lean_ctor_set(x_1749, 1, x_1748);
return x_1749;
}
}
else
{
lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; uint8_t x_1753; 
x_1750 = lean_ctor_get(x_1743, 1);
lean_inc(x_1750);
lean_dec(x_1743);
x_1751 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1752 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1742, x_1751, x_8, x_9, x_10, x_11, x_1750);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1753 = !lean_is_exclusive(x_1752);
if (x_1753 == 0)
{
lean_object* x_1754; 
x_1754 = lean_ctor_get(x_1752, 0);
lean_dec(x_1754);
lean_ctor_set(x_1752, 0, x_3);
return x_1752;
}
else
{
lean_object* x_1755; lean_object* x_1756; 
x_1755 = lean_ctor_get(x_1752, 1);
lean_inc(x_1755);
lean_dec(x_1752);
x_1756 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1756, 0, x_3);
lean_ctor_set(x_1756, 1, x_1755);
return x_1756;
}
}
}
}
else
{
lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; uint8_t x_1761; 
x_1757 = lean_ctor_get(x_1729, 1);
lean_inc(x_1757);
lean_dec(x_1729);
x_1758 = lean_st_ref_get(x_11, x_1757);
x_1759 = lean_ctor_get(x_1758, 0);
lean_inc(x_1759);
x_1760 = lean_ctor_get(x_1759, 3);
lean_inc(x_1760);
lean_dec(x_1759);
x_1761 = lean_ctor_get_uint8(x_1760, sizeof(void*)*1);
lean_dec(x_1760);
if (x_1761 == 0)
{
lean_object* x_1762; uint8_t x_1763; 
x_1762 = lean_ctor_get(x_1758, 1);
lean_inc(x_1762);
lean_dec(x_1758);
x_1763 = 0;
x_1712 = x_1763;
x_1713 = x_1762;
goto block_1722;
}
else
{
lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; uint8_t x_1769; 
x_1764 = lean_ctor_get(x_1758, 1);
lean_inc(x_1764);
lean_dec(x_1758);
x_1765 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1766 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1765, x_8, x_9, x_10, x_11, x_1764);
x_1767 = lean_ctor_get(x_1766, 0);
lean_inc(x_1767);
x_1768 = lean_ctor_get(x_1766, 1);
lean_inc(x_1768);
lean_dec(x_1766);
x_1769 = lean_unbox(x_1767);
lean_dec(x_1767);
x_1712 = x_1769;
x_1713 = x_1768;
goto block_1722;
}
}
}
else
{
uint8_t x_1770; 
lean_dec(x_1675);
lean_dec(x_1673);
lean_dec(x_1670);
lean_dec(x_1657);
lean_dec(x_1656);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1770 = !lean_is_exclusive(x_1729);
if (x_1770 == 0)
{
lean_object* x_1771; 
x_1771 = lean_ctor_get(x_1729, 0);
lean_dec(x_1771);
lean_ctor_set_tag(x_1729, 0);
lean_ctor_set(x_1729, 0, x_3);
return x_1729;
}
else
{
lean_object* x_1772; lean_object* x_1773; 
x_1772 = lean_ctor_get(x_1729, 1);
lean_inc(x_1772);
lean_dec(x_1729);
x_1773 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1773, 0, x_3);
lean_ctor_set(x_1773, 1, x_1772);
return x_1773;
}
}
}
else
{
lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; uint8_t x_1778; 
x_1774 = lean_ctor_get(x_1723, 1);
lean_inc(x_1774);
lean_dec(x_1723);
x_1775 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1776 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1775, x_8, x_9, x_10, x_11, x_1774);
x_1777 = lean_ctor_get(x_1776, 0);
lean_inc(x_1777);
x_1778 = lean_unbox(x_1777);
lean_dec(x_1777);
if (x_1778 == 0)
{
lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; 
lean_dec(x_1710);
x_1779 = lean_ctor_get(x_1776, 1);
lean_inc(x_1779);
lean_dec(x_1776);
x_1780 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1781 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1676, x_1780, x_8, x_9, x_10, x_11, x_1779);
if (lean_obj_tag(x_1781) == 0)
{
lean_object* x_1782; uint8_t x_1783; 
x_1782 = lean_ctor_get(x_1781, 0);
lean_inc(x_1782);
x_1783 = lean_unbox(x_1782);
lean_dec(x_1782);
if (x_1783 == 0)
{
lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; uint8_t x_1788; 
lean_dec(x_1675);
lean_dec(x_1673);
lean_dec(x_1670);
lean_dec(x_1657);
lean_dec(x_1656);
x_1784 = lean_ctor_get(x_1781, 1);
lean_inc(x_1784);
lean_dec(x_1781);
x_1785 = lean_st_ref_get(x_11, x_1784);
x_1786 = lean_ctor_get(x_1785, 0);
lean_inc(x_1786);
x_1787 = lean_ctor_get(x_1786, 3);
lean_inc(x_1787);
lean_dec(x_1786);
x_1788 = lean_ctor_get_uint8(x_1787, sizeof(void*)*1);
lean_dec(x_1787);
if (x_1788 == 0)
{
uint8_t x_1789; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1789 = !lean_is_exclusive(x_1785);
if (x_1789 == 0)
{
lean_object* x_1790; 
x_1790 = lean_ctor_get(x_1785, 0);
lean_dec(x_1790);
lean_ctor_set(x_1785, 0, x_3);
return x_1785;
}
else
{
lean_object* x_1791; lean_object* x_1792; 
x_1791 = lean_ctor_get(x_1785, 1);
lean_inc(x_1791);
lean_dec(x_1785);
x_1792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1792, 0, x_3);
lean_ctor_set(x_1792, 1, x_1791);
return x_1792;
}
}
else
{
lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; uint8_t x_1796; 
x_1793 = lean_ctor_get(x_1785, 1);
lean_inc(x_1793);
lean_dec(x_1785);
x_1794 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1775, x_8, x_9, x_10, x_11, x_1793);
x_1795 = lean_ctor_get(x_1794, 0);
lean_inc(x_1795);
x_1796 = lean_unbox(x_1795);
lean_dec(x_1795);
if (x_1796 == 0)
{
uint8_t x_1797; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1797 = !lean_is_exclusive(x_1794);
if (x_1797 == 0)
{
lean_object* x_1798; 
x_1798 = lean_ctor_get(x_1794, 0);
lean_dec(x_1798);
lean_ctor_set(x_1794, 0, x_3);
return x_1794;
}
else
{
lean_object* x_1799; lean_object* x_1800; 
x_1799 = lean_ctor_get(x_1794, 1);
lean_inc(x_1799);
lean_dec(x_1794);
x_1800 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1800, 0, x_3);
lean_ctor_set(x_1800, 1, x_1799);
return x_1800;
}
}
else
{
lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; uint8_t x_1804; 
x_1801 = lean_ctor_get(x_1794, 1);
lean_inc(x_1801);
lean_dec(x_1794);
x_1802 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1803 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1775, x_1802, x_8, x_9, x_10, x_11, x_1801);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1804 = !lean_is_exclusive(x_1803);
if (x_1804 == 0)
{
lean_object* x_1805; 
x_1805 = lean_ctor_get(x_1803, 0);
lean_dec(x_1805);
lean_ctor_set(x_1803, 0, x_3);
return x_1803;
}
else
{
lean_object* x_1806; lean_object* x_1807; 
x_1806 = lean_ctor_get(x_1803, 1);
lean_inc(x_1806);
lean_dec(x_1803);
x_1807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1807, 0, x_3);
lean_ctor_set(x_1807, 1, x_1806);
return x_1807;
}
}
}
}
else
{
lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; uint8_t x_1812; 
x_1808 = lean_ctor_get(x_1781, 1);
lean_inc(x_1808);
lean_dec(x_1781);
x_1809 = lean_st_ref_get(x_11, x_1808);
x_1810 = lean_ctor_get(x_1809, 0);
lean_inc(x_1810);
x_1811 = lean_ctor_get(x_1810, 3);
lean_inc(x_1811);
lean_dec(x_1810);
x_1812 = lean_ctor_get_uint8(x_1811, sizeof(void*)*1);
lean_dec(x_1811);
if (x_1812 == 0)
{
lean_object* x_1813; uint8_t x_1814; 
x_1813 = lean_ctor_get(x_1809, 1);
lean_inc(x_1813);
lean_dec(x_1809);
x_1814 = 0;
x_1712 = x_1814;
x_1713 = x_1813;
goto block_1722;
}
else
{
lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; uint8_t x_1819; 
x_1815 = lean_ctor_get(x_1809, 1);
lean_inc(x_1815);
lean_dec(x_1809);
x_1816 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1775, x_8, x_9, x_10, x_11, x_1815);
x_1817 = lean_ctor_get(x_1816, 0);
lean_inc(x_1817);
x_1818 = lean_ctor_get(x_1816, 1);
lean_inc(x_1818);
lean_dec(x_1816);
x_1819 = lean_unbox(x_1817);
lean_dec(x_1817);
x_1712 = x_1819;
x_1713 = x_1818;
goto block_1722;
}
}
}
else
{
uint8_t x_1820; 
lean_dec(x_1675);
lean_dec(x_1673);
lean_dec(x_1670);
lean_dec(x_1657);
lean_dec(x_1656);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1820 = !lean_is_exclusive(x_1781);
if (x_1820 == 0)
{
lean_object* x_1821; 
x_1821 = lean_ctor_get(x_1781, 0);
lean_dec(x_1821);
lean_ctor_set_tag(x_1781, 0);
lean_ctor_set(x_1781, 0, x_3);
return x_1781;
}
else
{
lean_object* x_1822; lean_object* x_1823; 
x_1822 = lean_ctor_get(x_1781, 1);
lean_inc(x_1822);
lean_dec(x_1781);
x_1823 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1823, 0, x_3);
lean_ctor_set(x_1823, 1, x_1822);
return x_1823;
}
}
}
else
{
lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; 
x_1824 = lean_ctor_get(x_1776, 1);
lean_inc(x_1824);
lean_dec(x_1776);
x_1825 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1825, 0, x_1710);
x_1826 = l_Lean_KernelException_toMessageData___closed__15;
x_1827 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1827, 0, x_1826);
lean_ctor_set(x_1827, 1, x_1825);
x_1828 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1828, 0, x_1827);
lean_ctor_set(x_1828, 1, x_1826);
x_1829 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1775, x_1828, x_8, x_9, x_10, x_11, x_1824);
x_1830 = lean_ctor_get(x_1829, 1);
lean_inc(x_1830);
lean_dec(x_1829);
x_1831 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1832 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1676, x_1831, x_8, x_9, x_10, x_11, x_1830);
if (lean_obj_tag(x_1832) == 0)
{
lean_object* x_1833; uint8_t x_1834; 
x_1833 = lean_ctor_get(x_1832, 0);
lean_inc(x_1833);
x_1834 = lean_unbox(x_1833);
lean_dec(x_1833);
if (x_1834 == 0)
{
lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; uint8_t x_1839; 
lean_dec(x_1675);
lean_dec(x_1673);
lean_dec(x_1670);
lean_dec(x_1657);
lean_dec(x_1656);
x_1835 = lean_ctor_get(x_1832, 1);
lean_inc(x_1835);
lean_dec(x_1832);
x_1836 = lean_st_ref_get(x_11, x_1835);
x_1837 = lean_ctor_get(x_1836, 0);
lean_inc(x_1837);
x_1838 = lean_ctor_get(x_1837, 3);
lean_inc(x_1838);
lean_dec(x_1837);
x_1839 = lean_ctor_get_uint8(x_1838, sizeof(void*)*1);
lean_dec(x_1838);
if (x_1839 == 0)
{
uint8_t x_1840; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1840 = !lean_is_exclusive(x_1836);
if (x_1840 == 0)
{
lean_object* x_1841; 
x_1841 = lean_ctor_get(x_1836, 0);
lean_dec(x_1841);
lean_ctor_set(x_1836, 0, x_3);
return x_1836;
}
else
{
lean_object* x_1842; lean_object* x_1843; 
x_1842 = lean_ctor_get(x_1836, 1);
lean_inc(x_1842);
lean_dec(x_1836);
x_1843 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1843, 0, x_3);
lean_ctor_set(x_1843, 1, x_1842);
return x_1843;
}
}
else
{
lean_object* x_1844; lean_object* x_1845; lean_object* x_1846; uint8_t x_1847; 
x_1844 = lean_ctor_get(x_1836, 1);
lean_inc(x_1844);
lean_dec(x_1836);
x_1845 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1775, x_8, x_9, x_10, x_11, x_1844);
x_1846 = lean_ctor_get(x_1845, 0);
lean_inc(x_1846);
x_1847 = lean_unbox(x_1846);
lean_dec(x_1846);
if (x_1847 == 0)
{
uint8_t x_1848; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1848 = !lean_is_exclusive(x_1845);
if (x_1848 == 0)
{
lean_object* x_1849; 
x_1849 = lean_ctor_get(x_1845, 0);
lean_dec(x_1849);
lean_ctor_set(x_1845, 0, x_3);
return x_1845;
}
else
{
lean_object* x_1850; lean_object* x_1851; 
x_1850 = lean_ctor_get(x_1845, 1);
lean_inc(x_1850);
lean_dec(x_1845);
x_1851 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1851, 0, x_3);
lean_ctor_set(x_1851, 1, x_1850);
return x_1851;
}
}
else
{
lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; uint8_t x_1855; 
x_1852 = lean_ctor_get(x_1845, 1);
lean_inc(x_1852);
lean_dec(x_1845);
x_1853 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1854 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1775, x_1853, x_8, x_9, x_10, x_11, x_1852);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1855 = !lean_is_exclusive(x_1854);
if (x_1855 == 0)
{
lean_object* x_1856; 
x_1856 = lean_ctor_get(x_1854, 0);
lean_dec(x_1856);
lean_ctor_set(x_1854, 0, x_3);
return x_1854;
}
else
{
lean_object* x_1857; lean_object* x_1858; 
x_1857 = lean_ctor_get(x_1854, 1);
lean_inc(x_1857);
lean_dec(x_1854);
x_1858 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1858, 0, x_3);
lean_ctor_set(x_1858, 1, x_1857);
return x_1858;
}
}
}
}
else
{
lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; uint8_t x_1863; 
x_1859 = lean_ctor_get(x_1832, 1);
lean_inc(x_1859);
lean_dec(x_1832);
x_1860 = lean_st_ref_get(x_11, x_1859);
x_1861 = lean_ctor_get(x_1860, 0);
lean_inc(x_1861);
x_1862 = lean_ctor_get(x_1861, 3);
lean_inc(x_1862);
lean_dec(x_1861);
x_1863 = lean_ctor_get_uint8(x_1862, sizeof(void*)*1);
lean_dec(x_1862);
if (x_1863 == 0)
{
lean_object* x_1864; uint8_t x_1865; 
x_1864 = lean_ctor_get(x_1860, 1);
lean_inc(x_1864);
lean_dec(x_1860);
x_1865 = 0;
x_1712 = x_1865;
x_1713 = x_1864;
goto block_1722;
}
else
{
lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; uint8_t x_1870; 
x_1866 = lean_ctor_get(x_1860, 1);
lean_inc(x_1866);
lean_dec(x_1860);
x_1867 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1775, x_8, x_9, x_10, x_11, x_1866);
x_1868 = lean_ctor_get(x_1867, 0);
lean_inc(x_1868);
x_1869 = lean_ctor_get(x_1867, 1);
lean_inc(x_1869);
lean_dec(x_1867);
x_1870 = lean_unbox(x_1868);
lean_dec(x_1868);
x_1712 = x_1870;
x_1713 = x_1869;
goto block_1722;
}
}
}
else
{
uint8_t x_1871; 
lean_dec(x_1675);
lean_dec(x_1673);
lean_dec(x_1670);
lean_dec(x_1657);
lean_dec(x_1656);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1871 = !lean_is_exclusive(x_1832);
if (x_1871 == 0)
{
lean_object* x_1872; 
x_1872 = lean_ctor_get(x_1832, 0);
lean_dec(x_1872);
lean_ctor_set_tag(x_1832, 0);
lean_ctor_set(x_1832, 0, x_3);
return x_1832;
}
else
{
lean_object* x_1873; lean_object* x_1874; 
x_1873 = lean_ctor_get(x_1832, 1);
lean_inc(x_1873);
lean_dec(x_1832);
x_1874 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1874, 0, x_3);
lean_ctor_set(x_1874, 1, x_1873);
return x_1874;
}
}
}
}
block_1722:
{
if (x_1712 == 0)
{
x_1677 = x_1713;
goto block_1708;
}
else
{
lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; 
lean_inc(x_1673);
x_1714 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1714, 0, x_1673);
x_1715 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_1716 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1716, 0, x_1715);
lean_ctor_set(x_1716, 1, x_1714);
x_1717 = l_Lean_KernelException_toMessageData___closed__15;
x_1718 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1718, 0, x_1716);
lean_ctor_set(x_1718, 1, x_1717);
x_1719 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1720 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1719, x_1718, x_8, x_9, x_10, x_11, x_1713);
x_1721 = lean_ctor_get(x_1720, 1);
lean_inc(x_1721);
lean_dec(x_1720);
x_1677 = x_1721;
goto block_1708;
}
}
}
else
{
uint8_t x_1875; 
lean_dec(x_1676);
lean_dec(x_1675);
lean_dec(x_1673);
lean_dec(x_1670);
lean_dec(x_1657);
lean_dec(x_1656);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1875 = !lean_is_exclusive(x_1709);
if (x_1875 == 0)
{
lean_object* x_1876; 
x_1876 = lean_ctor_get(x_1709, 0);
lean_dec(x_1876);
lean_ctor_set_tag(x_1709, 0);
lean_ctor_set(x_1709, 0, x_3);
return x_1709;
}
else
{
lean_object* x_1877; lean_object* x_1878; 
x_1877 = lean_ctor_get(x_1709, 1);
lean_inc(x_1877);
lean_dec(x_1709);
x_1878 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1878, 0, x_3);
lean_ctor_set(x_1878, 1, x_1877);
return x_1878;
}
}
block_1708:
{
lean_object* x_1678; uint8_t x_1679; 
x_1678 = lean_array_get_size(x_1);
x_1679 = lean_nat_dec_lt(x_1653, x_1678);
if (x_1679 == 0)
{
lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; 
lean_dec(x_1678);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1670)) {
 x_1680 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1680 = x_1670;
}
lean_ctor_set(x_1680, 0, x_1673);
lean_ctor_set(x_1680, 1, x_1656);
if (lean_is_scalar(x_1657)) {
 x_1681 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1681 = x_1657;
}
lean_ctor_set(x_1681, 0, x_1680);
if (lean_is_scalar(x_1675)) {
 x_1682 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1682 = x_1675;
}
lean_ctor_set(x_1682, 0, x_1681);
lean_ctor_set(x_1682, 1, x_1677);
return x_1682;
}
else
{
uint8_t x_1683; 
x_1683 = lean_nat_dec_le(x_1678, x_1678);
if (x_1683 == 0)
{
lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; 
lean_dec(x_1678);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1670)) {
 x_1684 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1684 = x_1670;
}
lean_ctor_set(x_1684, 0, x_1673);
lean_ctor_set(x_1684, 1, x_1656);
if (lean_is_scalar(x_1657)) {
 x_1685 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1685 = x_1657;
}
lean_ctor_set(x_1685, 0, x_1684);
if (lean_is_scalar(x_1675)) {
 x_1686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1686 = x_1675;
}
lean_ctor_set(x_1686, 0, x_1685);
lean_ctor_set(x_1686, 1, x_1677);
return x_1686;
}
else
{
size_t x_1687; size_t x_1688; lean_object* x_1689; 
lean_dec(x_1675);
x_1687 = 0;
x_1688 = lean_usize_of_nat(x_1678);
lean_dec(x_1678);
lean_inc(x_1673);
x_1689 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1673, x_1, x_1687, x_1688, x_8, x_9, x_10, x_11, x_1677);
if (lean_obj_tag(x_1689) == 0)
{
lean_object* x_1690; uint8_t x_1691; 
x_1690 = lean_ctor_get(x_1689, 0);
lean_inc(x_1690);
x_1691 = lean_unbox(x_1690);
lean_dec(x_1690);
if (x_1691 == 0)
{
uint8_t x_1692; 
lean_dec(x_3);
x_1692 = !lean_is_exclusive(x_1689);
if (x_1692 == 0)
{
lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; 
x_1693 = lean_ctor_get(x_1689, 0);
lean_dec(x_1693);
if (lean_is_scalar(x_1670)) {
 x_1694 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1694 = x_1670;
}
lean_ctor_set(x_1694, 0, x_1673);
lean_ctor_set(x_1694, 1, x_1656);
if (lean_is_scalar(x_1657)) {
 x_1695 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1695 = x_1657;
}
lean_ctor_set(x_1695, 0, x_1694);
lean_ctor_set(x_1689, 0, x_1695);
return x_1689;
}
else
{
lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; lean_object* x_1699; 
x_1696 = lean_ctor_get(x_1689, 1);
lean_inc(x_1696);
lean_dec(x_1689);
if (lean_is_scalar(x_1670)) {
 x_1697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1697 = x_1670;
}
lean_ctor_set(x_1697, 0, x_1673);
lean_ctor_set(x_1697, 1, x_1656);
if (lean_is_scalar(x_1657)) {
 x_1698 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1698 = x_1657;
}
lean_ctor_set(x_1698, 0, x_1697);
x_1699 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1699, 0, x_1698);
lean_ctor_set(x_1699, 1, x_1696);
return x_1699;
}
}
else
{
uint8_t x_1700; 
lean_dec(x_1673);
lean_dec(x_1670);
lean_dec(x_1657);
lean_dec(x_1656);
x_1700 = !lean_is_exclusive(x_1689);
if (x_1700 == 0)
{
lean_object* x_1701; 
x_1701 = lean_ctor_get(x_1689, 0);
lean_dec(x_1701);
lean_ctor_set(x_1689, 0, x_3);
return x_1689;
}
else
{
lean_object* x_1702; lean_object* x_1703; 
x_1702 = lean_ctor_get(x_1689, 1);
lean_inc(x_1702);
lean_dec(x_1689);
x_1703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1703, 0, x_3);
lean_ctor_set(x_1703, 1, x_1702);
return x_1703;
}
}
}
else
{
uint8_t x_1704; 
lean_dec(x_1673);
lean_dec(x_1670);
lean_dec(x_1657);
lean_dec(x_1656);
x_1704 = !lean_is_exclusive(x_1689);
if (x_1704 == 0)
{
lean_object* x_1705; 
x_1705 = lean_ctor_get(x_1689, 0);
lean_dec(x_1705);
lean_ctor_set_tag(x_1689, 0);
lean_ctor_set(x_1689, 0, x_3);
return x_1689;
}
else
{
lean_object* x_1706; lean_object* x_1707; 
x_1706 = lean_ctor_get(x_1689, 1);
lean_inc(x_1706);
lean_dec(x_1689);
x_1707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1707, 0, x_3);
lean_ctor_set(x_1707, 1, x_1706);
return x_1707;
}
}
}
}
}
}
else
{
uint8_t x_1879; 
lean_dec(x_1657);
lean_dec(x_1656);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_1879 = !lean_is_exclusive(x_1666);
if (x_1879 == 0)
{
return x_1666;
}
else
{
lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; 
x_1880 = lean_ctor_get(x_1666, 0);
x_1881 = lean_ctor_get(x_1666, 1);
lean_inc(x_1881);
lean_inc(x_1880);
lean_dec(x_1666);
x_1882 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1882, 0, x_1880);
lean_ctor_set(x_1882, 1, x_1881);
return x_1882;
}
}
}
}
}
}
case 9:
{
lean_object* x_1883; 
lean_dec(x_7);
lean_dec(x_6);
x_1883 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_1883) == 0)
{
lean_object* x_1884; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1884 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1884, 0, x_3);
lean_ctor_set(x_1884, 1, x_12);
return x_1884;
}
else
{
lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; 
x_1885 = lean_ctor_get(x_1883, 0);
lean_inc(x_1885);
lean_dec(x_1883);
x_1886 = lean_unsigned_to_nat(0u);
x_1887 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_1886);
if (lean_obj_tag(x_1887) == 0)
{
lean_object* x_1888; 
lean_dec(x_1885);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1888 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1888, 0, x_3);
lean_ctor_set(x_1888, 1, x_12);
return x_1888;
}
else
{
lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; uint8_t x_1893; 
x_1889 = lean_ctor_get(x_1887, 0);
lean_inc(x_1889);
if (lean_is_exclusive(x_1887)) {
 lean_ctor_release(x_1887, 0);
 x_1890 = x_1887;
} else {
 lean_dec_ref(x_1887);
 x_1890 = lean_box(0);
}
x_1891 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_1885, x_8, x_9, x_10, x_11, x_12);
x_1892 = lean_ctor_get(x_1891, 0);
lean_inc(x_1892);
x_1893 = lean_unbox(x_1892);
lean_dec(x_1892);
if (x_1893 == 0)
{
uint8_t x_1894; 
lean_dec(x_1890);
lean_dec(x_1889);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_1894 = !lean_is_exclusive(x_1891);
if (x_1894 == 0)
{
lean_object* x_1895; 
x_1895 = lean_ctor_get(x_1891, 0);
lean_dec(x_1895);
lean_ctor_set(x_1891, 0, x_3);
return x_1891;
}
else
{
lean_object* x_1896; lean_object* x_1897; 
x_1896 = lean_ctor_get(x_1891, 1);
lean_inc(x_1896);
lean_dec(x_1891);
x_1897 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1897, 0, x_3);
lean_ctor_set(x_1897, 1, x_1896);
return x_1897;
}
}
else
{
lean_object* x_1898; lean_object* x_1899; 
x_1898 = lean_ctor_get(x_1891, 1);
lean_inc(x_1898);
lean_dec(x_1891);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1899 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_1889, x_8, x_9, x_10, x_11, x_1898);
if (lean_obj_tag(x_1899) == 0)
{
lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1942; 
x_1900 = lean_ctor_get(x_1899, 0);
lean_inc(x_1900);
x_1901 = lean_ctor_get(x_1899, 1);
lean_inc(x_1901);
lean_dec(x_1899);
x_1902 = lean_ctor_get(x_1900, 1);
lean_inc(x_1902);
if (lean_is_exclusive(x_1900)) {
 lean_ctor_release(x_1900, 0);
 lean_ctor_release(x_1900, 1);
 x_1903 = x_1900;
} else {
 lean_dec_ref(x_1900);
 x_1903 = lean_box(0);
}
x_1904 = lean_box(0);
lean_inc(x_8);
x_1905 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1902, x_1904, x_8, x_9, x_10, x_11, x_1901);
x_1906 = lean_ctor_get(x_1905, 0);
lean_inc(x_1906);
x_1907 = lean_ctor_get(x_1905, 1);
lean_inc(x_1907);
if (lean_is_exclusive(x_1905)) {
 lean_ctor_release(x_1905, 0);
 lean_ctor_release(x_1905, 1);
 x_1908 = x_1905;
} else {
 lean_dec_ref(x_1905);
 x_1908 = lean_box(0);
}
x_1909 = l_Lean_Expr_mvarId_x21(x_1906);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1942 = l_Lean_Meta_ppGoal(x_1909, x_8, x_9, x_10, x_11, x_1907);
if (lean_obj_tag(x_1942) == 0)
{
lean_object* x_1943; lean_object* x_1944; uint8_t x_1945; lean_object* x_1946; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; uint8_t x_1959; 
x_1943 = lean_ctor_get(x_1942, 0);
lean_inc(x_1943);
x_1944 = lean_ctor_get(x_1942, 1);
lean_inc(x_1944);
lean_dec(x_1942);
x_1956 = lean_st_ref_get(x_11, x_1944);
x_1957 = lean_ctor_get(x_1956, 0);
lean_inc(x_1957);
x_1958 = lean_ctor_get(x_1957, 3);
lean_inc(x_1958);
lean_dec(x_1957);
x_1959 = lean_ctor_get_uint8(x_1958, sizeof(void*)*1);
lean_dec(x_1958);
if (x_1959 == 0)
{
lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; 
lean_dec(x_1943);
x_1960 = lean_ctor_get(x_1956, 1);
lean_inc(x_1960);
lean_dec(x_1956);
x_1961 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_1962 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1909, x_1961, x_8, x_9, x_10, x_11, x_1960);
if (lean_obj_tag(x_1962) == 0)
{
lean_object* x_1963; uint8_t x_1964; 
x_1963 = lean_ctor_get(x_1962, 0);
lean_inc(x_1963);
x_1964 = lean_unbox(x_1963);
lean_dec(x_1963);
if (x_1964 == 0)
{
lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; uint8_t x_1969; 
lean_dec(x_1908);
lean_dec(x_1906);
lean_dec(x_1903);
lean_dec(x_1890);
lean_dec(x_1889);
x_1965 = lean_ctor_get(x_1962, 1);
lean_inc(x_1965);
lean_dec(x_1962);
x_1966 = lean_st_ref_get(x_11, x_1965);
x_1967 = lean_ctor_get(x_1966, 0);
lean_inc(x_1967);
x_1968 = lean_ctor_get(x_1967, 3);
lean_inc(x_1968);
lean_dec(x_1967);
x_1969 = lean_ctor_get_uint8(x_1968, sizeof(void*)*1);
lean_dec(x_1968);
if (x_1969 == 0)
{
uint8_t x_1970; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1970 = !lean_is_exclusive(x_1966);
if (x_1970 == 0)
{
lean_object* x_1971; 
x_1971 = lean_ctor_get(x_1966, 0);
lean_dec(x_1971);
lean_ctor_set(x_1966, 0, x_3);
return x_1966;
}
else
{
lean_object* x_1972; lean_object* x_1973; 
x_1972 = lean_ctor_get(x_1966, 1);
lean_inc(x_1972);
lean_dec(x_1966);
x_1973 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1973, 0, x_3);
lean_ctor_set(x_1973, 1, x_1972);
return x_1973;
}
}
else
{
lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; uint8_t x_1978; 
x_1974 = lean_ctor_get(x_1966, 1);
lean_inc(x_1974);
lean_dec(x_1966);
x_1975 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1976 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1975, x_8, x_9, x_10, x_11, x_1974);
x_1977 = lean_ctor_get(x_1976, 0);
lean_inc(x_1977);
x_1978 = lean_unbox(x_1977);
lean_dec(x_1977);
if (x_1978 == 0)
{
uint8_t x_1979; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1979 = !lean_is_exclusive(x_1976);
if (x_1979 == 0)
{
lean_object* x_1980; 
x_1980 = lean_ctor_get(x_1976, 0);
lean_dec(x_1980);
lean_ctor_set(x_1976, 0, x_3);
return x_1976;
}
else
{
lean_object* x_1981; lean_object* x_1982; 
x_1981 = lean_ctor_get(x_1976, 1);
lean_inc(x_1981);
lean_dec(x_1976);
x_1982 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1982, 0, x_3);
lean_ctor_set(x_1982, 1, x_1981);
return x_1982;
}
}
else
{
lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; uint8_t x_1986; 
x_1983 = lean_ctor_get(x_1976, 1);
lean_inc(x_1983);
lean_dec(x_1976);
x_1984 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_1985 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1975, x_1984, x_8, x_9, x_10, x_11, x_1983);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_1986 = !lean_is_exclusive(x_1985);
if (x_1986 == 0)
{
lean_object* x_1987; 
x_1987 = lean_ctor_get(x_1985, 0);
lean_dec(x_1987);
lean_ctor_set(x_1985, 0, x_3);
return x_1985;
}
else
{
lean_object* x_1988; lean_object* x_1989; 
x_1988 = lean_ctor_get(x_1985, 1);
lean_inc(x_1988);
lean_dec(x_1985);
x_1989 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1989, 0, x_3);
lean_ctor_set(x_1989, 1, x_1988);
return x_1989;
}
}
}
}
else
{
lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; uint8_t x_1994; 
x_1990 = lean_ctor_get(x_1962, 1);
lean_inc(x_1990);
lean_dec(x_1962);
x_1991 = lean_st_ref_get(x_11, x_1990);
x_1992 = lean_ctor_get(x_1991, 0);
lean_inc(x_1992);
x_1993 = lean_ctor_get(x_1992, 3);
lean_inc(x_1993);
lean_dec(x_1992);
x_1994 = lean_ctor_get_uint8(x_1993, sizeof(void*)*1);
lean_dec(x_1993);
if (x_1994 == 0)
{
lean_object* x_1995; uint8_t x_1996; 
x_1995 = lean_ctor_get(x_1991, 1);
lean_inc(x_1995);
lean_dec(x_1991);
x_1996 = 0;
x_1945 = x_1996;
x_1946 = x_1995;
goto block_1955;
}
else
{
lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; uint8_t x_2002; 
x_1997 = lean_ctor_get(x_1991, 1);
lean_inc(x_1997);
lean_dec(x_1991);
x_1998 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1999 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_1998, x_8, x_9, x_10, x_11, x_1997);
x_2000 = lean_ctor_get(x_1999, 0);
lean_inc(x_2000);
x_2001 = lean_ctor_get(x_1999, 1);
lean_inc(x_2001);
lean_dec(x_1999);
x_2002 = lean_unbox(x_2000);
lean_dec(x_2000);
x_1945 = x_2002;
x_1946 = x_2001;
goto block_1955;
}
}
}
else
{
uint8_t x_2003; 
lean_dec(x_1908);
lean_dec(x_1906);
lean_dec(x_1903);
lean_dec(x_1890);
lean_dec(x_1889);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2003 = !lean_is_exclusive(x_1962);
if (x_2003 == 0)
{
lean_object* x_2004; 
x_2004 = lean_ctor_get(x_1962, 0);
lean_dec(x_2004);
lean_ctor_set_tag(x_1962, 0);
lean_ctor_set(x_1962, 0, x_3);
return x_1962;
}
else
{
lean_object* x_2005; lean_object* x_2006; 
x_2005 = lean_ctor_get(x_1962, 1);
lean_inc(x_2005);
lean_dec(x_1962);
x_2006 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2006, 0, x_3);
lean_ctor_set(x_2006, 1, x_2005);
return x_2006;
}
}
}
else
{
lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; uint8_t x_2011; 
x_2007 = lean_ctor_get(x_1956, 1);
lean_inc(x_2007);
lean_dec(x_1956);
x_2008 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2009 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2008, x_8, x_9, x_10, x_11, x_2007);
x_2010 = lean_ctor_get(x_2009, 0);
lean_inc(x_2010);
x_2011 = lean_unbox(x_2010);
lean_dec(x_2010);
if (x_2011 == 0)
{
lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; 
lean_dec(x_1943);
x_2012 = lean_ctor_get(x_2009, 1);
lean_inc(x_2012);
lean_dec(x_2009);
x_2013 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2014 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1909, x_2013, x_8, x_9, x_10, x_11, x_2012);
if (lean_obj_tag(x_2014) == 0)
{
lean_object* x_2015; uint8_t x_2016; 
x_2015 = lean_ctor_get(x_2014, 0);
lean_inc(x_2015);
x_2016 = lean_unbox(x_2015);
lean_dec(x_2015);
if (x_2016 == 0)
{
lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; uint8_t x_2021; 
lean_dec(x_1908);
lean_dec(x_1906);
lean_dec(x_1903);
lean_dec(x_1890);
lean_dec(x_1889);
x_2017 = lean_ctor_get(x_2014, 1);
lean_inc(x_2017);
lean_dec(x_2014);
x_2018 = lean_st_ref_get(x_11, x_2017);
x_2019 = lean_ctor_get(x_2018, 0);
lean_inc(x_2019);
x_2020 = lean_ctor_get(x_2019, 3);
lean_inc(x_2020);
lean_dec(x_2019);
x_2021 = lean_ctor_get_uint8(x_2020, sizeof(void*)*1);
lean_dec(x_2020);
if (x_2021 == 0)
{
uint8_t x_2022; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2022 = !lean_is_exclusive(x_2018);
if (x_2022 == 0)
{
lean_object* x_2023; 
x_2023 = lean_ctor_get(x_2018, 0);
lean_dec(x_2023);
lean_ctor_set(x_2018, 0, x_3);
return x_2018;
}
else
{
lean_object* x_2024; lean_object* x_2025; 
x_2024 = lean_ctor_get(x_2018, 1);
lean_inc(x_2024);
lean_dec(x_2018);
x_2025 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2025, 0, x_3);
lean_ctor_set(x_2025, 1, x_2024);
return x_2025;
}
}
else
{
lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; uint8_t x_2029; 
x_2026 = lean_ctor_get(x_2018, 1);
lean_inc(x_2026);
lean_dec(x_2018);
x_2027 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2008, x_8, x_9, x_10, x_11, x_2026);
x_2028 = lean_ctor_get(x_2027, 0);
lean_inc(x_2028);
x_2029 = lean_unbox(x_2028);
lean_dec(x_2028);
if (x_2029 == 0)
{
uint8_t x_2030; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2030 = !lean_is_exclusive(x_2027);
if (x_2030 == 0)
{
lean_object* x_2031; 
x_2031 = lean_ctor_get(x_2027, 0);
lean_dec(x_2031);
lean_ctor_set(x_2027, 0, x_3);
return x_2027;
}
else
{
lean_object* x_2032; lean_object* x_2033; 
x_2032 = lean_ctor_get(x_2027, 1);
lean_inc(x_2032);
lean_dec(x_2027);
x_2033 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2033, 0, x_3);
lean_ctor_set(x_2033, 1, x_2032);
return x_2033;
}
}
else
{
lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; uint8_t x_2037; 
x_2034 = lean_ctor_get(x_2027, 1);
lean_inc(x_2034);
lean_dec(x_2027);
x_2035 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_2036 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2008, x_2035, x_8, x_9, x_10, x_11, x_2034);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2037 = !lean_is_exclusive(x_2036);
if (x_2037 == 0)
{
lean_object* x_2038; 
x_2038 = lean_ctor_get(x_2036, 0);
lean_dec(x_2038);
lean_ctor_set(x_2036, 0, x_3);
return x_2036;
}
else
{
lean_object* x_2039; lean_object* x_2040; 
x_2039 = lean_ctor_get(x_2036, 1);
lean_inc(x_2039);
lean_dec(x_2036);
x_2040 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2040, 0, x_3);
lean_ctor_set(x_2040, 1, x_2039);
return x_2040;
}
}
}
}
else
{
lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; uint8_t x_2045; 
x_2041 = lean_ctor_get(x_2014, 1);
lean_inc(x_2041);
lean_dec(x_2014);
x_2042 = lean_st_ref_get(x_11, x_2041);
x_2043 = lean_ctor_get(x_2042, 0);
lean_inc(x_2043);
x_2044 = lean_ctor_get(x_2043, 3);
lean_inc(x_2044);
lean_dec(x_2043);
x_2045 = lean_ctor_get_uint8(x_2044, sizeof(void*)*1);
lean_dec(x_2044);
if (x_2045 == 0)
{
lean_object* x_2046; uint8_t x_2047; 
x_2046 = lean_ctor_get(x_2042, 1);
lean_inc(x_2046);
lean_dec(x_2042);
x_2047 = 0;
x_1945 = x_2047;
x_1946 = x_2046;
goto block_1955;
}
else
{
lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; uint8_t x_2052; 
x_2048 = lean_ctor_get(x_2042, 1);
lean_inc(x_2048);
lean_dec(x_2042);
x_2049 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2008, x_8, x_9, x_10, x_11, x_2048);
x_2050 = lean_ctor_get(x_2049, 0);
lean_inc(x_2050);
x_2051 = lean_ctor_get(x_2049, 1);
lean_inc(x_2051);
lean_dec(x_2049);
x_2052 = lean_unbox(x_2050);
lean_dec(x_2050);
x_1945 = x_2052;
x_1946 = x_2051;
goto block_1955;
}
}
}
else
{
uint8_t x_2053; 
lean_dec(x_1908);
lean_dec(x_1906);
lean_dec(x_1903);
lean_dec(x_1890);
lean_dec(x_1889);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2053 = !lean_is_exclusive(x_2014);
if (x_2053 == 0)
{
lean_object* x_2054; 
x_2054 = lean_ctor_get(x_2014, 0);
lean_dec(x_2054);
lean_ctor_set_tag(x_2014, 0);
lean_ctor_set(x_2014, 0, x_3);
return x_2014;
}
else
{
lean_object* x_2055; lean_object* x_2056; 
x_2055 = lean_ctor_get(x_2014, 1);
lean_inc(x_2055);
lean_dec(x_2014);
x_2056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2056, 0, x_3);
lean_ctor_set(x_2056, 1, x_2055);
return x_2056;
}
}
}
else
{
lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; 
x_2057 = lean_ctor_get(x_2009, 1);
lean_inc(x_2057);
lean_dec(x_2009);
x_2058 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2058, 0, x_1943);
x_2059 = l_Lean_KernelException_toMessageData___closed__15;
x_2060 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2060, 0, x_2059);
lean_ctor_set(x_2060, 1, x_2058);
x_2061 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2061, 0, x_2060);
lean_ctor_set(x_2061, 1, x_2059);
x_2062 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2008, x_2061, x_8, x_9, x_10, x_11, x_2057);
x_2063 = lean_ctor_get(x_2062, 1);
lean_inc(x_2063);
lean_dec(x_2062);
x_2064 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2065 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_1909, x_2064, x_8, x_9, x_10, x_11, x_2063);
if (lean_obj_tag(x_2065) == 0)
{
lean_object* x_2066; uint8_t x_2067; 
x_2066 = lean_ctor_get(x_2065, 0);
lean_inc(x_2066);
x_2067 = lean_unbox(x_2066);
lean_dec(x_2066);
if (x_2067 == 0)
{
lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; uint8_t x_2072; 
lean_dec(x_1908);
lean_dec(x_1906);
lean_dec(x_1903);
lean_dec(x_1890);
lean_dec(x_1889);
x_2068 = lean_ctor_get(x_2065, 1);
lean_inc(x_2068);
lean_dec(x_2065);
x_2069 = lean_st_ref_get(x_11, x_2068);
x_2070 = lean_ctor_get(x_2069, 0);
lean_inc(x_2070);
x_2071 = lean_ctor_get(x_2070, 3);
lean_inc(x_2071);
lean_dec(x_2070);
x_2072 = lean_ctor_get_uint8(x_2071, sizeof(void*)*1);
lean_dec(x_2071);
if (x_2072 == 0)
{
uint8_t x_2073; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2073 = !lean_is_exclusive(x_2069);
if (x_2073 == 0)
{
lean_object* x_2074; 
x_2074 = lean_ctor_get(x_2069, 0);
lean_dec(x_2074);
lean_ctor_set(x_2069, 0, x_3);
return x_2069;
}
else
{
lean_object* x_2075; lean_object* x_2076; 
x_2075 = lean_ctor_get(x_2069, 1);
lean_inc(x_2075);
lean_dec(x_2069);
x_2076 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2076, 0, x_3);
lean_ctor_set(x_2076, 1, x_2075);
return x_2076;
}
}
else
{
lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; uint8_t x_2080; 
x_2077 = lean_ctor_get(x_2069, 1);
lean_inc(x_2077);
lean_dec(x_2069);
x_2078 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2008, x_8, x_9, x_10, x_11, x_2077);
x_2079 = lean_ctor_get(x_2078, 0);
lean_inc(x_2079);
x_2080 = lean_unbox(x_2079);
lean_dec(x_2079);
if (x_2080 == 0)
{
uint8_t x_2081; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2081 = !lean_is_exclusive(x_2078);
if (x_2081 == 0)
{
lean_object* x_2082; 
x_2082 = lean_ctor_get(x_2078, 0);
lean_dec(x_2082);
lean_ctor_set(x_2078, 0, x_3);
return x_2078;
}
else
{
lean_object* x_2083; lean_object* x_2084; 
x_2083 = lean_ctor_get(x_2078, 1);
lean_inc(x_2083);
lean_dec(x_2078);
x_2084 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2084, 0, x_3);
lean_ctor_set(x_2084, 1, x_2083);
return x_2084;
}
}
else
{
lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; uint8_t x_2088; 
x_2085 = lean_ctor_get(x_2078, 1);
lean_inc(x_2085);
lean_dec(x_2078);
x_2086 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_2087 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2008, x_2086, x_8, x_9, x_10, x_11, x_2085);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2088 = !lean_is_exclusive(x_2087);
if (x_2088 == 0)
{
lean_object* x_2089; 
x_2089 = lean_ctor_get(x_2087, 0);
lean_dec(x_2089);
lean_ctor_set(x_2087, 0, x_3);
return x_2087;
}
else
{
lean_object* x_2090; lean_object* x_2091; 
x_2090 = lean_ctor_get(x_2087, 1);
lean_inc(x_2090);
lean_dec(x_2087);
x_2091 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2091, 0, x_3);
lean_ctor_set(x_2091, 1, x_2090);
return x_2091;
}
}
}
}
else
{
lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; uint8_t x_2096; 
x_2092 = lean_ctor_get(x_2065, 1);
lean_inc(x_2092);
lean_dec(x_2065);
x_2093 = lean_st_ref_get(x_11, x_2092);
x_2094 = lean_ctor_get(x_2093, 0);
lean_inc(x_2094);
x_2095 = lean_ctor_get(x_2094, 3);
lean_inc(x_2095);
lean_dec(x_2094);
x_2096 = lean_ctor_get_uint8(x_2095, sizeof(void*)*1);
lean_dec(x_2095);
if (x_2096 == 0)
{
lean_object* x_2097; uint8_t x_2098; 
x_2097 = lean_ctor_get(x_2093, 1);
lean_inc(x_2097);
lean_dec(x_2093);
x_2098 = 0;
x_1945 = x_2098;
x_1946 = x_2097;
goto block_1955;
}
else
{
lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; uint8_t x_2103; 
x_2099 = lean_ctor_get(x_2093, 1);
lean_inc(x_2099);
lean_dec(x_2093);
x_2100 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2008, x_8, x_9, x_10, x_11, x_2099);
x_2101 = lean_ctor_get(x_2100, 0);
lean_inc(x_2101);
x_2102 = lean_ctor_get(x_2100, 1);
lean_inc(x_2102);
lean_dec(x_2100);
x_2103 = lean_unbox(x_2101);
lean_dec(x_2101);
x_1945 = x_2103;
x_1946 = x_2102;
goto block_1955;
}
}
}
else
{
uint8_t x_2104; 
lean_dec(x_1908);
lean_dec(x_1906);
lean_dec(x_1903);
lean_dec(x_1890);
lean_dec(x_1889);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2104 = !lean_is_exclusive(x_2065);
if (x_2104 == 0)
{
lean_object* x_2105; 
x_2105 = lean_ctor_get(x_2065, 0);
lean_dec(x_2105);
lean_ctor_set_tag(x_2065, 0);
lean_ctor_set(x_2065, 0, x_3);
return x_2065;
}
else
{
lean_object* x_2106; lean_object* x_2107; 
x_2106 = lean_ctor_get(x_2065, 1);
lean_inc(x_2106);
lean_dec(x_2065);
x_2107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2107, 0, x_3);
lean_ctor_set(x_2107, 1, x_2106);
return x_2107;
}
}
}
}
block_1955:
{
if (x_1945 == 0)
{
x_1910 = x_1946;
goto block_1941;
}
else
{
lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; 
lean_inc(x_1906);
x_1947 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_1947, 0, x_1906);
x_1948 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_1949 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1949, 0, x_1948);
lean_ctor_set(x_1949, 1, x_1947);
x_1950 = l_Lean_KernelException_toMessageData___closed__15;
x_1951 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_1951, 0, x_1949);
lean_ctor_set(x_1951, 1, x_1950);
x_1952 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_1953 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_1952, x_1951, x_8, x_9, x_10, x_11, x_1946);
x_1954 = lean_ctor_get(x_1953, 1);
lean_inc(x_1954);
lean_dec(x_1953);
x_1910 = x_1954;
goto block_1941;
}
}
}
else
{
uint8_t x_2108; 
lean_dec(x_1909);
lean_dec(x_1908);
lean_dec(x_1906);
lean_dec(x_1903);
lean_dec(x_1890);
lean_dec(x_1889);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2108 = !lean_is_exclusive(x_1942);
if (x_2108 == 0)
{
lean_object* x_2109; 
x_2109 = lean_ctor_get(x_1942, 0);
lean_dec(x_2109);
lean_ctor_set_tag(x_1942, 0);
lean_ctor_set(x_1942, 0, x_3);
return x_1942;
}
else
{
lean_object* x_2110; lean_object* x_2111; 
x_2110 = lean_ctor_get(x_1942, 1);
lean_inc(x_2110);
lean_dec(x_1942);
x_2111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2111, 0, x_3);
lean_ctor_set(x_2111, 1, x_2110);
return x_2111;
}
}
block_1941:
{
lean_object* x_1911; uint8_t x_1912; 
x_1911 = lean_array_get_size(x_1);
x_1912 = lean_nat_dec_lt(x_1886, x_1911);
if (x_1912 == 0)
{
lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; 
lean_dec(x_1911);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1903)) {
 x_1913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1913 = x_1903;
}
lean_ctor_set(x_1913, 0, x_1906);
lean_ctor_set(x_1913, 1, x_1889);
if (lean_is_scalar(x_1890)) {
 x_1914 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1914 = x_1890;
}
lean_ctor_set(x_1914, 0, x_1913);
if (lean_is_scalar(x_1908)) {
 x_1915 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1915 = x_1908;
}
lean_ctor_set(x_1915, 0, x_1914);
lean_ctor_set(x_1915, 1, x_1910);
return x_1915;
}
else
{
uint8_t x_1916; 
x_1916 = lean_nat_dec_le(x_1911, x_1911);
if (x_1916 == 0)
{
lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; 
lean_dec(x_1911);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_1903)) {
 x_1917 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1917 = x_1903;
}
lean_ctor_set(x_1917, 0, x_1906);
lean_ctor_set(x_1917, 1, x_1889);
if (lean_is_scalar(x_1890)) {
 x_1918 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1918 = x_1890;
}
lean_ctor_set(x_1918, 0, x_1917);
if (lean_is_scalar(x_1908)) {
 x_1919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1919 = x_1908;
}
lean_ctor_set(x_1919, 0, x_1918);
lean_ctor_set(x_1919, 1, x_1910);
return x_1919;
}
else
{
size_t x_1920; size_t x_1921; lean_object* x_1922; 
lean_dec(x_1908);
x_1920 = 0;
x_1921 = lean_usize_of_nat(x_1911);
lean_dec(x_1911);
lean_inc(x_1906);
x_1922 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_1906, x_1, x_1920, x_1921, x_8, x_9, x_10, x_11, x_1910);
if (lean_obj_tag(x_1922) == 0)
{
lean_object* x_1923; uint8_t x_1924; 
x_1923 = lean_ctor_get(x_1922, 0);
lean_inc(x_1923);
x_1924 = lean_unbox(x_1923);
lean_dec(x_1923);
if (x_1924 == 0)
{
uint8_t x_1925; 
lean_dec(x_3);
x_1925 = !lean_is_exclusive(x_1922);
if (x_1925 == 0)
{
lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; 
x_1926 = lean_ctor_get(x_1922, 0);
lean_dec(x_1926);
if (lean_is_scalar(x_1903)) {
 x_1927 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1927 = x_1903;
}
lean_ctor_set(x_1927, 0, x_1906);
lean_ctor_set(x_1927, 1, x_1889);
if (lean_is_scalar(x_1890)) {
 x_1928 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1928 = x_1890;
}
lean_ctor_set(x_1928, 0, x_1927);
lean_ctor_set(x_1922, 0, x_1928);
return x_1922;
}
else
{
lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; 
x_1929 = lean_ctor_get(x_1922, 1);
lean_inc(x_1929);
lean_dec(x_1922);
if (lean_is_scalar(x_1903)) {
 x_1930 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1930 = x_1903;
}
lean_ctor_set(x_1930, 0, x_1906);
lean_ctor_set(x_1930, 1, x_1889);
if (lean_is_scalar(x_1890)) {
 x_1931 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1931 = x_1890;
}
lean_ctor_set(x_1931, 0, x_1930);
x_1932 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1932, 0, x_1931);
lean_ctor_set(x_1932, 1, x_1929);
return x_1932;
}
}
else
{
uint8_t x_1933; 
lean_dec(x_1906);
lean_dec(x_1903);
lean_dec(x_1890);
lean_dec(x_1889);
x_1933 = !lean_is_exclusive(x_1922);
if (x_1933 == 0)
{
lean_object* x_1934; 
x_1934 = lean_ctor_get(x_1922, 0);
lean_dec(x_1934);
lean_ctor_set(x_1922, 0, x_3);
return x_1922;
}
else
{
lean_object* x_1935; lean_object* x_1936; 
x_1935 = lean_ctor_get(x_1922, 1);
lean_inc(x_1935);
lean_dec(x_1922);
x_1936 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1936, 0, x_3);
lean_ctor_set(x_1936, 1, x_1935);
return x_1936;
}
}
}
else
{
uint8_t x_1937; 
lean_dec(x_1906);
lean_dec(x_1903);
lean_dec(x_1890);
lean_dec(x_1889);
x_1937 = !lean_is_exclusive(x_1922);
if (x_1937 == 0)
{
lean_object* x_1938; 
x_1938 = lean_ctor_get(x_1922, 0);
lean_dec(x_1938);
lean_ctor_set_tag(x_1922, 0);
lean_ctor_set(x_1922, 0, x_3);
return x_1922;
}
else
{
lean_object* x_1939; lean_object* x_1940; 
x_1939 = lean_ctor_get(x_1922, 1);
lean_inc(x_1939);
lean_dec(x_1922);
x_1940 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1940, 0, x_3);
lean_ctor_set(x_1940, 1, x_1939);
return x_1940;
}
}
}
}
}
}
else
{
uint8_t x_2112; 
lean_dec(x_1890);
lean_dec(x_1889);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_2112 = !lean_is_exclusive(x_1899);
if (x_2112 == 0)
{
return x_1899;
}
else
{
lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; 
x_2113 = lean_ctor_get(x_1899, 0);
x_2114 = lean_ctor_get(x_1899, 1);
lean_inc(x_2114);
lean_inc(x_2113);
lean_dec(x_1899);
x_2115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2115, 0, x_2113);
lean_ctor_set(x_2115, 1, x_2114);
return x_2115;
}
}
}
}
}
}
case 10:
{
lean_object* x_2116; 
lean_dec(x_7);
lean_dec(x_6);
x_2116 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_2116) == 0)
{
lean_object* x_2117; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_2117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2117, 0, x_3);
lean_ctor_set(x_2117, 1, x_12);
return x_2117;
}
else
{
lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; 
x_2118 = lean_ctor_get(x_2116, 0);
lean_inc(x_2118);
lean_dec(x_2116);
x_2119 = lean_unsigned_to_nat(0u);
x_2120 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_2119);
if (lean_obj_tag(x_2120) == 0)
{
lean_object* x_2121; 
lean_dec(x_2118);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_2121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2121, 0, x_3);
lean_ctor_set(x_2121, 1, x_12);
return x_2121;
}
else
{
lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; uint8_t x_2126; 
x_2122 = lean_ctor_get(x_2120, 0);
lean_inc(x_2122);
if (lean_is_exclusive(x_2120)) {
 lean_ctor_release(x_2120, 0);
 x_2123 = x_2120;
} else {
 lean_dec_ref(x_2120);
 x_2123 = lean_box(0);
}
x_2124 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_2118, x_8, x_9, x_10, x_11, x_12);
x_2125 = lean_ctor_get(x_2124, 0);
lean_inc(x_2125);
x_2126 = lean_unbox(x_2125);
lean_dec(x_2125);
if (x_2126 == 0)
{
uint8_t x_2127; 
lean_dec(x_2123);
lean_dec(x_2122);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_2127 = !lean_is_exclusive(x_2124);
if (x_2127 == 0)
{
lean_object* x_2128; 
x_2128 = lean_ctor_get(x_2124, 0);
lean_dec(x_2128);
lean_ctor_set(x_2124, 0, x_3);
return x_2124;
}
else
{
lean_object* x_2129; lean_object* x_2130; 
x_2129 = lean_ctor_get(x_2124, 1);
lean_inc(x_2129);
lean_dec(x_2124);
x_2130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2130, 0, x_3);
lean_ctor_set(x_2130, 1, x_2129);
return x_2130;
}
}
else
{
lean_object* x_2131; lean_object* x_2132; 
x_2131 = lean_ctor_get(x_2124, 1);
lean_inc(x_2131);
lean_dec(x_2124);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2132 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_2122, x_8, x_9, x_10, x_11, x_2131);
if (lean_obj_tag(x_2132) == 0)
{
lean_object* x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2175; 
x_2133 = lean_ctor_get(x_2132, 0);
lean_inc(x_2133);
x_2134 = lean_ctor_get(x_2132, 1);
lean_inc(x_2134);
lean_dec(x_2132);
x_2135 = lean_ctor_get(x_2133, 1);
lean_inc(x_2135);
if (lean_is_exclusive(x_2133)) {
 lean_ctor_release(x_2133, 0);
 lean_ctor_release(x_2133, 1);
 x_2136 = x_2133;
} else {
 lean_dec_ref(x_2133);
 x_2136 = lean_box(0);
}
x_2137 = lean_box(0);
lean_inc(x_8);
x_2138 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2135, x_2137, x_8, x_9, x_10, x_11, x_2134);
x_2139 = lean_ctor_get(x_2138, 0);
lean_inc(x_2139);
x_2140 = lean_ctor_get(x_2138, 1);
lean_inc(x_2140);
if (lean_is_exclusive(x_2138)) {
 lean_ctor_release(x_2138, 0);
 lean_ctor_release(x_2138, 1);
 x_2141 = x_2138;
} else {
 lean_dec_ref(x_2138);
 x_2141 = lean_box(0);
}
x_2142 = l_Lean_Expr_mvarId_x21(x_2139);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2175 = l_Lean_Meta_ppGoal(x_2142, x_8, x_9, x_10, x_11, x_2140);
if (lean_obj_tag(x_2175) == 0)
{
lean_object* x_2176; lean_object* x_2177; uint8_t x_2178; lean_object* x_2179; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; uint8_t x_2192; 
x_2176 = lean_ctor_get(x_2175, 0);
lean_inc(x_2176);
x_2177 = lean_ctor_get(x_2175, 1);
lean_inc(x_2177);
lean_dec(x_2175);
x_2189 = lean_st_ref_get(x_11, x_2177);
x_2190 = lean_ctor_get(x_2189, 0);
lean_inc(x_2190);
x_2191 = lean_ctor_get(x_2190, 3);
lean_inc(x_2191);
lean_dec(x_2190);
x_2192 = lean_ctor_get_uint8(x_2191, sizeof(void*)*1);
lean_dec(x_2191);
if (x_2192 == 0)
{
lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; 
lean_dec(x_2176);
x_2193 = lean_ctor_get(x_2189, 1);
lean_inc(x_2193);
lean_dec(x_2189);
x_2194 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2195 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_2142, x_2194, x_8, x_9, x_10, x_11, x_2193);
if (lean_obj_tag(x_2195) == 0)
{
lean_object* x_2196; uint8_t x_2197; 
x_2196 = lean_ctor_get(x_2195, 0);
lean_inc(x_2196);
x_2197 = lean_unbox(x_2196);
lean_dec(x_2196);
if (x_2197 == 0)
{
lean_object* x_2198; lean_object* x_2199; lean_object* x_2200; lean_object* x_2201; uint8_t x_2202; 
lean_dec(x_2141);
lean_dec(x_2139);
lean_dec(x_2136);
lean_dec(x_2123);
lean_dec(x_2122);
x_2198 = lean_ctor_get(x_2195, 1);
lean_inc(x_2198);
lean_dec(x_2195);
x_2199 = lean_st_ref_get(x_11, x_2198);
x_2200 = lean_ctor_get(x_2199, 0);
lean_inc(x_2200);
x_2201 = lean_ctor_get(x_2200, 3);
lean_inc(x_2201);
lean_dec(x_2200);
x_2202 = lean_ctor_get_uint8(x_2201, sizeof(void*)*1);
lean_dec(x_2201);
if (x_2202 == 0)
{
uint8_t x_2203; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2203 = !lean_is_exclusive(x_2199);
if (x_2203 == 0)
{
lean_object* x_2204; 
x_2204 = lean_ctor_get(x_2199, 0);
lean_dec(x_2204);
lean_ctor_set(x_2199, 0, x_3);
return x_2199;
}
else
{
lean_object* x_2205; lean_object* x_2206; 
x_2205 = lean_ctor_get(x_2199, 1);
lean_inc(x_2205);
lean_dec(x_2199);
x_2206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2206, 0, x_3);
lean_ctor_set(x_2206, 1, x_2205);
return x_2206;
}
}
else
{
lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; uint8_t x_2211; 
x_2207 = lean_ctor_get(x_2199, 1);
lean_inc(x_2207);
lean_dec(x_2199);
x_2208 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2209 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2208, x_8, x_9, x_10, x_11, x_2207);
x_2210 = lean_ctor_get(x_2209, 0);
lean_inc(x_2210);
x_2211 = lean_unbox(x_2210);
lean_dec(x_2210);
if (x_2211 == 0)
{
uint8_t x_2212; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2212 = !lean_is_exclusive(x_2209);
if (x_2212 == 0)
{
lean_object* x_2213; 
x_2213 = lean_ctor_get(x_2209, 0);
lean_dec(x_2213);
lean_ctor_set(x_2209, 0, x_3);
return x_2209;
}
else
{
lean_object* x_2214; lean_object* x_2215; 
x_2214 = lean_ctor_get(x_2209, 1);
lean_inc(x_2214);
lean_dec(x_2209);
x_2215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2215, 0, x_3);
lean_ctor_set(x_2215, 1, x_2214);
return x_2215;
}
}
else
{
lean_object* x_2216; lean_object* x_2217; lean_object* x_2218; uint8_t x_2219; 
x_2216 = lean_ctor_get(x_2209, 1);
lean_inc(x_2216);
lean_dec(x_2209);
x_2217 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_2218 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2208, x_2217, x_8, x_9, x_10, x_11, x_2216);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2219 = !lean_is_exclusive(x_2218);
if (x_2219 == 0)
{
lean_object* x_2220; 
x_2220 = lean_ctor_get(x_2218, 0);
lean_dec(x_2220);
lean_ctor_set(x_2218, 0, x_3);
return x_2218;
}
else
{
lean_object* x_2221; lean_object* x_2222; 
x_2221 = lean_ctor_get(x_2218, 1);
lean_inc(x_2221);
lean_dec(x_2218);
x_2222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2222, 0, x_3);
lean_ctor_set(x_2222, 1, x_2221);
return x_2222;
}
}
}
}
else
{
lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; uint8_t x_2227; 
x_2223 = lean_ctor_get(x_2195, 1);
lean_inc(x_2223);
lean_dec(x_2195);
x_2224 = lean_st_ref_get(x_11, x_2223);
x_2225 = lean_ctor_get(x_2224, 0);
lean_inc(x_2225);
x_2226 = lean_ctor_get(x_2225, 3);
lean_inc(x_2226);
lean_dec(x_2225);
x_2227 = lean_ctor_get_uint8(x_2226, sizeof(void*)*1);
lean_dec(x_2226);
if (x_2227 == 0)
{
lean_object* x_2228; uint8_t x_2229; 
x_2228 = lean_ctor_get(x_2224, 1);
lean_inc(x_2228);
lean_dec(x_2224);
x_2229 = 0;
x_2178 = x_2229;
x_2179 = x_2228;
goto block_2188;
}
else
{
lean_object* x_2230; lean_object* x_2231; lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; uint8_t x_2235; 
x_2230 = lean_ctor_get(x_2224, 1);
lean_inc(x_2230);
lean_dec(x_2224);
x_2231 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2232 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2231, x_8, x_9, x_10, x_11, x_2230);
x_2233 = lean_ctor_get(x_2232, 0);
lean_inc(x_2233);
x_2234 = lean_ctor_get(x_2232, 1);
lean_inc(x_2234);
lean_dec(x_2232);
x_2235 = lean_unbox(x_2233);
lean_dec(x_2233);
x_2178 = x_2235;
x_2179 = x_2234;
goto block_2188;
}
}
}
else
{
uint8_t x_2236; 
lean_dec(x_2141);
lean_dec(x_2139);
lean_dec(x_2136);
lean_dec(x_2123);
lean_dec(x_2122);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2236 = !lean_is_exclusive(x_2195);
if (x_2236 == 0)
{
lean_object* x_2237; 
x_2237 = lean_ctor_get(x_2195, 0);
lean_dec(x_2237);
lean_ctor_set_tag(x_2195, 0);
lean_ctor_set(x_2195, 0, x_3);
return x_2195;
}
else
{
lean_object* x_2238; lean_object* x_2239; 
x_2238 = lean_ctor_get(x_2195, 1);
lean_inc(x_2238);
lean_dec(x_2195);
x_2239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2239, 0, x_3);
lean_ctor_set(x_2239, 1, x_2238);
return x_2239;
}
}
}
else
{
lean_object* x_2240; lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; uint8_t x_2244; 
x_2240 = lean_ctor_get(x_2189, 1);
lean_inc(x_2240);
lean_dec(x_2189);
x_2241 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2242 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2241, x_8, x_9, x_10, x_11, x_2240);
x_2243 = lean_ctor_get(x_2242, 0);
lean_inc(x_2243);
x_2244 = lean_unbox(x_2243);
lean_dec(x_2243);
if (x_2244 == 0)
{
lean_object* x_2245; lean_object* x_2246; lean_object* x_2247; 
lean_dec(x_2176);
x_2245 = lean_ctor_get(x_2242, 1);
lean_inc(x_2245);
lean_dec(x_2242);
x_2246 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2247 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_2142, x_2246, x_8, x_9, x_10, x_11, x_2245);
if (lean_obj_tag(x_2247) == 0)
{
lean_object* x_2248; uint8_t x_2249; 
x_2248 = lean_ctor_get(x_2247, 0);
lean_inc(x_2248);
x_2249 = lean_unbox(x_2248);
lean_dec(x_2248);
if (x_2249 == 0)
{
lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; uint8_t x_2254; 
lean_dec(x_2141);
lean_dec(x_2139);
lean_dec(x_2136);
lean_dec(x_2123);
lean_dec(x_2122);
x_2250 = lean_ctor_get(x_2247, 1);
lean_inc(x_2250);
lean_dec(x_2247);
x_2251 = lean_st_ref_get(x_11, x_2250);
x_2252 = lean_ctor_get(x_2251, 0);
lean_inc(x_2252);
x_2253 = lean_ctor_get(x_2252, 3);
lean_inc(x_2253);
lean_dec(x_2252);
x_2254 = lean_ctor_get_uint8(x_2253, sizeof(void*)*1);
lean_dec(x_2253);
if (x_2254 == 0)
{
uint8_t x_2255; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2255 = !lean_is_exclusive(x_2251);
if (x_2255 == 0)
{
lean_object* x_2256; 
x_2256 = lean_ctor_get(x_2251, 0);
lean_dec(x_2256);
lean_ctor_set(x_2251, 0, x_3);
return x_2251;
}
else
{
lean_object* x_2257; lean_object* x_2258; 
x_2257 = lean_ctor_get(x_2251, 1);
lean_inc(x_2257);
lean_dec(x_2251);
x_2258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2258, 0, x_3);
lean_ctor_set(x_2258, 1, x_2257);
return x_2258;
}
}
else
{
lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; uint8_t x_2262; 
x_2259 = lean_ctor_get(x_2251, 1);
lean_inc(x_2259);
lean_dec(x_2251);
x_2260 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2241, x_8, x_9, x_10, x_11, x_2259);
x_2261 = lean_ctor_get(x_2260, 0);
lean_inc(x_2261);
x_2262 = lean_unbox(x_2261);
lean_dec(x_2261);
if (x_2262 == 0)
{
uint8_t x_2263; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2263 = !lean_is_exclusive(x_2260);
if (x_2263 == 0)
{
lean_object* x_2264; 
x_2264 = lean_ctor_get(x_2260, 0);
lean_dec(x_2264);
lean_ctor_set(x_2260, 0, x_3);
return x_2260;
}
else
{
lean_object* x_2265; lean_object* x_2266; 
x_2265 = lean_ctor_get(x_2260, 1);
lean_inc(x_2265);
lean_dec(x_2260);
x_2266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2266, 0, x_3);
lean_ctor_set(x_2266, 1, x_2265);
return x_2266;
}
}
else
{
lean_object* x_2267; lean_object* x_2268; lean_object* x_2269; uint8_t x_2270; 
x_2267 = lean_ctor_get(x_2260, 1);
lean_inc(x_2267);
lean_dec(x_2260);
x_2268 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_2269 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2241, x_2268, x_8, x_9, x_10, x_11, x_2267);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2270 = !lean_is_exclusive(x_2269);
if (x_2270 == 0)
{
lean_object* x_2271; 
x_2271 = lean_ctor_get(x_2269, 0);
lean_dec(x_2271);
lean_ctor_set(x_2269, 0, x_3);
return x_2269;
}
else
{
lean_object* x_2272; lean_object* x_2273; 
x_2272 = lean_ctor_get(x_2269, 1);
lean_inc(x_2272);
lean_dec(x_2269);
x_2273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2273, 0, x_3);
lean_ctor_set(x_2273, 1, x_2272);
return x_2273;
}
}
}
}
else
{
lean_object* x_2274; lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; uint8_t x_2278; 
x_2274 = lean_ctor_get(x_2247, 1);
lean_inc(x_2274);
lean_dec(x_2247);
x_2275 = lean_st_ref_get(x_11, x_2274);
x_2276 = lean_ctor_get(x_2275, 0);
lean_inc(x_2276);
x_2277 = lean_ctor_get(x_2276, 3);
lean_inc(x_2277);
lean_dec(x_2276);
x_2278 = lean_ctor_get_uint8(x_2277, sizeof(void*)*1);
lean_dec(x_2277);
if (x_2278 == 0)
{
lean_object* x_2279; uint8_t x_2280; 
x_2279 = lean_ctor_get(x_2275, 1);
lean_inc(x_2279);
lean_dec(x_2275);
x_2280 = 0;
x_2178 = x_2280;
x_2179 = x_2279;
goto block_2188;
}
else
{
lean_object* x_2281; lean_object* x_2282; lean_object* x_2283; lean_object* x_2284; uint8_t x_2285; 
x_2281 = lean_ctor_get(x_2275, 1);
lean_inc(x_2281);
lean_dec(x_2275);
x_2282 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2241, x_8, x_9, x_10, x_11, x_2281);
x_2283 = lean_ctor_get(x_2282, 0);
lean_inc(x_2283);
x_2284 = lean_ctor_get(x_2282, 1);
lean_inc(x_2284);
lean_dec(x_2282);
x_2285 = lean_unbox(x_2283);
lean_dec(x_2283);
x_2178 = x_2285;
x_2179 = x_2284;
goto block_2188;
}
}
}
else
{
uint8_t x_2286; 
lean_dec(x_2141);
lean_dec(x_2139);
lean_dec(x_2136);
lean_dec(x_2123);
lean_dec(x_2122);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2286 = !lean_is_exclusive(x_2247);
if (x_2286 == 0)
{
lean_object* x_2287; 
x_2287 = lean_ctor_get(x_2247, 0);
lean_dec(x_2287);
lean_ctor_set_tag(x_2247, 0);
lean_ctor_set(x_2247, 0, x_3);
return x_2247;
}
else
{
lean_object* x_2288; lean_object* x_2289; 
x_2288 = lean_ctor_get(x_2247, 1);
lean_inc(x_2288);
lean_dec(x_2247);
x_2289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2289, 0, x_3);
lean_ctor_set(x_2289, 1, x_2288);
return x_2289;
}
}
}
else
{
lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; 
x_2290 = lean_ctor_get(x_2242, 1);
lean_inc(x_2290);
lean_dec(x_2242);
x_2291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2291, 0, x_2176);
x_2292 = l_Lean_KernelException_toMessageData___closed__15;
x_2293 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2293, 0, x_2292);
lean_ctor_set(x_2293, 1, x_2291);
x_2294 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2294, 0, x_2293);
lean_ctor_set(x_2294, 1, x_2292);
x_2295 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2241, x_2294, x_8, x_9, x_10, x_11, x_2290);
x_2296 = lean_ctor_get(x_2295, 1);
lean_inc(x_2296);
lean_dec(x_2295);
x_2297 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2298 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_2142, x_2297, x_8, x_9, x_10, x_11, x_2296);
if (lean_obj_tag(x_2298) == 0)
{
lean_object* x_2299; uint8_t x_2300; 
x_2299 = lean_ctor_get(x_2298, 0);
lean_inc(x_2299);
x_2300 = lean_unbox(x_2299);
lean_dec(x_2299);
if (x_2300 == 0)
{
lean_object* x_2301; lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; uint8_t x_2305; 
lean_dec(x_2141);
lean_dec(x_2139);
lean_dec(x_2136);
lean_dec(x_2123);
lean_dec(x_2122);
x_2301 = lean_ctor_get(x_2298, 1);
lean_inc(x_2301);
lean_dec(x_2298);
x_2302 = lean_st_ref_get(x_11, x_2301);
x_2303 = lean_ctor_get(x_2302, 0);
lean_inc(x_2303);
x_2304 = lean_ctor_get(x_2303, 3);
lean_inc(x_2304);
lean_dec(x_2303);
x_2305 = lean_ctor_get_uint8(x_2304, sizeof(void*)*1);
lean_dec(x_2304);
if (x_2305 == 0)
{
uint8_t x_2306; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2306 = !lean_is_exclusive(x_2302);
if (x_2306 == 0)
{
lean_object* x_2307; 
x_2307 = lean_ctor_get(x_2302, 0);
lean_dec(x_2307);
lean_ctor_set(x_2302, 0, x_3);
return x_2302;
}
else
{
lean_object* x_2308; lean_object* x_2309; 
x_2308 = lean_ctor_get(x_2302, 1);
lean_inc(x_2308);
lean_dec(x_2302);
x_2309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2309, 0, x_3);
lean_ctor_set(x_2309, 1, x_2308);
return x_2309;
}
}
else
{
lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; uint8_t x_2313; 
x_2310 = lean_ctor_get(x_2302, 1);
lean_inc(x_2310);
lean_dec(x_2302);
x_2311 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2241, x_8, x_9, x_10, x_11, x_2310);
x_2312 = lean_ctor_get(x_2311, 0);
lean_inc(x_2312);
x_2313 = lean_unbox(x_2312);
lean_dec(x_2312);
if (x_2313 == 0)
{
uint8_t x_2314; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2314 = !lean_is_exclusive(x_2311);
if (x_2314 == 0)
{
lean_object* x_2315; 
x_2315 = lean_ctor_get(x_2311, 0);
lean_dec(x_2315);
lean_ctor_set(x_2311, 0, x_3);
return x_2311;
}
else
{
lean_object* x_2316; lean_object* x_2317; 
x_2316 = lean_ctor_get(x_2311, 1);
lean_inc(x_2316);
lean_dec(x_2311);
x_2317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2317, 0, x_3);
lean_ctor_set(x_2317, 1, x_2316);
return x_2317;
}
}
else
{
lean_object* x_2318; lean_object* x_2319; lean_object* x_2320; uint8_t x_2321; 
x_2318 = lean_ctor_get(x_2311, 1);
lean_inc(x_2318);
lean_dec(x_2311);
x_2319 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_2320 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2241, x_2319, x_8, x_9, x_10, x_11, x_2318);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2321 = !lean_is_exclusive(x_2320);
if (x_2321 == 0)
{
lean_object* x_2322; 
x_2322 = lean_ctor_get(x_2320, 0);
lean_dec(x_2322);
lean_ctor_set(x_2320, 0, x_3);
return x_2320;
}
else
{
lean_object* x_2323; lean_object* x_2324; 
x_2323 = lean_ctor_get(x_2320, 1);
lean_inc(x_2323);
lean_dec(x_2320);
x_2324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2324, 0, x_3);
lean_ctor_set(x_2324, 1, x_2323);
return x_2324;
}
}
}
}
else
{
lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; uint8_t x_2329; 
x_2325 = lean_ctor_get(x_2298, 1);
lean_inc(x_2325);
lean_dec(x_2298);
x_2326 = lean_st_ref_get(x_11, x_2325);
x_2327 = lean_ctor_get(x_2326, 0);
lean_inc(x_2327);
x_2328 = lean_ctor_get(x_2327, 3);
lean_inc(x_2328);
lean_dec(x_2327);
x_2329 = lean_ctor_get_uint8(x_2328, sizeof(void*)*1);
lean_dec(x_2328);
if (x_2329 == 0)
{
lean_object* x_2330; uint8_t x_2331; 
x_2330 = lean_ctor_get(x_2326, 1);
lean_inc(x_2330);
lean_dec(x_2326);
x_2331 = 0;
x_2178 = x_2331;
x_2179 = x_2330;
goto block_2188;
}
else
{
lean_object* x_2332; lean_object* x_2333; lean_object* x_2334; lean_object* x_2335; uint8_t x_2336; 
x_2332 = lean_ctor_get(x_2326, 1);
lean_inc(x_2332);
lean_dec(x_2326);
x_2333 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2241, x_8, x_9, x_10, x_11, x_2332);
x_2334 = lean_ctor_get(x_2333, 0);
lean_inc(x_2334);
x_2335 = lean_ctor_get(x_2333, 1);
lean_inc(x_2335);
lean_dec(x_2333);
x_2336 = lean_unbox(x_2334);
lean_dec(x_2334);
x_2178 = x_2336;
x_2179 = x_2335;
goto block_2188;
}
}
}
else
{
uint8_t x_2337; 
lean_dec(x_2141);
lean_dec(x_2139);
lean_dec(x_2136);
lean_dec(x_2123);
lean_dec(x_2122);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2337 = !lean_is_exclusive(x_2298);
if (x_2337 == 0)
{
lean_object* x_2338; 
x_2338 = lean_ctor_get(x_2298, 0);
lean_dec(x_2338);
lean_ctor_set_tag(x_2298, 0);
lean_ctor_set(x_2298, 0, x_3);
return x_2298;
}
else
{
lean_object* x_2339; lean_object* x_2340; 
x_2339 = lean_ctor_get(x_2298, 1);
lean_inc(x_2339);
lean_dec(x_2298);
x_2340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2340, 0, x_3);
lean_ctor_set(x_2340, 1, x_2339);
return x_2340;
}
}
}
}
block_2188:
{
if (x_2178 == 0)
{
x_2143 = x_2179;
goto block_2174;
}
else
{
lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; 
lean_inc(x_2139);
x_2180 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2180, 0, x_2139);
x_2181 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_2182 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2182, 0, x_2181);
lean_ctor_set(x_2182, 1, x_2180);
x_2183 = l_Lean_KernelException_toMessageData___closed__15;
x_2184 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2184, 0, x_2182);
lean_ctor_set(x_2184, 1, x_2183);
x_2185 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2186 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2185, x_2184, x_8, x_9, x_10, x_11, x_2179);
x_2187 = lean_ctor_get(x_2186, 1);
lean_inc(x_2187);
lean_dec(x_2186);
x_2143 = x_2187;
goto block_2174;
}
}
}
else
{
uint8_t x_2341; 
lean_dec(x_2142);
lean_dec(x_2141);
lean_dec(x_2139);
lean_dec(x_2136);
lean_dec(x_2123);
lean_dec(x_2122);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2341 = !lean_is_exclusive(x_2175);
if (x_2341 == 0)
{
lean_object* x_2342; 
x_2342 = lean_ctor_get(x_2175, 0);
lean_dec(x_2342);
lean_ctor_set_tag(x_2175, 0);
lean_ctor_set(x_2175, 0, x_3);
return x_2175;
}
else
{
lean_object* x_2343; lean_object* x_2344; 
x_2343 = lean_ctor_get(x_2175, 1);
lean_inc(x_2343);
lean_dec(x_2175);
x_2344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2344, 0, x_3);
lean_ctor_set(x_2344, 1, x_2343);
return x_2344;
}
}
block_2174:
{
lean_object* x_2144; uint8_t x_2145; 
x_2144 = lean_array_get_size(x_1);
x_2145 = lean_nat_dec_lt(x_2119, x_2144);
if (x_2145 == 0)
{
lean_object* x_2146; lean_object* x_2147; lean_object* x_2148; 
lean_dec(x_2144);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_2136)) {
 x_2146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2146 = x_2136;
}
lean_ctor_set(x_2146, 0, x_2139);
lean_ctor_set(x_2146, 1, x_2122);
if (lean_is_scalar(x_2123)) {
 x_2147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2147 = x_2123;
}
lean_ctor_set(x_2147, 0, x_2146);
if (lean_is_scalar(x_2141)) {
 x_2148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2148 = x_2141;
}
lean_ctor_set(x_2148, 0, x_2147);
lean_ctor_set(x_2148, 1, x_2143);
return x_2148;
}
else
{
uint8_t x_2149; 
x_2149 = lean_nat_dec_le(x_2144, x_2144);
if (x_2149 == 0)
{
lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; 
lean_dec(x_2144);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_2136)) {
 x_2150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2150 = x_2136;
}
lean_ctor_set(x_2150, 0, x_2139);
lean_ctor_set(x_2150, 1, x_2122);
if (lean_is_scalar(x_2123)) {
 x_2151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2151 = x_2123;
}
lean_ctor_set(x_2151, 0, x_2150);
if (lean_is_scalar(x_2141)) {
 x_2152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2152 = x_2141;
}
lean_ctor_set(x_2152, 0, x_2151);
lean_ctor_set(x_2152, 1, x_2143);
return x_2152;
}
else
{
size_t x_2153; size_t x_2154; lean_object* x_2155; 
lean_dec(x_2141);
x_2153 = 0;
x_2154 = lean_usize_of_nat(x_2144);
lean_dec(x_2144);
lean_inc(x_2139);
x_2155 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_2139, x_1, x_2153, x_2154, x_8, x_9, x_10, x_11, x_2143);
if (lean_obj_tag(x_2155) == 0)
{
lean_object* x_2156; uint8_t x_2157; 
x_2156 = lean_ctor_get(x_2155, 0);
lean_inc(x_2156);
x_2157 = lean_unbox(x_2156);
lean_dec(x_2156);
if (x_2157 == 0)
{
uint8_t x_2158; 
lean_dec(x_3);
x_2158 = !lean_is_exclusive(x_2155);
if (x_2158 == 0)
{
lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; 
x_2159 = lean_ctor_get(x_2155, 0);
lean_dec(x_2159);
if (lean_is_scalar(x_2136)) {
 x_2160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2160 = x_2136;
}
lean_ctor_set(x_2160, 0, x_2139);
lean_ctor_set(x_2160, 1, x_2122);
if (lean_is_scalar(x_2123)) {
 x_2161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2161 = x_2123;
}
lean_ctor_set(x_2161, 0, x_2160);
lean_ctor_set(x_2155, 0, x_2161);
return x_2155;
}
else
{
lean_object* x_2162; lean_object* x_2163; lean_object* x_2164; lean_object* x_2165; 
x_2162 = lean_ctor_get(x_2155, 1);
lean_inc(x_2162);
lean_dec(x_2155);
if (lean_is_scalar(x_2136)) {
 x_2163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2163 = x_2136;
}
lean_ctor_set(x_2163, 0, x_2139);
lean_ctor_set(x_2163, 1, x_2122);
if (lean_is_scalar(x_2123)) {
 x_2164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2164 = x_2123;
}
lean_ctor_set(x_2164, 0, x_2163);
x_2165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2165, 0, x_2164);
lean_ctor_set(x_2165, 1, x_2162);
return x_2165;
}
}
else
{
uint8_t x_2166; 
lean_dec(x_2139);
lean_dec(x_2136);
lean_dec(x_2123);
lean_dec(x_2122);
x_2166 = !lean_is_exclusive(x_2155);
if (x_2166 == 0)
{
lean_object* x_2167; 
x_2167 = lean_ctor_get(x_2155, 0);
lean_dec(x_2167);
lean_ctor_set(x_2155, 0, x_3);
return x_2155;
}
else
{
lean_object* x_2168; lean_object* x_2169; 
x_2168 = lean_ctor_get(x_2155, 1);
lean_inc(x_2168);
lean_dec(x_2155);
x_2169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2169, 0, x_3);
lean_ctor_set(x_2169, 1, x_2168);
return x_2169;
}
}
}
else
{
uint8_t x_2170; 
lean_dec(x_2139);
lean_dec(x_2136);
lean_dec(x_2123);
lean_dec(x_2122);
x_2170 = !lean_is_exclusive(x_2155);
if (x_2170 == 0)
{
lean_object* x_2171; 
x_2171 = lean_ctor_get(x_2155, 0);
lean_dec(x_2171);
lean_ctor_set_tag(x_2155, 0);
lean_ctor_set(x_2155, 0, x_3);
return x_2155;
}
else
{
lean_object* x_2172; lean_object* x_2173; 
x_2172 = lean_ctor_get(x_2155, 1);
lean_inc(x_2172);
lean_dec(x_2155);
x_2173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2173, 0, x_3);
lean_ctor_set(x_2173, 1, x_2172);
return x_2173;
}
}
}
}
}
}
else
{
uint8_t x_2345; 
lean_dec(x_2123);
lean_dec(x_2122);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_2345 = !lean_is_exclusive(x_2132);
if (x_2345 == 0)
{
return x_2132;
}
else
{
lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; 
x_2346 = lean_ctor_get(x_2132, 0);
x_2347 = lean_ctor_get(x_2132, 1);
lean_inc(x_2347);
lean_inc(x_2346);
lean_dec(x_2132);
x_2348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2348, 0, x_2346);
lean_ctor_set(x_2348, 1, x_2347);
return x_2348;
}
}
}
}
}
}
default: 
{
lean_object* x_2349; 
lean_dec(x_7);
lean_dec(x_6);
x_2349 = l_Lean_Expr_constName_x3f(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_2349) == 0)
{
lean_object* x_2350; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_2350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2350, 0, x_3);
lean_ctor_set(x_2350, 1, x_12);
return x_2350;
}
else
{
lean_object* x_2351; lean_object* x_2352; lean_object* x_2353; 
x_2351 = lean_ctor_get(x_2349, 0);
lean_inc(x_2351);
lean_dec(x_2349);
x_2352 = lean_unsigned_to_nat(0u);
x_2353 = l_Array_indexOfAux___at_Lean_Meta_getElimInfo___spec__1(x_1, x_4, x_2352);
if (lean_obj_tag(x_2353) == 0)
{
lean_object* x_2354; 
lean_dec(x_2351);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_2354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2354, 0, x_3);
lean_ctor_set(x_2354, 1, x_12);
return x_2354;
}
else
{
lean_object* x_2355; lean_object* x_2356; lean_object* x_2357; lean_object* x_2358; uint8_t x_2359; 
x_2355 = lean_ctor_get(x_2353, 0);
lean_inc(x_2355);
if (lean_is_exclusive(x_2353)) {
 lean_ctor_release(x_2353, 0);
 x_2356 = x_2353;
} else {
 lean_dec_ref(x_2353);
 x_2356 = lean_box(0);
}
x_2357 = l_Lean_isInductivePredicate___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__1(x_2351, x_8, x_9, x_10, x_11, x_12);
x_2358 = lean_ctor_get(x_2357, 0);
lean_inc(x_2358);
x_2359 = lean_unbox(x_2358);
lean_dec(x_2358);
if (x_2359 == 0)
{
uint8_t x_2360; 
lean_dec(x_2356);
lean_dec(x_2355);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_2360 = !lean_is_exclusive(x_2357);
if (x_2360 == 0)
{
lean_object* x_2361; 
x_2361 = lean_ctor_get(x_2357, 0);
lean_dec(x_2361);
lean_ctor_set(x_2357, 0, x_3);
return x_2357;
}
else
{
lean_object* x_2362; lean_object* x_2363; 
x_2362 = lean_ctor_get(x_2357, 1);
lean_inc(x_2362);
lean_dec(x_2357);
x_2363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2363, 0, x_3);
lean_ctor_set(x_2363, 1, x_2362);
return x_2363;
}
}
else
{
lean_object* x_2364; lean_object* x_2365; 
x_2364 = lean_ctor_get(x_2357, 1);
lean_inc(x_2364);
lean_dec(x_2357);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2365 = l___private_Lean_Meta_IndPredBelow_0__Lean_Meta_IndPredBelow_belowType(x_2, x_1, x_2355, x_8, x_9, x_10, x_11, x_2364);
if (lean_obj_tag(x_2365) == 0)
{
lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; lean_object* x_2370; lean_object* x_2371; lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; lean_object* x_2376; lean_object* x_2408; 
x_2366 = lean_ctor_get(x_2365, 0);
lean_inc(x_2366);
x_2367 = lean_ctor_get(x_2365, 1);
lean_inc(x_2367);
lean_dec(x_2365);
x_2368 = lean_ctor_get(x_2366, 1);
lean_inc(x_2368);
if (lean_is_exclusive(x_2366)) {
 lean_ctor_release(x_2366, 0);
 lean_ctor_release(x_2366, 1);
 x_2369 = x_2366;
} else {
 lean_dec_ref(x_2366);
 x_2369 = lean_box(0);
}
x_2370 = lean_box(0);
lean_inc(x_8);
x_2371 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2368, x_2370, x_8, x_9, x_10, x_11, x_2367);
x_2372 = lean_ctor_get(x_2371, 0);
lean_inc(x_2372);
x_2373 = lean_ctor_get(x_2371, 1);
lean_inc(x_2373);
if (lean_is_exclusive(x_2371)) {
 lean_ctor_release(x_2371, 0);
 lean_ctor_release(x_2371, 1);
 x_2374 = x_2371;
} else {
 lean_dec_ref(x_2371);
 x_2374 = lean_box(0);
}
x_2375 = l_Lean_Expr_mvarId_x21(x_2372);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2408 = l_Lean_Meta_ppGoal(x_2375, x_8, x_9, x_10, x_11, x_2373);
if (lean_obj_tag(x_2408) == 0)
{
lean_object* x_2409; lean_object* x_2410; uint8_t x_2411; lean_object* x_2412; lean_object* x_2422; lean_object* x_2423; lean_object* x_2424; uint8_t x_2425; 
x_2409 = lean_ctor_get(x_2408, 0);
lean_inc(x_2409);
x_2410 = lean_ctor_get(x_2408, 1);
lean_inc(x_2410);
lean_dec(x_2408);
x_2422 = lean_st_ref_get(x_11, x_2410);
x_2423 = lean_ctor_get(x_2422, 0);
lean_inc(x_2423);
x_2424 = lean_ctor_get(x_2423, 3);
lean_inc(x_2424);
lean_dec(x_2423);
x_2425 = lean_ctor_get_uint8(x_2424, sizeof(void*)*1);
lean_dec(x_2424);
if (x_2425 == 0)
{
lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; 
lean_dec(x_2409);
x_2426 = lean_ctor_get(x_2422, 1);
lean_inc(x_2426);
lean_dec(x_2422);
x_2427 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2428 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_2375, x_2427, x_8, x_9, x_10, x_11, x_2426);
if (lean_obj_tag(x_2428) == 0)
{
lean_object* x_2429; uint8_t x_2430; 
x_2429 = lean_ctor_get(x_2428, 0);
lean_inc(x_2429);
x_2430 = lean_unbox(x_2429);
lean_dec(x_2429);
if (x_2430 == 0)
{
lean_object* x_2431; lean_object* x_2432; lean_object* x_2433; lean_object* x_2434; uint8_t x_2435; 
lean_dec(x_2374);
lean_dec(x_2372);
lean_dec(x_2369);
lean_dec(x_2356);
lean_dec(x_2355);
x_2431 = lean_ctor_get(x_2428, 1);
lean_inc(x_2431);
lean_dec(x_2428);
x_2432 = lean_st_ref_get(x_11, x_2431);
x_2433 = lean_ctor_get(x_2432, 0);
lean_inc(x_2433);
x_2434 = lean_ctor_get(x_2433, 3);
lean_inc(x_2434);
lean_dec(x_2433);
x_2435 = lean_ctor_get_uint8(x_2434, sizeof(void*)*1);
lean_dec(x_2434);
if (x_2435 == 0)
{
uint8_t x_2436; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2436 = !lean_is_exclusive(x_2432);
if (x_2436 == 0)
{
lean_object* x_2437; 
x_2437 = lean_ctor_get(x_2432, 0);
lean_dec(x_2437);
lean_ctor_set(x_2432, 0, x_3);
return x_2432;
}
else
{
lean_object* x_2438; lean_object* x_2439; 
x_2438 = lean_ctor_get(x_2432, 1);
lean_inc(x_2438);
lean_dec(x_2432);
x_2439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2439, 0, x_3);
lean_ctor_set(x_2439, 1, x_2438);
return x_2439;
}
}
else
{
lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; uint8_t x_2444; 
x_2440 = lean_ctor_get(x_2432, 1);
lean_inc(x_2440);
lean_dec(x_2432);
x_2441 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2442 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2441, x_8, x_9, x_10, x_11, x_2440);
x_2443 = lean_ctor_get(x_2442, 0);
lean_inc(x_2443);
x_2444 = lean_unbox(x_2443);
lean_dec(x_2443);
if (x_2444 == 0)
{
uint8_t x_2445; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2445 = !lean_is_exclusive(x_2442);
if (x_2445 == 0)
{
lean_object* x_2446; 
x_2446 = lean_ctor_get(x_2442, 0);
lean_dec(x_2446);
lean_ctor_set(x_2442, 0, x_3);
return x_2442;
}
else
{
lean_object* x_2447; lean_object* x_2448; 
x_2447 = lean_ctor_get(x_2442, 1);
lean_inc(x_2447);
lean_dec(x_2442);
x_2448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2448, 0, x_3);
lean_ctor_set(x_2448, 1, x_2447);
return x_2448;
}
}
else
{
lean_object* x_2449; lean_object* x_2450; lean_object* x_2451; uint8_t x_2452; 
x_2449 = lean_ctor_get(x_2442, 1);
lean_inc(x_2449);
lean_dec(x_2442);
x_2450 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_2451 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2441, x_2450, x_8, x_9, x_10, x_11, x_2449);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2452 = !lean_is_exclusive(x_2451);
if (x_2452 == 0)
{
lean_object* x_2453; 
x_2453 = lean_ctor_get(x_2451, 0);
lean_dec(x_2453);
lean_ctor_set(x_2451, 0, x_3);
return x_2451;
}
else
{
lean_object* x_2454; lean_object* x_2455; 
x_2454 = lean_ctor_get(x_2451, 1);
lean_inc(x_2454);
lean_dec(x_2451);
x_2455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2455, 0, x_3);
lean_ctor_set(x_2455, 1, x_2454);
return x_2455;
}
}
}
}
else
{
lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; uint8_t x_2460; 
x_2456 = lean_ctor_get(x_2428, 1);
lean_inc(x_2456);
lean_dec(x_2428);
x_2457 = lean_st_ref_get(x_11, x_2456);
x_2458 = lean_ctor_get(x_2457, 0);
lean_inc(x_2458);
x_2459 = lean_ctor_get(x_2458, 3);
lean_inc(x_2459);
lean_dec(x_2458);
x_2460 = lean_ctor_get_uint8(x_2459, sizeof(void*)*1);
lean_dec(x_2459);
if (x_2460 == 0)
{
lean_object* x_2461; uint8_t x_2462; 
x_2461 = lean_ctor_get(x_2457, 1);
lean_inc(x_2461);
lean_dec(x_2457);
x_2462 = 0;
x_2411 = x_2462;
x_2412 = x_2461;
goto block_2421;
}
else
{
lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; lean_object* x_2467; uint8_t x_2468; 
x_2463 = lean_ctor_get(x_2457, 1);
lean_inc(x_2463);
lean_dec(x_2457);
x_2464 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2465 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2464, x_8, x_9, x_10, x_11, x_2463);
x_2466 = lean_ctor_get(x_2465, 0);
lean_inc(x_2466);
x_2467 = lean_ctor_get(x_2465, 1);
lean_inc(x_2467);
lean_dec(x_2465);
x_2468 = lean_unbox(x_2466);
lean_dec(x_2466);
x_2411 = x_2468;
x_2412 = x_2467;
goto block_2421;
}
}
}
else
{
uint8_t x_2469; 
lean_dec(x_2374);
lean_dec(x_2372);
lean_dec(x_2369);
lean_dec(x_2356);
lean_dec(x_2355);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2469 = !lean_is_exclusive(x_2428);
if (x_2469 == 0)
{
lean_object* x_2470; 
x_2470 = lean_ctor_get(x_2428, 0);
lean_dec(x_2470);
lean_ctor_set_tag(x_2428, 0);
lean_ctor_set(x_2428, 0, x_3);
return x_2428;
}
else
{
lean_object* x_2471; lean_object* x_2472; 
x_2471 = lean_ctor_get(x_2428, 1);
lean_inc(x_2471);
lean_dec(x_2428);
x_2472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2472, 0, x_3);
lean_ctor_set(x_2472, 1, x_2471);
return x_2472;
}
}
}
else
{
lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; uint8_t x_2477; 
x_2473 = lean_ctor_get(x_2422, 1);
lean_inc(x_2473);
lean_dec(x_2422);
x_2474 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2475 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2474, x_8, x_9, x_10, x_11, x_2473);
x_2476 = lean_ctor_get(x_2475, 0);
lean_inc(x_2476);
x_2477 = lean_unbox(x_2476);
lean_dec(x_2476);
if (x_2477 == 0)
{
lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; 
lean_dec(x_2409);
x_2478 = lean_ctor_get(x_2475, 1);
lean_inc(x_2478);
lean_dec(x_2475);
x_2479 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2480 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_2375, x_2479, x_8, x_9, x_10, x_11, x_2478);
if (lean_obj_tag(x_2480) == 0)
{
lean_object* x_2481; uint8_t x_2482; 
x_2481 = lean_ctor_get(x_2480, 0);
lean_inc(x_2481);
x_2482 = lean_unbox(x_2481);
lean_dec(x_2481);
if (x_2482 == 0)
{
lean_object* x_2483; lean_object* x_2484; lean_object* x_2485; lean_object* x_2486; uint8_t x_2487; 
lean_dec(x_2374);
lean_dec(x_2372);
lean_dec(x_2369);
lean_dec(x_2356);
lean_dec(x_2355);
x_2483 = lean_ctor_get(x_2480, 1);
lean_inc(x_2483);
lean_dec(x_2480);
x_2484 = lean_st_ref_get(x_11, x_2483);
x_2485 = lean_ctor_get(x_2484, 0);
lean_inc(x_2485);
x_2486 = lean_ctor_get(x_2485, 3);
lean_inc(x_2486);
lean_dec(x_2485);
x_2487 = lean_ctor_get_uint8(x_2486, sizeof(void*)*1);
lean_dec(x_2486);
if (x_2487 == 0)
{
uint8_t x_2488; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2488 = !lean_is_exclusive(x_2484);
if (x_2488 == 0)
{
lean_object* x_2489; 
x_2489 = lean_ctor_get(x_2484, 0);
lean_dec(x_2489);
lean_ctor_set(x_2484, 0, x_3);
return x_2484;
}
else
{
lean_object* x_2490; lean_object* x_2491; 
x_2490 = lean_ctor_get(x_2484, 1);
lean_inc(x_2490);
lean_dec(x_2484);
x_2491 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2491, 0, x_3);
lean_ctor_set(x_2491, 1, x_2490);
return x_2491;
}
}
else
{
lean_object* x_2492; lean_object* x_2493; lean_object* x_2494; uint8_t x_2495; 
x_2492 = lean_ctor_get(x_2484, 1);
lean_inc(x_2492);
lean_dec(x_2484);
x_2493 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2474, x_8, x_9, x_10, x_11, x_2492);
x_2494 = lean_ctor_get(x_2493, 0);
lean_inc(x_2494);
x_2495 = lean_unbox(x_2494);
lean_dec(x_2494);
if (x_2495 == 0)
{
uint8_t x_2496; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2496 = !lean_is_exclusive(x_2493);
if (x_2496 == 0)
{
lean_object* x_2497; 
x_2497 = lean_ctor_get(x_2493, 0);
lean_dec(x_2497);
lean_ctor_set(x_2493, 0, x_3);
return x_2493;
}
else
{
lean_object* x_2498; lean_object* x_2499; 
x_2498 = lean_ctor_get(x_2493, 1);
lean_inc(x_2498);
lean_dec(x_2493);
x_2499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2499, 0, x_3);
lean_ctor_set(x_2499, 1, x_2498);
return x_2499;
}
}
else
{
lean_object* x_2500; lean_object* x_2501; lean_object* x_2502; uint8_t x_2503; 
x_2500 = lean_ctor_get(x_2493, 1);
lean_inc(x_2500);
lean_dec(x_2493);
x_2501 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_2502 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2474, x_2501, x_8, x_9, x_10, x_11, x_2500);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2503 = !lean_is_exclusive(x_2502);
if (x_2503 == 0)
{
lean_object* x_2504; 
x_2504 = lean_ctor_get(x_2502, 0);
lean_dec(x_2504);
lean_ctor_set(x_2502, 0, x_3);
return x_2502;
}
else
{
lean_object* x_2505; lean_object* x_2506; 
x_2505 = lean_ctor_get(x_2502, 1);
lean_inc(x_2505);
lean_dec(x_2502);
x_2506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2506, 0, x_3);
lean_ctor_set(x_2506, 1, x_2505);
return x_2506;
}
}
}
}
else
{
lean_object* x_2507; lean_object* x_2508; lean_object* x_2509; lean_object* x_2510; uint8_t x_2511; 
x_2507 = lean_ctor_get(x_2480, 1);
lean_inc(x_2507);
lean_dec(x_2480);
x_2508 = lean_st_ref_get(x_11, x_2507);
x_2509 = lean_ctor_get(x_2508, 0);
lean_inc(x_2509);
x_2510 = lean_ctor_get(x_2509, 3);
lean_inc(x_2510);
lean_dec(x_2509);
x_2511 = lean_ctor_get_uint8(x_2510, sizeof(void*)*1);
lean_dec(x_2510);
if (x_2511 == 0)
{
lean_object* x_2512; uint8_t x_2513; 
x_2512 = lean_ctor_get(x_2508, 1);
lean_inc(x_2512);
lean_dec(x_2508);
x_2513 = 0;
x_2411 = x_2513;
x_2412 = x_2512;
goto block_2421;
}
else
{
lean_object* x_2514; lean_object* x_2515; lean_object* x_2516; lean_object* x_2517; uint8_t x_2518; 
x_2514 = lean_ctor_get(x_2508, 1);
lean_inc(x_2514);
lean_dec(x_2508);
x_2515 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2474, x_8, x_9, x_10, x_11, x_2514);
x_2516 = lean_ctor_get(x_2515, 0);
lean_inc(x_2516);
x_2517 = lean_ctor_get(x_2515, 1);
lean_inc(x_2517);
lean_dec(x_2515);
x_2518 = lean_unbox(x_2516);
lean_dec(x_2516);
x_2411 = x_2518;
x_2412 = x_2517;
goto block_2421;
}
}
}
else
{
uint8_t x_2519; 
lean_dec(x_2374);
lean_dec(x_2372);
lean_dec(x_2369);
lean_dec(x_2356);
lean_dec(x_2355);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2519 = !lean_is_exclusive(x_2480);
if (x_2519 == 0)
{
lean_object* x_2520; 
x_2520 = lean_ctor_get(x_2480, 0);
lean_dec(x_2520);
lean_ctor_set_tag(x_2480, 0);
lean_ctor_set(x_2480, 0, x_3);
return x_2480;
}
else
{
lean_object* x_2521; lean_object* x_2522; 
x_2521 = lean_ctor_get(x_2480, 1);
lean_inc(x_2521);
lean_dec(x_2480);
x_2522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2522, 0, x_3);
lean_ctor_set(x_2522, 1, x_2521);
return x_2522;
}
}
}
else
{
lean_object* x_2523; lean_object* x_2524; lean_object* x_2525; lean_object* x_2526; lean_object* x_2527; lean_object* x_2528; lean_object* x_2529; lean_object* x_2530; lean_object* x_2531; 
x_2523 = lean_ctor_get(x_2475, 1);
lean_inc(x_2523);
lean_dec(x_2475);
x_2524 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2524, 0, x_2409);
x_2525 = l_Lean_KernelException_toMessageData___closed__15;
x_2526 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2526, 0, x_2525);
lean_ctor_set(x_2526, 1, x_2524);
x_2527 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2527, 0, x_2526);
lean_ctor_set(x_2527, 1, x_2525);
x_2528 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2474, x_2527, x_8, x_9, x_10, x_11, x_2523);
x_2529 = lean_ctor_get(x_2528, 1);
lean_inc(x_2529);
lean_dec(x_2528);
x_2530 = lean_unsigned_to_nat(10u);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_2531 = l_Lean_Meta_IndPredBelow_backwardsChaining(x_2375, x_2530, x_8, x_9, x_10, x_11, x_2529);
if (lean_obj_tag(x_2531) == 0)
{
lean_object* x_2532; uint8_t x_2533; 
x_2532 = lean_ctor_get(x_2531, 0);
lean_inc(x_2532);
x_2533 = lean_unbox(x_2532);
lean_dec(x_2532);
if (x_2533 == 0)
{
lean_object* x_2534; lean_object* x_2535; lean_object* x_2536; lean_object* x_2537; uint8_t x_2538; 
lean_dec(x_2374);
lean_dec(x_2372);
lean_dec(x_2369);
lean_dec(x_2356);
lean_dec(x_2355);
x_2534 = lean_ctor_get(x_2531, 1);
lean_inc(x_2534);
lean_dec(x_2531);
x_2535 = lean_st_ref_get(x_11, x_2534);
x_2536 = lean_ctor_get(x_2535, 0);
lean_inc(x_2536);
x_2537 = lean_ctor_get(x_2536, 3);
lean_inc(x_2537);
lean_dec(x_2536);
x_2538 = lean_ctor_get_uint8(x_2537, sizeof(void*)*1);
lean_dec(x_2537);
if (x_2538 == 0)
{
uint8_t x_2539; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2539 = !lean_is_exclusive(x_2535);
if (x_2539 == 0)
{
lean_object* x_2540; 
x_2540 = lean_ctor_get(x_2535, 0);
lean_dec(x_2540);
lean_ctor_set(x_2535, 0, x_3);
return x_2535;
}
else
{
lean_object* x_2541; lean_object* x_2542; 
x_2541 = lean_ctor_get(x_2535, 1);
lean_inc(x_2541);
lean_dec(x_2535);
x_2542 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2542, 0, x_3);
lean_ctor_set(x_2542, 1, x_2541);
return x_2542;
}
}
else
{
lean_object* x_2543; lean_object* x_2544; lean_object* x_2545; uint8_t x_2546; 
x_2543 = lean_ctor_get(x_2535, 1);
lean_inc(x_2543);
lean_dec(x_2535);
x_2544 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2474, x_8, x_9, x_10, x_11, x_2543);
x_2545 = lean_ctor_get(x_2544, 0);
lean_inc(x_2545);
x_2546 = lean_unbox(x_2545);
lean_dec(x_2545);
if (x_2546 == 0)
{
uint8_t x_2547; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2547 = !lean_is_exclusive(x_2544);
if (x_2547 == 0)
{
lean_object* x_2548; 
x_2548 = lean_ctor_get(x_2544, 0);
lean_dec(x_2548);
lean_ctor_set(x_2544, 0, x_3);
return x_2544;
}
else
{
lean_object* x_2549; lean_object* x_2550; 
x_2549 = lean_ctor_get(x_2544, 1);
lean_inc(x_2549);
lean_dec(x_2544);
x_2550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2550, 0, x_3);
lean_ctor_set(x_2550, 1, x_2549);
return x_2550;
}
}
else
{
lean_object* x_2551; lean_object* x_2552; lean_object* x_2553; uint8_t x_2554; 
x_2551 = lean_ctor_get(x_2544, 1);
lean_inc(x_2551);
lean_dec(x_2544);
x_2552 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4;
x_2553 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2474, x_2552, x_8, x_9, x_10, x_11, x_2551);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2554 = !lean_is_exclusive(x_2553);
if (x_2554 == 0)
{
lean_object* x_2555; 
x_2555 = lean_ctor_get(x_2553, 0);
lean_dec(x_2555);
lean_ctor_set(x_2553, 0, x_3);
return x_2553;
}
else
{
lean_object* x_2556; lean_object* x_2557; 
x_2556 = lean_ctor_get(x_2553, 1);
lean_inc(x_2556);
lean_dec(x_2553);
x_2557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2557, 0, x_3);
lean_ctor_set(x_2557, 1, x_2556);
return x_2557;
}
}
}
}
else
{
lean_object* x_2558; lean_object* x_2559; lean_object* x_2560; lean_object* x_2561; uint8_t x_2562; 
x_2558 = lean_ctor_get(x_2531, 1);
lean_inc(x_2558);
lean_dec(x_2531);
x_2559 = lean_st_ref_get(x_11, x_2558);
x_2560 = lean_ctor_get(x_2559, 0);
lean_inc(x_2560);
x_2561 = lean_ctor_get(x_2560, 3);
lean_inc(x_2561);
lean_dec(x_2560);
x_2562 = lean_ctor_get_uint8(x_2561, sizeof(void*)*1);
lean_dec(x_2561);
if (x_2562 == 0)
{
lean_object* x_2563; uint8_t x_2564; 
x_2563 = lean_ctor_get(x_2559, 1);
lean_inc(x_2563);
lean_dec(x_2559);
x_2564 = 0;
x_2411 = x_2564;
x_2412 = x_2563;
goto block_2421;
}
else
{
lean_object* x_2565; lean_object* x_2566; lean_object* x_2567; lean_object* x_2568; uint8_t x_2569; 
x_2565 = lean_ctor_get(x_2559, 1);
lean_inc(x_2565);
lean_dec(x_2559);
x_2566 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_2474, x_8, x_9, x_10, x_11, x_2565);
x_2567 = lean_ctor_get(x_2566, 0);
lean_inc(x_2567);
x_2568 = lean_ctor_get(x_2566, 1);
lean_inc(x_2568);
lean_dec(x_2566);
x_2569 = lean_unbox(x_2567);
lean_dec(x_2567);
x_2411 = x_2569;
x_2412 = x_2568;
goto block_2421;
}
}
}
else
{
uint8_t x_2570; 
lean_dec(x_2374);
lean_dec(x_2372);
lean_dec(x_2369);
lean_dec(x_2356);
lean_dec(x_2355);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2570 = !lean_is_exclusive(x_2531);
if (x_2570 == 0)
{
lean_object* x_2571; 
x_2571 = lean_ctor_get(x_2531, 0);
lean_dec(x_2571);
lean_ctor_set_tag(x_2531, 0);
lean_ctor_set(x_2531, 0, x_3);
return x_2531;
}
else
{
lean_object* x_2572; lean_object* x_2573; 
x_2572 = lean_ctor_get(x_2531, 1);
lean_inc(x_2572);
lean_dec(x_2531);
x_2573 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2573, 0, x_3);
lean_ctor_set(x_2573, 1, x_2572);
return x_2573;
}
}
}
}
block_2421:
{
if (x_2411 == 0)
{
x_2376 = x_2412;
goto block_2407;
}
else
{
lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; lean_object* x_2416; lean_object* x_2417; lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; 
lean_inc(x_2372);
x_2413 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2413, 0, x_2372);
x_2414 = l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2;
x_2415 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2415, 0, x_2414);
lean_ctor_set(x_2415, 1, x_2413);
x_2416 = l_Lean_KernelException_toMessageData___closed__15;
x_2417 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_2417, 0, x_2415);
lean_ctor_set(x_2417, 1, x_2416);
x_2418 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
x_2419 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_2418, x_2417, x_8, x_9, x_10, x_11, x_2412);
x_2420 = lean_ctor_get(x_2419, 1);
lean_inc(x_2420);
lean_dec(x_2419);
x_2376 = x_2420;
goto block_2407;
}
}
}
else
{
uint8_t x_2574; 
lean_dec(x_2375);
lean_dec(x_2374);
lean_dec(x_2372);
lean_dec(x_2369);
lean_dec(x_2356);
lean_dec(x_2355);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_2574 = !lean_is_exclusive(x_2408);
if (x_2574 == 0)
{
lean_object* x_2575; 
x_2575 = lean_ctor_get(x_2408, 0);
lean_dec(x_2575);
lean_ctor_set_tag(x_2408, 0);
lean_ctor_set(x_2408, 0, x_3);
return x_2408;
}
else
{
lean_object* x_2576; lean_object* x_2577; 
x_2576 = lean_ctor_get(x_2408, 1);
lean_inc(x_2576);
lean_dec(x_2408);
x_2577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2577, 0, x_3);
lean_ctor_set(x_2577, 1, x_2576);
return x_2577;
}
}
block_2407:
{
lean_object* x_2377; uint8_t x_2378; 
x_2377 = lean_array_get_size(x_1);
x_2378 = lean_nat_dec_lt(x_2352, x_2377);
if (x_2378 == 0)
{
lean_object* x_2379; lean_object* x_2380; lean_object* x_2381; 
lean_dec(x_2377);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_2369)) {
 x_2379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2379 = x_2369;
}
lean_ctor_set(x_2379, 0, x_2372);
lean_ctor_set(x_2379, 1, x_2355);
if (lean_is_scalar(x_2356)) {
 x_2380 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2380 = x_2356;
}
lean_ctor_set(x_2380, 0, x_2379);
if (lean_is_scalar(x_2374)) {
 x_2381 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2381 = x_2374;
}
lean_ctor_set(x_2381, 0, x_2380);
lean_ctor_set(x_2381, 1, x_2376);
return x_2381;
}
else
{
uint8_t x_2382; 
x_2382 = lean_nat_dec_le(x_2377, x_2377);
if (x_2382 == 0)
{
lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; 
lean_dec(x_2377);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
if (lean_is_scalar(x_2369)) {
 x_2383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2383 = x_2369;
}
lean_ctor_set(x_2383, 0, x_2372);
lean_ctor_set(x_2383, 1, x_2355);
if (lean_is_scalar(x_2356)) {
 x_2384 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2384 = x_2356;
}
lean_ctor_set(x_2384, 0, x_2383);
if (lean_is_scalar(x_2374)) {
 x_2385 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2385 = x_2374;
}
lean_ctor_set(x_2385, 0, x_2384);
lean_ctor_set(x_2385, 1, x_2376);
return x_2385;
}
else
{
size_t x_2386; size_t x_2387; lean_object* x_2388; 
lean_dec(x_2374);
x_2386 = 0;
x_2387 = lean_usize_of_nat(x_2377);
lean_dec(x_2377);
lean_inc(x_2372);
x_2388 = l_Array_anyMUnsafe_any___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__2(x_2372, x_1, x_2386, x_2387, x_8, x_9, x_10, x_11, x_2376);
if (lean_obj_tag(x_2388) == 0)
{
lean_object* x_2389; uint8_t x_2390; 
x_2389 = lean_ctor_get(x_2388, 0);
lean_inc(x_2389);
x_2390 = lean_unbox(x_2389);
lean_dec(x_2389);
if (x_2390 == 0)
{
uint8_t x_2391; 
lean_dec(x_3);
x_2391 = !lean_is_exclusive(x_2388);
if (x_2391 == 0)
{
lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; 
x_2392 = lean_ctor_get(x_2388, 0);
lean_dec(x_2392);
if (lean_is_scalar(x_2369)) {
 x_2393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2393 = x_2369;
}
lean_ctor_set(x_2393, 0, x_2372);
lean_ctor_set(x_2393, 1, x_2355);
if (lean_is_scalar(x_2356)) {
 x_2394 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2394 = x_2356;
}
lean_ctor_set(x_2394, 0, x_2393);
lean_ctor_set(x_2388, 0, x_2394);
return x_2388;
}
else
{
lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; 
x_2395 = lean_ctor_get(x_2388, 1);
lean_inc(x_2395);
lean_dec(x_2388);
if (lean_is_scalar(x_2369)) {
 x_2396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2396 = x_2369;
}
lean_ctor_set(x_2396, 0, x_2372);
lean_ctor_set(x_2396, 1, x_2355);
if (lean_is_scalar(x_2356)) {
 x_2397 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2397 = x_2356;
}
lean_ctor_set(x_2397, 0, x_2396);
x_2398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2398, 0, x_2397);
lean_ctor_set(x_2398, 1, x_2395);
return x_2398;
}
}
else
{
uint8_t x_2399; 
lean_dec(x_2372);
lean_dec(x_2369);
lean_dec(x_2356);
lean_dec(x_2355);
x_2399 = !lean_is_exclusive(x_2388);
if (x_2399 == 0)
{
lean_object* x_2400; 
x_2400 = lean_ctor_get(x_2388, 0);
lean_dec(x_2400);
lean_ctor_set(x_2388, 0, x_3);
return x_2388;
}
else
{
lean_object* x_2401; lean_object* x_2402; 
x_2401 = lean_ctor_get(x_2388, 1);
lean_inc(x_2401);
lean_dec(x_2388);
x_2402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2402, 0, x_3);
lean_ctor_set(x_2402, 1, x_2401);
return x_2402;
}
}
}
else
{
uint8_t x_2403; 
lean_dec(x_2372);
lean_dec(x_2369);
lean_dec(x_2356);
lean_dec(x_2355);
x_2403 = !lean_is_exclusive(x_2388);
if (x_2403 == 0)
{
lean_object* x_2404; 
x_2404 = lean_ctor_get(x_2388, 0);
lean_dec(x_2404);
lean_ctor_set_tag(x_2388, 0);
lean_ctor_set(x_2388, 0, x_3);
return x_2388;
}
else
{
lean_object* x_2405; lean_object* x_2406; 
x_2405 = lean_ctor_get(x_2388, 1);
lean_inc(x_2405);
lean_dec(x_2388);
x_2406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2406, 0, x_3);
lean_ctor_set(x_2406, 1, x_2405);
return x_2406;
}
}
}
}
}
}
else
{
uint8_t x_2578; 
lean_dec(x_2356);
lean_dec(x_2355);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_2578 = !lean_is_exclusive(x_2365);
if (x_2578 == 0)
{
return x_2365;
}
else
{
lean_object* x_2579; lean_object* x_2580; lean_object* x_2581; 
x_2579 = lean_ctor_get(x_2365, 0);
x_2580 = lean_ctor_get(x_2365, 1);
lean_inc(x_2580);
lean_inc(x_2579);
lean_dec(x_2365);
x_2581 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2581, 0, x_2579);
lean_ctor_set(x_2581, 1, x_2580);
return x_2581;
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
x_22 = l_Lean_Expr_getAppArgs___closed__1;
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
x_12 = l_Array_findSomeM_x3f___rarg___closed__1;
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
#define _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("failed to prove brecOn for ");\
__INIT_VAR__ = x_1; goto l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1_end;\
}\
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1_end: ((void) 0);}
#define _init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2_end;\
}\
l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2_end: ((void) 0);}
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
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
x_30 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2;
x_31 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = l_Array_foldlMUnsafe_fold___at___private_Lean_Util_Trace_0__Lean_withNestedTracesFinalizer___spec__5___closed__1;
x_33 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Exception_toMessageData(x_19);
x_35 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_KernelException_toMessageData___closed__15;
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
lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_12 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(x_11, x_5, x_6, x_7, x_8, x_9);
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
#define _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("Not inductive predicate");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkBelow___closed__1_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelow___closed__1_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_mkBelow___closed__1;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_mkBelow___closed__2_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelow___closed__2_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("Not recursive");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkBelow___closed__3_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelow___closed__3_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_mkBelow___closed__3;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_mkBelow___closed__4_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelow___closed__4_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("added ");\
__INIT_VAR__ = x_1; goto l_Lean_Meta_IndPredBelow_mkBelow___closed__5_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelow___closed__5_end: ((void) 0);}
#define _init_l_Lean_Meta_IndPredBelow_mkBelow___closed__6(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = l_Lean_Meta_IndPredBelow_mkBelow___closed__5;\
x_2 = l_Lean_stringToMessageData(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Meta_IndPredBelow_mkBelow___closed__6_end;\
}\
l_Lean_Meta_IndPredBelow_mkBelow___closed__6_end: ((void) 0);}
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
x_22 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
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
x_51 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
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
lean_object* x_72; lean_object* x_73; uint8_t x_103; lean_object* x_104; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_117 = lean_st_ref_get(x_5, x_72);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_118, 3);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_ctor_get_uint8(x_119, sizeof(void*)*1);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_117, 1);
lean_inc(x_121);
lean_dec(x_117);
x_122 = 0;
x_103 = x_122;
x_104 = x_121;
goto block_116;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_117, 1);
lean_inc(x_123);
lean_dec(x_117);
x_124 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
x_125 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_mkCongrLemma___spec__8(x_124, x_2, x_3, x_4, x_5, x_123);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_unbox(x_126);
lean_dec(x_126);
x_103 = x_128;
x_104 = x_127;
goto block_116;
}
block_102:
{
lean_object* x_74; lean_object* x_75; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_74 = lean_ctor_get(x_66, 2);
lean_inc(x_74);
x_89 = lean_array_get_size(x_74);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_nat_dec_lt(x_90, x_89);
if (x_91 == 0)
{
lean_dec(x_89);
x_75 = x_73;
goto block_88;
}
else
{
uint8_t x_92; 
x_92 = lean_nat_dec_le(x_89, x_89);
if (x_92 == 0)
{
lean_dec(x_89);
x_75 = x_73;
goto block_88;
}
else
{
size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; 
x_93 = 0;
x_94 = lean_usize_of_nat(x_89);
lean_dec(x_89);
x_95 = lean_box(0);
lean_inc(x_4);
x_96 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_IndPredBelow_mkBelow___spec__3(x_74, x_93, x_94, x_95, x_2, x_3, x_4, x_5, x_73);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_75 = x_97;
goto block_88;
}
else
{
uint8_t x_98; 
lean_dec(x_74);
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
return x_96;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_96, 0);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_96);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
block_88:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_76 = lean_ctor_get(x_66, 1);
lean_inc(x_76);
x_77 = lean_array_get_size(x_76);
lean_dec(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_unsigned_to_nat(1u);
lean_inc(x_77);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_77);
lean_ctor_set(x_80, 2, x_79);
x_81 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
x_82 = lean_box(0);
x_83 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(x_66, x_81, x_74, x_80, x_77, x_78, x_82, x_2, x_3, x_4, x_5, x_75);
lean_dec(x_80);
lean_dec(x_74);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
block_116:
{
if (x_103 == 0)
{
x_73 = x_104;
goto block_102;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_105 = lean_ctor_get(x_66, 2);
lean_inc(x_105);
x_106 = lean_array_to_list(lean_box(0), x_105);
x_107 = l_List_map___at_Lean_Meta_IndPredBelow_mkBelow___spec__4(x_106);
x_108 = l_Lean_MessageData_ofList(x_107);
lean_dec(x_107);
x_109 = l_Lean_Meta_IndPredBelow_mkBelow___closed__6;
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Lean_KernelException_toMessageData___closed__15;
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
x_114 = l_Lean_addTrace___at_Lean_Meta_mkCongrLemma___spec__7(x_113, x_112, x_2, x_3, x_4, x_5, x_104);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_73 = x_115;
goto block_102;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_71);
if (x_129 == 0)
{
return x_71;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_71, 0);
x_131 = lean_ctor_get(x_71, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_71);
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
lean_dec(x_66);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_133 = !lean_is_exclusive(x_68);
if (x_133 == 0)
{
return x_68;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_68, 0);
x_135 = lean_ctor_get(x_68, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_68);
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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_65);
if (x_137 == 0)
{
return x_65;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_65, 0);
x_139 = lean_ctor_get(x_65, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_65);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_36);
if (x_141 == 0)
{
return x_36;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_36, 0);
x_143 = lean_ctor_get(x_36, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_36);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
lean_object* l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_mkCasesOn___at_Lean_Meta_IndPredBelow_mkBelow___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
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
x_2 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2;
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
_init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__1);
_init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__2);
_init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__3);
_init_l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5____closed__4);
res = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_maxBackwardChainingDepth);
lean_dec_ref(res);
_init_l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1(l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_instInhabitedVariables___closed__1);
_init_l_Lean_Meta_IndPredBelow_instInhabitedVariables(l_Lean_Meta_IndPredBelow_instInhabitedVariables);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_instInhabitedVariables);
_init_l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1(l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkContext_motiveName___closed__1);
_init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1);
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__1);
_init_l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2);
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Meta_IndPredBelow_mkContext___spec__5___closed__2);
_init_l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1(l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkContext___boxed__const__1);
_init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1);
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__1);
_init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2);
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_mkBelowBinder___spec__3___closed__2);
_init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1);
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__11___boxed__const__1);
_init_l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1(l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1);
lean_mark_persistent(l_Lean_Meta_transform___at_Lean_Meta_IndPredBelow_mkCtorType_checkCount___spec__1___closed__1);
_init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__1);
_init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__2);
_init_l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_checkCount___closed__3);
_init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1);
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__1);
_init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2);
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__2);
_init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3);
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__3);
_init_l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4);
lean_mark_persistent(l_Lean_Meta_withLocalDecls_loop___at_Lean_Meta_IndPredBelow_mkCtorType_addMotives___spec__3___closed__4);
_init_l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1(l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkCtorType_addMotives___boxed__const__1);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__1);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_applyIH___closed__2);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__1);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__2);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__3);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__4);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__5);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__6);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__7);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__8);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__9);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__10);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__11);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn_closeGoal___rarg___closed__12);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1(l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn___closed__1);
_init_l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2(l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_proveBrecOn___closed__2);
_init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__1);
_init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__2);
_init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBrecOnDecl_mkIH___closed__3);
_init_l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1(l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBrecOnDecl___closed__1);
_init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1);
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___spec__1___closed__1);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__1(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__1);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__2(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___lambda__2___closed__2);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__1);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__2);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__3);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_convertToBelow___closed__4);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__1);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__1___closed__2);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__1);
_init_l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelowMatcher_newMotive___lambda__2___closed__2);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__1);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__2);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__3);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__4);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__5);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__6);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__7);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__8);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__9);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__10);
_init_l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11);
lean_mark_persistent(l_Array_mapIdxM_map___at_Lean_Meta_IndPredBelow_mkBelowMatcher___spec__4___lambda__1___closed__11);
_init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1);
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__1);
_init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2);
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__2);
_init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3);
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__3);
_init_l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4);
lean_mark_persistent(l_Lean_Expr_withAppAux___at_Lean_Meta_IndPredBelow_findBelowIdx___spec__3___closed__4);
_init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1);
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__1);
_init_l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2);
lean_mark_persistent(l_Std_Range_forIn_loop___at_Lean_Meta_IndPredBelow_mkBelow___spec__1___closed__2);
_init_l_Lean_Meta_IndPredBelow_mkBelow___closed__1(l_Lean_Meta_IndPredBelow_mkBelow___closed__1);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__1);
_init_l_Lean_Meta_IndPredBelow_mkBelow___closed__2(l_Lean_Meta_IndPredBelow_mkBelow___closed__2);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__2);
_init_l_Lean_Meta_IndPredBelow_mkBelow___closed__3(l_Lean_Meta_IndPredBelow_mkBelow___closed__3);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__3);
_init_l_Lean_Meta_IndPredBelow_mkBelow___closed__4(l_Lean_Meta_IndPredBelow_mkBelow___closed__4);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__4);
_init_l_Lean_Meta_IndPredBelow_mkBelow___closed__5(l_Lean_Meta_IndPredBelow_mkBelow___closed__5);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__5);
_init_l_Lean_Meta_IndPredBelow_mkBelow___closed__6(l_Lean_Meta_IndPredBelow_mkBelow___closed__6);
lean_mark_persistent(l_Lean_Meta_IndPredBelow_mkBelow___closed__6);
res = l_Lean_Meta_IndPredBelow_initFn____x40_Lean_Meta_IndPredBelow___hyg_5254_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
