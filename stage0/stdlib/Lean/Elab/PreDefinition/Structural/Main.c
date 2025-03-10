// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Main
// Imports: Lean.Elab.PreDefinition.TerminationMeasure Lean.Elab.PreDefinition.Mutual Lean.Elab.PreDefinition.Structural.Basic Lean.Elab.PreDefinition.Structural.FindRecArg Lean.Elab.PreDefinition.Structural.Preprocess Lean.Elab.PreDefinition.Structural.BRecOn Lean.Elab.PreDefinition.Structural.IndPred Lean.Elab.PreDefinition.Structural.Eqns Lean.Elab.PreDefinition.Structural.SmartUnfolding Lean.Meta.Tactic.TryThis
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
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__39___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBrecOnApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__7;
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_withCommonTelescope_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__36(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__1;
lean_object* l_Lean_Meta_generateEagerEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__24___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__8(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDecl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_reporttermMeasure___closed__2;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Mutual_withCommonTelescope___spec__1(size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__8;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__11;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__2;
static lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
static lean_object* l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_markAsRecursive(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__15;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__4;
static lean_object* l_Lean_Elab_Structural_reporttermMeasure___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__1;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__6;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__25(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__26(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__3;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Class_0__Lean_checkOutParam___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__33(lean_object*);
lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__22___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__5;
lean_object* l___private_Lean_Elab_PreDefinition_Structural_RecArgInfo_0__Lean_Elab_Structural_reprRecArgInfo____x40_Lean_Elab_PreDefinition_Structural_RecArgInfo___hyg_71_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__4(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__19(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__22(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__40(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__25___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__5;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__2;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__1___boxed(lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_buildArgs___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__1;
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__14;
extern lean_object* l_Lean_Elab_Structural_instInhabitedRecArgInfo;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__27(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__5___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_Structural_mkIndPredBRecOn___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__32(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerm_instantiateLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__4;
lean_object* l_panic___at_Lean_Elab_Structural_Positions_groupAndSort___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_range___lambda__1___boxed(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__42___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_applyAttributesOf(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_FixedParamPerms_erase(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__3;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__12;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__9;
lean_object* l_Array_zip___rarg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_forEachExpr_x27___at_Lean_Meta_setMVarUserNamesAt___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofFn___rarg(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__1(lean_object*);
lean_object* l_Lean_Elab_addNonRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_withErasedFVars___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__4;
static lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__2;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__3;
static lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__16;
lean_object* l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__17(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_tryAllArgs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__1;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_isInductivePredicate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__2;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__18(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed__const__1;
lean_object* l_Lean_Elab_Structural_run___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_abstractNestedProofs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1;
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8___boxed__const__1;
lean_object* l_Lean_Elab_Structural_inferBRecOnFTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__6;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___boxed(lean_object**);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__2;
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__7(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__4___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__1;
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__6;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__17___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___closed__1;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__2;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__6;
lean_object* l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__1;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_withCommonTelescope_go___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__23(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlTOfPure___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__23___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__7;
lean_object* l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__20(lean_object*, lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_Structural_reporttermMeasure___closed__5;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__28(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__13;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVarOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__3;
lean_object* l_Array_qsort_sort___at_Lean_Elab_Structural_Positions_groupAndSort___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__4;
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__10;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnMotive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__12(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8(lean_object*);
lean_object* l_Lean_Elab_Structural_mkIndPredBRecOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Structural_mkBRecOnF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__24(lean_object*, lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntax(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__5;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__2;
static lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_reporttermMeasure___closed__6;
uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_Mutual_withCommonTelescope_go___spec__3(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__36___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__37(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2;
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__15___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__2;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__36___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__37___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__38(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Structural_reporttermMeasure___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__31(size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_withCommonTelescope_go___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__34(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__35(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_pure___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__14(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_TerminationMeasure_delab(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__2;
lean_object* l_Lean_Elab_Structural_addSmartUnfoldingDef(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_withCommonTelescope_go___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__1;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
static lean_object* l_Lean_Elab_Structural_reporttermMeasure___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope_go___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__16___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_Positions_groupAndSort___spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__13___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__14___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__15(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_Structural_reporttermMeasure___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__14___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__13___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__12___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__2;
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__8___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__19(lean_object*, lean_object*, size_t, size_t);
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__42(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_uget(x_5, x_7);
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_8, 1);
x_19 = lean_ctor_get(x_8, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 2);
lean_inc(x_22);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_4);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_13);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_26 = lean_ctor_get(x_18, 2);
lean_dec(x_26);
x_27 = lean_ctor_get(x_18, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = lean_array_fget(x_20, x_21);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_21, x_30);
lean_dec(x_21);
lean_ctor_set(x_18, 1, x_31);
x_32 = lean_ctor_get(x_9, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_34 = lean_ctor_get(x_9, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_9, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_9, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_9, 4);
lean_inc(x_37);
x_38 = lean_ctor_get(x_9, 5);
lean_inc(x_38);
x_39 = lean_ctor_get(x_9, 6);
lean_inc(x_39);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint64_t x_60; uint8_t x_61; lean_object* x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; lean_object* x_68; lean_object* x_69; 
x_41 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_42 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_43 = lean_ctor_get_uint8(x_32, 0);
x_44 = lean_ctor_get_uint8(x_32, 1);
x_45 = lean_ctor_get_uint8(x_32, 2);
x_46 = lean_ctor_get_uint8(x_32, 3);
x_47 = lean_ctor_get_uint8(x_32, 4);
x_48 = lean_ctor_get_uint8(x_32, 5);
x_49 = lean_ctor_get_uint8(x_32, 7);
x_50 = lean_ctor_get_uint8(x_32, 8);
x_51 = lean_ctor_get_uint8(x_32, 10);
x_52 = lean_ctor_get_uint8(x_32, 11);
x_53 = lean_ctor_get_uint8(x_32, 12);
x_54 = lean_ctor_get_uint8(x_32, 13);
x_55 = lean_ctor_get_uint8(x_32, 14);
x_56 = lean_ctor_get_uint8(x_32, 15);
x_57 = lean_ctor_get_uint8(x_32, 16);
x_58 = lean_ctor_get_uint8(x_32, 17);
x_59 = 0;
lean_ctor_set_uint8(x_32, 6, x_59);
x_60 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_32);
lean_dec(x_32);
x_61 = 2;
x_62 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_62, 0, x_43);
lean_ctor_set_uint8(x_62, 1, x_44);
lean_ctor_set_uint8(x_62, 2, x_45);
lean_ctor_set_uint8(x_62, 3, x_46);
lean_ctor_set_uint8(x_62, 4, x_47);
lean_ctor_set_uint8(x_62, 5, x_48);
lean_ctor_set_uint8(x_62, 6, x_59);
lean_ctor_set_uint8(x_62, 7, x_49);
lean_ctor_set_uint8(x_62, 8, x_50);
lean_ctor_set_uint8(x_62, 9, x_61);
lean_ctor_set_uint8(x_62, 10, x_51);
lean_ctor_set_uint8(x_62, 11, x_52);
lean_ctor_set_uint8(x_62, 12, x_53);
lean_ctor_set_uint8(x_62, 13, x_54);
lean_ctor_set_uint8(x_62, 14, x_55);
lean_ctor_set_uint8(x_62, 15, x_56);
lean_ctor_set_uint8(x_62, 16, x_57);
lean_ctor_set_uint8(x_62, 17, x_58);
x_63 = 2;
x_64 = lean_uint64_shift_right(x_60, x_63);
x_65 = lean_uint64_shift_left(x_64, x_63);
x_66 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
x_67 = lean_uint64_lor(x_65, x_66);
x_68 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_34);
lean_ctor_set(x_68, 2, x_35);
lean_ctor_set(x_68, 3, x_36);
lean_ctor_set(x_68, 4, x_37);
lean_ctor_set(x_68, 5, x_38);
lean_ctor_set(x_68, 6, x_39);
lean_ctor_set_uint64(x_68, sizeof(void*)*7, x_67);
lean_ctor_set_uint8(x_68, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_68, sizeof(void*)*7 + 9, x_41);
lean_ctor_set_uint8(x_68, sizeof(void*)*7 + 10, x_42);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_69 = l_Lean_Meta_isExprDefEq(x_16, x_29, x_68, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
uint8_t x_72; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_72 = !lean_is_exclusive(x_69);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_69, 0);
lean_dec(x_73);
x_74 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2;
lean_ctor_set(x_8, 0, x_74);
lean_ctor_set(x_69, 0, x_8);
return x_69;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_dec(x_69);
x_76 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2;
lean_ctor_set(x_8, 0, x_76);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_8);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; size_t x_79; size_t x_80; 
x_78 = lean_ctor_get(x_69, 1);
lean_inc(x_78);
lean_dec(x_69);
lean_inc(x_4);
lean_ctor_set(x_8, 0, x_4);
x_79 = 1;
x_80 = lean_usize_add(x_7, x_79);
x_7 = x_80;
x_13 = x_78;
goto _start;
}
}
else
{
uint8_t x_82; 
lean_dec(x_18);
lean_free_object(x_8);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_69);
if (x_82 == 0)
{
return x_69;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_69, 0);
x_84 = lean_ctor_get(x_69, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_69);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; uint64_t x_107; uint8_t x_108; lean_object* x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; lean_object* x_115; lean_object* x_116; 
x_86 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_87 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_88 = lean_ctor_get_uint8(x_32, 0);
x_89 = lean_ctor_get_uint8(x_32, 1);
x_90 = lean_ctor_get_uint8(x_32, 2);
x_91 = lean_ctor_get_uint8(x_32, 3);
x_92 = lean_ctor_get_uint8(x_32, 4);
x_93 = lean_ctor_get_uint8(x_32, 5);
x_94 = lean_ctor_get_uint8(x_32, 7);
x_95 = lean_ctor_get_uint8(x_32, 8);
x_96 = lean_ctor_get_uint8(x_32, 9);
x_97 = lean_ctor_get_uint8(x_32, 10);
x_98 = lean_ctor_get_uint8(x_32, 11);
x_99 = lean_ctor_get_uint8(x_32, 12);
x_100 = lean_ctor_get_uint8(x_32, 13);
x_101 = lean_ctor_get_uint8(x_32, 14);
x_102 = lean_ctor_get_uint8(x_32, 15);
x_103 = lean_ctor_get_uint8(x_32, 16);
x_104 = lean_ctor_get_uint8(x_32, 17);
lean_dec(x_32);
x_105 = 0;
x_106 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_106, 0, x_88);
lean_ctor_set_uint8(x_106, 1, x_89);
lean_ctor_set_uint8(x_106, 2, x_90);
lean_ctor_set_uint8(x_106, 3, x_91);
lean_ctor_set_uint8(x_106, 4, x_92);
lean_ctor_set_uint8(x_106, 5, x_93);
lean_ctor_set_uint8(x_106, 6, x_105);
lean_ctor_set_uint8(x_106, 7, x_94);
lean_ctor_set_uint8(x_106, 8, x_95);
lean_ctor_set_uint8(x_106, 9, x_96);
lean_ctor_set_uint8(x_106, 10, x_97);
lean_ctor_set_uint8(x_106, 11, x_98);
lean_ctor_set_uint8(x_106, 12, x_99);
lean_ctor_set_uint8(x_106, 13, x_100);
lean_ctor_set_uint8(x_106, 14, x_101);
lean_ctor_set_uint8(x_106, 15, x_102);
lean_ctor_set_uint8(x_106, 16, x_103);
lean_ctor_set_uint8(x_106, 17, x_104);
x_107 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_106);
lean_dec(x_106);
x_108 = 2;
x_109 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_109, 0, x_88);
lean_ctor_set_uint8(x_109, 1, x_89);
lean_ctor_set_uint8(x_109, 2, x_90);
lean_ctor_set_uint8(x_109, 3, x_91);
lean_ctor_set_uint8(x_109, 4, x_92);
lean_ctor_set_uint8(x_109, 5, x_93);
lean_ctor_set_uint8(x_109, 6, x_105);
lean_ctor_set_uint8(x_109, 7, x_94);
lean_ctor_set_uint8(x_109, 8, x_95);
lean_ctor_set_uint8(x_109, 9, x_108);
lean_ctor_set_uint8(x_109, 10, x_97);
lean_ctor_set_uint8(x_109, 11, x_98);
lean_ctor_set_uint8(x_109, 12, x_99);
lean_ctor_set_uint8(x_109, 13, x_100);
lean_ctor_set_uint8(x_109, 14, x_101);
lean_ctor_set_uint8(x_109, 15, x_102);
lean_ctor_set_uint8(x_109, 16, x_103);
lean_ctor_set_uint8(x_109, 17, x_104);
x_110 = 2;
x_111 = lean_uint64_shift_right(x_107, x_110);
x_112 = lean_uint64_shift_left(x_111, x_110);
x_113 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
x_114 = lean_uint64_lor(x_112, x_113);
x_115 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_34);
lean_ctor_set(x_115, 2, x_35);
lean_ctor_set(x_115, 3, x_36);
lean_ctor_set(x_115, 4, x_37);
lean_ctor_set(x_115, 5, x_38);
lean_ctor_set(x_115, 6, x_39);
lean_ctor_set_uint64(x_115, sizeof(void*)*7, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*7 + 8, x_33);
lean_ctor_set_uint8(x_115, sizeof(void*)*7 + 9, x_86);
lean_ctor_set_uint8(x_115, sizeof(void*)*7 + 10, x_87);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_116 = l_Lean_Meta_isExprDefEq(x_16, x_29, x_115, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
x_121 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2;
lean_ctor_set(x_8, 0, x_121);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_8);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
else
{
lean_object* x_123; size_t x_124; size_t x_125; 
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
lean_dec(x_116);
lean_inc(x_4);
lean_ctor_set(x_8, 0, x_4);
x_124 = 1;
x_125 = lean_usize_add(x_7, x_124);
x_7 = x_125;
x_13 = x_123;
goto _start;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_18);
lean_free_object(x_8);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_127 = lean_ctor_get(x_116, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_116, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_129 = x_116;
} else {
 lean_dec_ref(x_116);
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
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; uint64_t x_165; uint8_t x_166; lean_object* x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_18);
x_131 = lean_array_fget(x_20, x_21);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_nat_add(x_21, x_132);
lean_dec(x_21);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_20);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set(x_134, 2, x_22);
x_135 = lean_ctor_get(x_9, 0);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_137 = lean_ctor_get(x_9, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_9, 2);
lean_inc(x_138);
x_139 = lean_ctor_get(x_9, 3);
lean_inc(x_139);
x_140 = lean_ctor_get(x_9, 4);
lean_inc(x_140);
x_141 = lean_ctor_get(x_9, 5);
lean_inc(x_141);
x_142 = lean_ctor_get(x_9, 6);
lean_inc(x_142);
x_143 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_144 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_145 = lean_ctor_get_uint8(x_135, 0);
x_146 = lean_ctor_get_uint8(x_135, 1);
x_147 = lean_ctor_get_uint8(x_135, 2);
x_148 = lean_ctor_get_uint8(x_135, 3);
x_149 = lean_ctor_get_uint8(x_135, 4);
x_150 = lean_ctor_get_uint8(x_135, 5);
x_151 = lean_ctor_get_uint8(x_135, 7);
x_152 = lean_ctor_get_uint8(x_135, 8);
x_153 = lean_ctor_get_uint8(x_135, 9);
x_154 = lean_ctor_get_uint8(x_135, 10);
x_155 = lean_ctor_get_uint8(x_135, 11);
x_156 = lean_ctor_get_uint8(x_135, 12);
x_157 = lean_ctor_get_uint8(x_135, 13);
x_158 = lean_ctor_get_uint8(x_135, 14);
x_159 = lean_ctor_get_uint8(x_135, 15);
x_160 = lean_ctor_get_uint8(x_135, 16);
x_161 = lean_ctor_get_uint8(x_135, 17);
if (lean_is_exclusive(x_135)) {
 x_162 = x_135;
} else {
 lean_dec_ref(x_135);
 x_162 = lean_box(0);
}
x_163 = 0;
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 0, 18);
} else {
 x_164 = x_162;
}
lean_ctor_set_uint8(x_164, 0, x_145);
lean_ctor_set_uint8(x_164, 1, x_146);
lean_ctor_set_uint8(x_164, 2, x_147);
lean_ctor_set_uint8(x_164, 3, x_148);
lean_ctor_set_uint8(x_164, 4, x_149);
lean_ctor_set_uint8(x_164, 5, x_150);
lean_ctor_set_uint8(x_164, 6, x_163);
lean_ctor_set_uint8(x_164, 7, x_151);
lean_ctor_set_uint8(x_164, 8, x_152);
lean_ctor_set_uint8(x_164, 9, x_153);
lean_ctor_set_uint8(x_164, 10, x_154);
lean_ctor_set_uint8(x_164, 11, x_155);
lean_ctor_set_uint8(x_164, 12, x_156);
lean_ctor_set_uint8(x_164, 13, x_157);
lean_ctor_set_uint8(x_164, 14, x_158);
lean_ctor_set_uint8(x_164, 15, x_159);
lean_ctor_set_uint8(x_164, 16, x_160);
lean_ctor_set_uint8(x_164, 17, x_161);
x_165 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_164);
lean_dec(x_164);
x_166 = 2;
x_167 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_167, 0, x_145);
lean_ctor_set_uint8(x_167, 1, x_146);
lean_ctor_set_uint8(x_167, 2, x_147);
lean_ctor_set_uint8(x_167, 3, x_148);
lean_ctor_set_uint8(x_167, 4, x_149);
lean_ctor_set_uint8(x_167, 5, x_150);
lean_ctor_set_uint8(x_167, 6, x_163);
lean_ctor_set_uint8(x_167, 7, x_151);
lean_ctor_set_uint8(x_167, 8, x_152);
lean_ctor_set_uint8(x_167, 9, x_166);
lean_ctor_set_uint8(x_167, 10, x_154);
lean_ctor_set_uint8(x_167, 11, x_155);
lean_ctor_set_uint8(x_167, 12, x_156);
lean_ctor_set_uint8(x_167, 13, x_157);
lean_ctor_set_uint8(x_167, 14, x_158);
lean_ctor_set_uint8(x_167, 15, x_159);
lean_ctor_set_uint8(x_167, 16, x_160);
lean_ctor_set_uint8(x_167, 17, x_161);
x_168 = 2;
x_169 = lean_uint64_shift_right(x_165, x_168);
x_170 = lean_uint64_shift_left(x_169, x_168);
x_171 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
x_172 = lean_uint64_lor(x_170, x_171);
x_173 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_173, 0, x_167);
lean_ctor_set(x_173, 1, x_137);
lean_ctor_set(x_173, 2, x_138);
lean_ctor_set(x_173, 3, x_139);
lean_ctor_set(x_173, 4, x_140);
lean_ctor_set(x_173, 5, x_141);
lean_ctor_set(x_173, 6, x_142);
lean_ctor_set_uint64(x_173, sizeof(void*)*7, x_172);
lean_ctor_set_uint8(x_173, sizeof(void*)*7 + 8, x_136);
lean_ctor_set_uint8(x_173, sizeof(void*)*7 + 9, x_143);
lean_ctor_set_uint8(x_173, sizeof(void*)*7 + 10, x_144);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_174 = l_Lean_Meta_isExprDefEq(x_16, x_131, x_173, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_178 = x_174;
} else {
 lean_dec_ref(x_174);
 x_178 = lean_box(0);
}
x_179 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2;
lean_ctor_set(x_8, 1, x_134);
lean_ctor_set(x_8, 0, x_179);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_8);
lean_ctor_set(x_180, 1, x_177);
return x_180;
}
else
{
lean_object* x_181; size_t x_182; size_t x_183; 
x_181 = lean_ctor_get(x_174, 1);
lean_inc(x_181);
lean_dec(x_174);
lean_inc(x_4);
lean_ctor_set(x_8, 1, x_134);
lean_ctor_set(x_8, 0, x_4);
x_182 = 1;
x_183 = lean_usize_add(x_7, x_182);
x_7 = x_183;
x_13 = x_181;
goto _start;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_134);
lean_free_object(x_8);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_185 = lean_ctor_get(x_174, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_187 = x_174;
} else {
 lean_dec_ref(x_174);
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
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_189 = lean_ctor_get(x_8, 1);
lean_inc(x_189);
lean_dec(x_8);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
x_192 = lean_ctor_get(x_189, 2);
lean_inc(x_192);
x_193 = lean_nat_dec_lt(x_191, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_4);
lean_ctor_set(x_194, 1, x_189);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_195, 1, x_13);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; uint8_t x_210; uint8_t x_211; uint8_t x_212; uint8_t x_213; uint8_t x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; uint8_t x_220; uint8_t x_221; uint8_t x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; uint64_t x_231; uint8_t x_232; lean_object* x_233; uint64_t x_234; uint64_t x_235; uint64_t x_236; uint64_t x_237; uint64_t x_238; lean_object* x_239; lean_object* x_240; 
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 x_196 = x_189;
} else {
 lean_dec_ref(x_189);
 x_196 = lean_box(0);
}
x_197 = lean_array_fget(x_190, x_191);
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_add(x_191, x_198);
lean_dec(x_191);
if (lean_is_scalar(x_196)) {
 x_200 = lean_alloc_ctor(0, 3, 0);
} else {
 x_200 = x_196;
}
lean_ctor_set(x_200, 0, x_190);
lean_ctor_set(x_200, 1, x_199);
lean_ctor_set(x_200, 2, x_192);
x_201 = lean_ctor_get(x_9, 0);
lean_inc(x_201);
x_202 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_203 = lean_ctor_get(x_9, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_9, 2);
lean_inc(x_204);
x_205 = lean_ctor_get(x_9, 3);
lean_inc(x_205);
x_206 = lean_ctor_get(x_9, 4);
lean_inc(x_206);
x_207 = lean_ctor_get(x_9, 5);
lean_inc(x_207);
x_208 = lean_ctor_get(x_9, 6);
lean_inc(x_208);
x_209 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_210 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
x_211 = lean_ctor_get_uint8(x_201, 0);
x_212 = lean_ctor_get_uint8(x_201, 1);
x_213 = lean_ctor_get_uint8(x_201, 2);
x_214 = lean_ctor_get_uint8(x_201, 3);
x_215 = lean_ctor_get_uint8(x_201, 4);
x_216 = lean_ctor_get_uint8(x_201, 5);
x_217 = lean_ctor_get_uint8(x_201, 7);
x_218 = lean_ctor_get_uint8(x_201, 8);
x_219 = lean_ctor_get_uint8(x_201, 9);
x_220 = lean_ctor_get_uint8(x_201, 10);
x_221 = lean_ctor_get_uint8(x_201, 11);
x_222 = lean_ctor_get_uint8(x_201, 12);
x_223 = lean_ctor_get_uint8(x_201, 13);
x_224 = lean_ctor_get_uint8(x_201, 14);
x_225 = lean_ctor_get_uint8(x_201, 15);
x_226 = lean_ctor_get_uint8(x_201, 16);
x_227 = lean_ctor_get_uint8(x_201, 17);
if (lean_is_exclusive(x_201)) {
 x_228 = x_201;
} else {
 lean_dec_ref(x_201);
 x_228 = lean_box(0);
}
x_229 = 0;
if (lean_is_scalar(x_228)) {
 x_230 = lean_alloc_ctor(0, 0, 18);
} else {
 x_230 = x_228;
}
lean_ctor_set_uint8(x_230, 0, x_211);
lean_ctor_set_uint8(x_230, 1, x_212);
lean_ctor_set_uint8(x_230, 2, x_213);
lean_ctor_set_uint8(x_230, 3, x_214);
lean_ctor_set_uint8(x_230, 4, x_215);
lean_ctor_set_uint8(x_230, 5, x_216);
lean_ctor_set_uint8(x_230, 6, x_229);
lean_ctor_set_uint8(x_230, 7, x_217);
lean_ctor_set_uint8(x_230, 8, x_218);
lean_ctor_set_uint8(x_230, 9, x_219);
lean_ctor_set_uint8(x_230, 10, x_220);
lean_ctor_set_uint8(x_230, 11, x_221);
lean_ctor_set_uint8(x_230, 12, x_222);
lean_ctor_set_uint8(x_230, 13, x_223);
lean_ctor_set_uint8(x_230, 14, x_224);
lean_ctor_set_uint8(x_230, 15, x_225);
lean_ctor_set_uint8(x_230, 16, x_226);
lean_ctor_set_uint8(x_230, 17, x_227);
x_231 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_230);
lean_dec(x_230);
x_232 = 2;
x_233 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_233, 0, x_211);
lean_ctor_set_uint8(x_233, 1, x_212);
lean_ctor_set_uint8(x_233, 2, x_213);
lean_ctor_set_uint8(x_233, 3, x_214);
lean_ctor_set_uint8(x_233, 4, x_215);
lean_ctor_set_uint8(x_233, 5, x_216);
lean_ctor_set_uint8(x_233, 6, x_229);
lean_ctor_set_uint8(x_233, 7, x_217);
lean_ctor_set_uint8(x_233, 8, x_218);
lean_ctor_set_uint8(x_233, 9, x_232);
lean_ctor_set_uint8(x_233, 10, x_220);
lean_ctor_set_uint8(x_233, 11, x_221);
lean_ctor_set_uint8(x_233, 12, x_222);
lean_ctor_set_uint8(x_233, 13, x_223);
lean_ctor_set_uint8(x_233, 14, x_224);
lean_ctor_set_uint8(x_233, 15, x_225);
lean_ctor_set_uint8(x_233, 16, x_226);
lean_ctor_set_uint8(x_233, 17, x_227);
x_234 = 2;
x_235 = lean_uint64_shift_right(x_231, x_234);
x_236 = lean_uint64_shift_left(x_235, x_234);
x_237 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1;
x_238 = lean_uint64_lor(x_236, x_237);
x_239 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_239, 0, x_233);
lean_ctor_set(x_239, 1, x_203);
lean_ctor_set(x_239, 2, x_204);
lean_ctor_set(x_239, 3, x_205);
lean_ctor_set(x_239, 4, x_206);
lean_ctor_set(x_239, 5, x_207);
lean_ctor_set(x_239, 6, x_208);
lean_ctor_set_uint64(x_239, sizeof(void*)*7, x_238);
lean_ctor_set_uint8(x_239, sizeof(void*)*7 + 8, x_202);
lean_ctor_set_uint8(x_239, sizeof(void*)*7 + 9, x_209);
lean_ctor_set_uint8(x_239, sizeof(void*)*7 + 10, x_210);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_240 = l_Lean_Meta_isExprDefEq(x_16, x_197, x_239, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; uint8_t x_242; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_unbox(x_241);
lean_dec(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_244 = x_240;
} else {
 lean_dec_ref(x_240);
 x_244 = lean_box(0);
}
x_245 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2;
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_200);
if (lean_is_scalar(x_244)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_244;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_243);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; size_t x_250; size_t x_251; 
x_248 = lean_ctor_get(x_240, 1);
lean_inc(x_248);
lean_dec(x_240);
lean_inc(x_4);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_4);
lean_ctor_set(x_249, 1, x_200);
x_250 = 1;
x_251 = lean_usize_add(x_7, x_250);
x_7 = x_251;
x_8 = x_249;
x_13 = x_248;
goto _start;
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_200);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
x_253 = lean_ctor_get(x_240, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_240, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_255 = x_240;
} else {
 lean_dec_ref(x_240);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isAppOf(x_6, x_1);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_6, x_16);
x_18 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1;
lean_inc(x_17);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_17, x_20);
lean_dec(x_17);
x_22 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_6, x_19, x_21);
x_48 = lean_st_ref_take(x_5, x_11);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_array_get_size(x_22);
x_52 = lean_nat_dec_lt(x_51, x_49);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
x_53 = lean_st_ref_set(x_5, x_49, x_50);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_23 = x_54;
goto block_47;
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_49);
x_55 = lean_st_ref_set(x_5, x_51, x_50);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_23 = x_56;
goto block_47;
}
block_47:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_24 = l_Array_toSubarray___rarg(x_2, x_16, x_3);
x_25 = lean_box(0);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
x_28 = lean_array_size(x_22);
x_29 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_30 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1(x_4, x_22, x_25, x_26, x_22, x_28, x_29, x_27, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2;
x_35 = lean_box(0);
x_36 = lean_apply_6(x_34, x_35, x_7, x_8, x_9, x_10, x_33);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__1;
x_2 = l_ReaderT_instApplicativeOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__2;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_instMonadControlTOfPure___rarg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_array_get_size(x_2);
lean_inc(x_9);
x_10 = lean_st_mk_ref(x_9, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__3;
lean_inc(x_11);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___boxed), 11, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_9);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_11);
x_15 = l_Lean_Meta_forEachExpr_x27___at_Lean_Meta_setMVarUserNamesAt___spec__6(x_3, x_14, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
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
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_11);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_16 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1(x_1, x_2, x_3, x_4, x_5, x_14, x_15, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_withCommonTelescope_go___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_9 = l_Lean_Expr_bindingBody_x21(x_6);
lean_dec(x_6);
x_10 = lean_expr_instantiate1(x_9, x_1);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_10);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_withCommonTelescope_go___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_array_uget(x_2, x_3);
x_13 = l_Lean_Expr_bindingDomain_x21(x_12);
lean_dec(x_12);
x_14 = l_Lean_instInhabitedExpr;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_1, x_15);
x_17 = l_Lean_Expr_bindingDomain_x21(x_16);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l_Lean_Meta_isExprDefEq(x_13, x_17, x_6, x_7, x_8, x_9, x_10);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = 1;
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
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; 
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_dec(x_18);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
x_10 = x_29;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
uint8_t x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_37 = 0;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_10);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope_go___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_4);
x_11 = lean_array_push(x_1, x_4);
x_12 = lean_array_size(x_2);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_withCommonTelescope_go___spec__1(x_4, x_12, x_13, x_2);
lean_dec(x_4);
x_15 = l_Lean_Elab_Structural_withCommonTelescope_go___rarg(x_3, x_11, x_14, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_41; uint8_t x_42; 
x_10 = lean_array_get_size(x_3);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_nat_dec_lt(x_41, x_10);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_box(0);
x_11 = x_43;
goto block_40;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = 0;
x_45 = lean_usize_of_nat(x_10);
x_46 = l_Array_anyMUnsafe_any___at_Lean_Elab_Mutual_withCommonTelescope_go___spec__3(x_3, x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_box(0);
x_11 = x_47;
goto block_40;
}
else
{
lean_object* x_48; 
lean_dec(x_10);
x_48 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_48;
}
}
block_40:
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
lean_dec(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_10);
if (x_13 == 0)
{
uint8_t x_26; 
lean_dec(x_10);
x_26 = 1;
x_14 = x_26;
x_15 = x_9;
goto block_25;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = 0;
x_28 = lean_usize_of_nat(x_10);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_withCommonTelescope_go___spec__2(x_3, x_3, x_27, x_28, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = 1;
x_14 = x_33;
x_15 = x_32;
goto block_25;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = 0;
x_14 = x_35;
x_15 = x_34;
goto block_25;
}
}
else
{
uint8_t x_36; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
block_25:
{
if (x_14 == 0)
{
lean_object* x_16; 
x_16 = lean_apply_8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_array_get(x_17, x_3, x_12);
x_19 = l_Lean_Expr_bindingName_x21(x_18);
x_20 = l_Lean_Expr_binderInfo(x_18);
x_21 = l_Lean_Expr_bindingDomain_x21(x_18);
lean_dec(x_18);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_withCommonTelescope_go___rarg___lambda__1), 10, 3);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_1);
x_23 = 0;
x_24 = l_Lean_Meta_withLocalDecl___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___spec__7___rarg(x_19, x_20, x_21, x_22, x_23, x_4, x_5, x_6, x_7, x_8, x_15);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_withCommonTelescope_go___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_withCommonTelescope_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_Structural_withCommonTelescope_go___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_withCommonTelescope_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_anyMUnsafe_any___at_Lean_Elab_Structural_withCommonTelescope_go___spec__2(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_size(x_1);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lean_Elab_Mutual_withCommonTelescope___spec__1(x_9, x_10, x_1);
x_12 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_13 = l_Lean_Elab_Structural_withCommonTelescope_go___rarg(x_2, x_12, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_withCommonTelescope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_withCommonTelescope___rarg), 8, 0);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_5, x_17);
lean_dec(x_5);
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_ctor_get(x_2, 1);
x_21 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1;
x_22 = lean_array_get(x_21, x_20, x_6);
x_23 = lean_ctor_get(x_19, 5);
lean_inc(x_23);
lean_dec(x_19);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_3);
x_24 = l_Lean_Elab_FixedParamPerm_instantiateLambda(x_22, x_23, x_3, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_add(x_6, x_17);
lean_dec(x_6);
x_28 = lean_array_push(x_8, x_25);
x_5 = x_18;
x_6 = x_27;
x_7 = lean_box(0);
x_8 = x_28;
x_14 = x_26;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
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
lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_14);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
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
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' is not a inductive type", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_getConstInfo___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_addBelow___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 5)
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = 0;
x_18 = l_Lean_MessageData_ofConstName(x_1, x_17);
x_19 = l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__2;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__4;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__3(x_22, x_2, x_3, x_4, x_5, x_6, x_16);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; size_t x_14; size_t x_15; 
x_10 = lean_array_uget(x_5, x_6);
lean_inc(x_1);
x_11 = lean_array_get(x_1, x_3, x_10);
lean_inc(x_2);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_nat_dec_eq(x_12, x_4);
lean_dec(x_12);
x_14 = 1;
x_15 = lean_usize_add(x_6, x_14);
if (x_13 == 0)
{
lean_dec(x_10);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_array_push(x_8, x_10);
x_6 = x_15;
x_8 = x_17;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_range___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; size_t x_16; size_t x_17; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_6, x_5, x_9);
x_11 = lean_array_get_size(x_3);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___closed__1;
x_13 = l_Array_ofFn___rarg(x_11, x_12);
lean_dec(x_11);
x_14 = lean_array_get_size(x_13);
x_15 = lean_nat_dec_lt(x_9, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_5, x_16);
if (x_15 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
x_18 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_19 = lean_array_uset(x_10, x_5, x_18);
x_5 = x_17;
x_6 = x_19;
goto _start;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_14, x_14);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
x_22 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_23 = lean_array_uset(x_10, x_5, x_22);
x_5 = x_17;
x_6 = x_23;
goto _start;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_27 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
lean_inc(x_2);
lean_inc(x_1);
x_28 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__5(x_1, x_2, x_3, x_8, x_13, x_25, x_26, x_27);
lean_dec(x_13);
lean_dec(x_8);
x_29 = lean_array_uset(x_10, x_5, x_28);
x_5 = x_17;
x_6 = x_29;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_array_fget(x_4, x_11);
x_13 = lean_array_fget(x_5, x_11);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
x_3 = lean_box(0);
x_6 = x_11;
x_7 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = 1;
return x_17;
}
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Array.range xs.size == positions.flatten.qsort Nat.blt\n  ", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__1;
x_2 = l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.Structural.Basic", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.Structural.Positions.groupAndSort", 43, 43);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__4;
x_2 = l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__5;
x_3 = lean_unsigned_to_nat(86u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_24; 
x_5 = lean_array_size(x_4);
x_6 = 0;
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6(x_1, x_2, x_3, x_5, x_6, x_4);
x_8 = lean_array_get_size(x_3);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___closed__1;
x_10 = l_Array_ofFn___rarg(x_8, x_9);
lean_dec(x_8);
x_11 = lean_array_get_size(x_7);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = lean_array_get_size(x_10);
if (x_13 == 0)
{
lean_object* x_33; 
lean_dec(x_11);
x_33 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1;
x_24 = x_33;
goto block_32;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_11, x_11);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_11);
x_35 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1;
x_24 = x_35;
goto block_32;
}
else
{
size_t x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_37 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1;
x_38 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_Positions_groupAndSort___spec__6(x_7, x_6, x_36, x_37);
x_24 = x_38;
goto block_32;
}
}
block_23:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_get_size(x_15);
x_17 = lean_nat_dec_eq(x_14, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_7);
x_18 = l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__6;
x_19 = l_panic___at_Lean_Elab_Structural_Positions_groupAndSort___spec__3(x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = l_Array_isEqvAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__7(x_3, x_15, lean_box(0), x_10, x_15, x_14, lean_box(0));
lean_dec(x_10);
lean_dec(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_21 = l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__6;
x_22 = l_panic___at_Lean_Elab_Structural_Positions_groupAndSort___spec__3(x_21);
return x_22;
}
else
{
return x_7;
}
}
}
block_32:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_array_get_size(x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
x_28 = lean_nat_dec_eq(x_25, x_12);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_12, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_inc(x_27);
x_30 = l_Array_qsort_sort___at_Lean_Elab_Structural_Positions_groupAndSort___spec__5(x_25, x_24, x_27, x_27, lean_box(0), lean_box(0));
lean_dec(x_27);
lean_dec(x_25);
x_15 = x_30;
goto block_23;
}
else
{
lean_object* x_31; 
x_31 = l_Array_qsort_sort___at_Lean_Elab_Structural_Positions_groupAndSort___spec__5(x_25, x_24, x_12, x_27, lean_box(0), lean_box(0));
lean_dec(x_27);
lean_dec(x_25);
x_15 = x_31;
goto block_23;
}
}
else
{
lean_dec(x_27);
lean_dec(x_25);
x_15 = x_24;
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__8(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_uset(x_3, x_2, x_13);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Lean_Elab_Structural_mkBRecOnMotive(x_15, x_16, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_14, x_2, x_18);
x_2 = x_21;
x_3 = x_22;
x_9 = x_19;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_array_uget(x_5, x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_5, x_4, x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Lean_Elab_Structural_mkBRecOnF(x_1, x_2, x_18, x_19, x_20, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = 1;
x_25 = lean_usize_add(x_4, x_24);
x_26 = lean_array_uset(x_16, x_4, x_22);
x_4 = x_25;
x_5 = x_26;
x_11 = x_23;
goto _start;
}
else
{
uint8_t x_28; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_6, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_6, x_18);
lean_dec(x_6);
x_20 = lean_array_fget(x_5, x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_7);
lean_inc(x_1);
x_23 = l_Lean_Elab_Structural_mkBrecOnApp(x_1, x_7, x_3, x_4, x_21, x_22, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_nat_add(x_7, x_18);
lean_dec(x_7);
x_27 = lean_array_push(x_9, x_24);
x_6 = x_19;
x_7 = x_26;
x_8 = lean_box(0);
x_9 = x_27;
x_15 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_15);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1;
x_15 = lean_array_get(x_14, x_13, x_2);
lean_inc(x_5);
x_16 = l_Lean_Elab_FixedParamPerm_buildArgs___rarg(x_15, x_3, x_5);
x_17 = l_Lean_Expr_beta(x_4, x_5);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_16, x_17, x_18, x_19, x_18, x_20, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_5, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_5, x_17);
lean_dec(x_5);
x_19 = lean_array_fget(x_4, x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_2);
lean_inc(x_6);
lean_inc(x_1);
x_22 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11___lambda__1___boxed), 12, 4);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_6);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_21);
x_23 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_24 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_Structural_mkIndPredBRecOn___spec__2___rarg(x_20, x_22, x_23, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_nat_add(x_6, x_17);
lean_dec(x_6);
x_28 = lean_array_push(x_8, x_25);
x_5 = x_18;
x_6 = x_27;
x_7 = lean_box(0);
x_8 = x_28;
x_14 = x_26;
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
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
lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_8);
lean_ctor_set(x_34, 1, x_14);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__12(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 5);
lean_dec(x_13);
lean_ctor_set(x_10, 5, x_11);
x_14 = lean_array_uset(x_7, x_2, x_10);
x_2 = x_9;
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get_uint8(x_10, sizeof(void*)*7);
x_18 = lean_ctor_get(x_10, 1);
x_19 = lean_ctor_get(x_10, 2);
x_20 = lean_ctor_get(x_10, 3);
x_21 = lean_ctor_get(x_10, 4);
x_22 = lean_ctor_get(x_10, 6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_11);
lean_ctor_set(x_23, 6, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*7, x_17);
x_24 = lean_array_uset(x_7, x_2, x_23);
x_2 = x_9;
x_3 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_6);
x_9 = l_Lean_MessageData_ofFormat(x_8);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_9);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_11);
x_14 = l_Lean_MessageData_ofFormat(x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_2 = x_12;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__13___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_7);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = l_Lean_MessageData_ofFormat(x_10);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_11);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_2);
x_15 = lean_apply_1(x_2, x_13);
lean_inc(x_1);
x_16 = lean_apply_1(x_1, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_3 = x_14;
x_4 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__13___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__14___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__15(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__16(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_to_list(x_5);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__13___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__14___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__15(x_7, x_8);
x_10 = l_Lean_MessageData_ofList(x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_10);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = lean_array_to_list(x_12);
x_15 = lean_box(0);
x_16 = l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__13___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__14___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__15(x_14, x_15);
x_17 = l_Lean_MessageData_ofList(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_2);
x_1 = x_13;
x_2 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 5);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_get_size(x_1);
x_18 = lean_mk_empty_array_with_capacity(x_17);
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_20 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__10(x_2, x_1, x_3, x_4, x_1, x_17, x_19, lean_box(0), x_18, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Array_zip___rarg(x_5, x_21);
lean_dec(x_21);
x_24 = lean_array_get_size(x_23);
x_25 = lean_mk_empty_array_with_capacity(x_24);
x_26 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11(x_6, x_7, x_23, x_23, x_24, x_19, lean_box(0), x_25, x_11, x_12, x_13, x_14, x_15, x_22);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Array_zip___rarg(x_8, x_28);
lean_dec(x_28);
x_30 = lean_array_size(x_29);
x_31 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__12(x_30, x_9, x_29);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = l_Array_zip___rarg(x_8, x_32);
lean_dec(x_32);
x_35 = lean_array_size(x_34);
x_36 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__12(x_35, x_9, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FArgs: ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; 
x_19 = l_Array_zip___rarg(x_1, x_2);
x_20 = l_Array_zip___rarg(x_3, x_19);
lean_dec(x_19);
x_21 = lean_array_size(x_20);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_4);
x_22 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__9(x_3, x_4, x_21, x_5, x_20, x_13, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
x_25 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_6, x_13, x_14, x_15, x_16, x_17, x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__2(x_7, x_4, x_8, x_23, x_1, x_9, x_10, x_11, x_5, x_29, x_13, x_14, x_15, x_16, x_17, x_28);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_25);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_32 = lean_ctor_get(x_25, 1);
x_33 = lean_ctor_get(x_25, 0);
lean_dec(x_33);
lean_inc(x_23);
x_34 = lean_array_to_list(x_23);
x_35 = lean_box(0);
x_36 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_34, x_35);
x_37 = l_Lean_MessageData_ofList(x_36);
x_38 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__2;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_37);
lean_ctor_set(x_25, 0, x_38);
x_39 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_6, x_40, x_13, x_14, x_15, x_16, x_17, x_32);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__2(x_7, x_4, x_8, x_23, x_1, x_9, x_10, x_11, x_5, x_42, x_13, x_14, x_15, x_16, x_17, x_43);
lean_dec(x_42);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
lean_inc(x_23);
x_46 = lean_array_to_list(x_23);
x_47 = lean_box(0);
x_48 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_46, x_47);
x_49 = l_Lean_MessageData_ofList(x_48);
x_50 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__2;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_6, x_53, x_13, x_14, x_15, x_16, x_17, x_45);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__2(x_7, x_4, x_8, x_23, x_1, x_9, x_10, x_11, x_5, x_55, x_13, x_14, x_15, x_16, x_17, x_56);
lean_dec(x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
return x_22;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_22, 0);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_22);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FTypes: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_18 = l_Lean_Elab_Structural_mkBRecOnConst(x_1, x_2, x_3, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_19);
lean_inc(x_2);
x_21 = l_Lean_Elab_Structural_inferBRecOnFTypes(x_1, x_2, x_19, x_13, x_14, x_15, x_16, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_4);
x_24 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_4, x_12, x_13, x_14, x_15, x_16, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3(x_5, x_22, x_1, x_2, x_6, x_4, x_7, x_19, x_8, x_9, x_10, x_28, x_12, x_13, x_14, x_15, x_16, x_27);
lean_dec(x_22);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
lean_inc(x_22);
x_33 = lean_array_to_list(x_22);
x_34 = lean_box(0);
x_35 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_33, x_34);
x_36 = l_Lean_MessageData_ofList(x_35);
x_37 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__2;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_36);
lean_ctor_set(x_24, 0, x_37);
x_38 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_4);
x_40 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_4, x_39, x_12, x_13, x_14, x_15, x_16, x_31);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3(x_5, x_22, x_1, x_2, x_6, x_4, x_7, x_19, x_8, x_9, x_10, x_41, x_12, x_13, x_14, x_15, x_16, x_42);
lean_dec(x_41);
lean_dec(x_22);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_ctor_get(x_24, 1);
lean_inc(x_44);
lean_dec(x_24);
lean_inc(x_22);
x_45 = lean_array_to_list(x_22);
x_46 = lean_box(0);
x_47 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_45, x_46);
x_48 = l_Lean_MessageData_ofList(x_47);
x_49 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__2;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_inc(x_4);
x_53 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_4, x_52, x_12, x_13, x_14, x_15, x_16, x_44);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3(x_5, x_22, x_1, x_2, x_6, x_4, x_7, x_19, x_8, x_9, x_10, x_54, x_12, x_13, x_14, x_15, x_16, x_55);
lean_dec(x_54);
lean_dec(x_22);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_21);
if (x_57 == 0)
{
return x_21;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_21, 0);
x_59 = lean_ctor_get(x_21, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_21);
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
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_18);
if (x_61 == 0)
{
return x_18;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_18, 0);
x_63 = lean_ctor_get(x_18, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_18);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("motives: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = l_Array_zip___rarg(x_1, x_2);
x_16 = lean_array_size(x_15);
x_17 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_15);
x_18 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__8(x_16, x_17, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_3);
x_21 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_3, x_9, x_10, x_11, x_12, x_13, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4(x_1, x_4, x_19, x_3, x_2, x_17, x_15, x_5, x_6, x_7, x_25, x_9, x_10, x_11, x_12, x_13, x_24);
lean_dec(x_15);
lean_dec(x_19);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_21, 1);
x_29 = lean_ctor_get(x_21, 0);
lean_dec(x_29);
lean_inc(x_19);
x_30 = lean_array_to_list(x_19);
x_31 = lean_box(0);
x_32 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_30, x_31);
x_33 = l_Lean_MessageData_ofList(x_32);
x_34 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__2;
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_33);
lean_ctor_set(x_21, 0, x_34);
x_35 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_21);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_3);
x_37 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_3, x_36, x_9, x_10, x_11, x_12, x_13, x_28);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4(x_1, x_4, x_19, x_3, x_2, x_17, x_15, x_5, x_6, x_7, x_38, x_9, x_10, x_11, x_12, x_13, x_39);
lean_dec(x_38);
lean_dec(x_15);
lean_dec(x_19);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_dec(x_21);
lean_inc(x_19);
x_42 = lean_array_to_list(x_19);
x_43 = lean_box(0);
x_44 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_42, x_43);
x_45 = l_Lean_MessageData_ofList(x_44);
x_46 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__2;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_3);
x_50 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_3, x_49, x_9, x_10, x_11, x_12, x_13, x_41);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4(x_1, x_4, x_19, x_3, x_2, x_17, x_15, x_5, x_6, x_7, x_51, x_9, x_10, x_11, x_12, x_13, x_52);
lean_dec(x_51);
lean_dec(x_15);
lean_dec(x_19);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_18);
if (x_54 == 0)
{
return x_18;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_18, 0);
x_56 = lean_ctor_get(x_18, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_18);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structural", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__3;
x_3 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assignments of type formers of ", 31, 31);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" to functions: ", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_15 = l_Lean_InductiveVal_numTypeFormers(x_1);
x_16 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___closed__1;
x_17 = l_Array_ofFn___rarg(x_15, x_16);
lean_dec(x_15);
x_18 = l_Lean_Elab_Structural_instInhabitedRecArgInfo;
x_19 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__1;
x_20 = l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4(x_18, x_19, x_2, x_17);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__5;
x_22 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_21, x_9, x_10, x_11, x_12, x_13, x_14);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5(x_2, x_3, x_21, x_20, x_4, x_5, x_6, x_26, x_9, x_10, x_11, x_12, x_13, x_25);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_22);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_29 = lean_ctor_get(x_22, 1);
x_30 = lean_ctor_get(x_22, 0);
lean_dec(x_30);
x_31 = l_Lean_MessageData_ofName(x_7);
x_32 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__7;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_31);
lean_ctor_set(x_22, 0, x_32);
x_33 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__9;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_22);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_20);
x_35 = lean_array_to_list(x_20);
x_36 = lean_box(0);
x_37 = l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__16(x_35, x_36);
x_38 = l_Lean_MessageData_ofList(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_21, x_41, x_9, x_10, x_11, x_12, x_13, x_29);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5(x_2, x_3, x_21, x_20, x_4, x_5, x_6, x_43, x_9, x_10, x_11, x_12, x_13, x_44);
lean_dec(x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_46 = lean_ctor_get(x_22, 1);
lean_inc(x_46);
lean_dec(x_22);
x_47 = l_Lean_MessageData_ofName(x_7);
x_48 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__7;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__9;
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_20);
x_52 = lean_array_to_list(x_20);
x_53 = lean_box(0);
x_54 = l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__16(x_52, x_53);
x_55 = l_Lean_MessageData_ofList(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_21, x_58, x_9, x_10, x_11, x_12, x_13, x_46);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5(x_2, x_3, x_21, x_20, x_4, x_5, x_6, x_60, x_9, x_10, x_11, x_12, x_13, x_61);
lean_dec(x_60);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 1);
x_13 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1;
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get(x_13, x_12, x_14);
lean_inc(x_4);
x_16 = l_Lean_Elab_FixedParamPerm_buildArgs___rarg(x_15, x_2, x_4);
x_17 = l_Lean_mkAppN(x_3, x_4);
lean_dec(x_4);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_16, x_17, x_18, x_19, x_19, x_20, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_Meta_check(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 5);
lean_dec(x_14);
lean_ctor_set(x_2, 5, x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_mk(x_16);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 2);
x_22 = lean_ctor_get(x_2, 3);
x_23 = lean_ctor_get(x_2, 4);
x_24 = lean_ctor_get(x_2, 6);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_25, 0, x_18);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_21);
lean_ctor_set(x_25, 3, x_22);
lean_ctor_set(x_25, 4, x_23);
lean_ctor_set(x_25, 5, x_1);
lean_ctor_set(x_25, 6, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*7, x_19);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_dec(x_10);
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_2, 3);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 4);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 6);
lean_inc(x_36);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 lean_ctor_release(x_2, 3);
 lean_ctor_release(x_2, 4);
 lean_ctor_release(x_2, 5);
 lean_ctor_release(x_2, 6);
 x_37 = x_2;
} else {
 lean_dec_ref(x_2);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 7, 1);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_32);
lean_ctor_set(x_38, 2, x_33);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_35);
lean_ctor_set(x_38, 5, x_1);
lean_ctor_set(x_38, 6, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*7, x_31);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_array_mk(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_29);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_10);
if (x_43 == 0)
{
return x_10;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = lean_ctor_get(x_10, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_10);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nonrecursive value:", 19, 19);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Lean_Elab_instInhabitedPreDefinition;
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get(x_14, x_1, x_15);
x_17 = l_Lean_instInhabitedExpr;
x_18 = lean_array_get(x_17, x_2, x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_18);
x_19 = l_Lean_Elab_Structural_mkIndPredBRecOn(x_3, x_18, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__7___boxed), 11, 3);
lean_closure_set(x_22, 0, x_4);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_20);
x_23 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_Structural_mkIndPredBRecOn___spec__2___rarg(x_18, x_22, x_23, x_8, x_9, x_10, x_11, x_12, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_6);
x_27 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_6, x_8, x_9, x_10, x_11, x_12, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_box(0);
x_32 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__8(x_25, x_16, x_31, x_8, x_9, x_10, x_11, x_12, x_30);
lean_dec(x_8);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_27, 1);
x_35 = lean_ctor_get(x_27, 0);
lean_dec(x_35);
lean_inc(x_25);
x_36 = l_Lean_indentExpr(x_25);
x_37 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__2;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_37);
x_38 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_6, x_39, x_8, x_9, x_10, x_11, x_12, x_34);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__8(x_25, x_16, x_41, x_8, x_9, x_10, x_11, x_12, x_42);
lean_dec(x_8);
lean_dec(x_41);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_dec(x_27);
lean_inc(x_25);
x_45 = l_Lean_indentExpr(x_25);
x_46 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__2;
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_6, x_49, x_8, x_9, x_10, x_11, x_12, x_44);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__8(x_25, x_16, x_51, x_8, x_9, x_10, x_11, x_12, x_52);
lean_dec(x_8);
lean_dec(x_51);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_54 = !lean_is_exclusive(x_24);
if (x_54 == 0)
{
return x_24;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_24, 0);
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_24);
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
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_19);
if (x_58 == 0)
{
return x_19;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_19, 0);
x_60 = lean_ctor_get(x_19, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_19);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Using mkIndPred construction", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__5;
x_14 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_13, x_7, x_8, x_9, x_10, x_11, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9(x_1, x_2, x_3, x_4, x_5, x_13, x_18, x_7, x_8, x_9, x_10, x_11, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__2;
x_22 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_13, x_21, x_7, x_8, x_9, x_10, x_11, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9(x_1, x_2, x_3, x_4, x_5, x_13, x_23, x_7, x_8, x_9, x_10, x_11, x_24);
lean_dec(x_23);
return x_25;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structural mutual recursion over inductive predicates is not supported", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_11);
lean_inc(x_3);
x_14 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1(x_1, x_2, x_3, x_1, x_11, x_13, lean_box(0), x_12, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Structural_instInhabitedRecArgInfo;
x_18 = lean_array_get(x_17, x_4, x_13);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_instInhabitedName;
x_23 = lean_array_get(x_22, x_21, x_13);
lean_dec(x_21);
x_24 = l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2(x_23, x_5, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_28);
x_29 = l_Lean_Meta_isInductivePredicate(x_28, x_6, x_7, x_8, x_9, x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_18);
lean_dec(x_11);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_box(0);
x_34 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6(x_25, x_4, x_15, x_2, x_3, x_1, x_28, x_33, x_5, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_15);
lean_dec(x_25);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_4);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_dec_eq(x_11, x_36);
lean_dec(x_11);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_38 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2;
x_39 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__19(x_38, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(0);
x_45 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10(x_1, x_15, x_18, x_2, x_3, x_44, x_5, x_6, x_7, x_8, x_9, x_35);
lean_dec(x_15);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_29);
if (x_46 == 0)
{
return x_29;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_29, 0);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_29);
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
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_24);
if (x_50 == 0)
{
return x_24;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_24, 0);
x_52 = lean_ctor_get(x_24, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_24);
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
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_14);
if (x_54 == 0)
{
return x_14;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_14, 0);
x_56 = lean_ctor_get(x_14, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_14);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__5(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__8(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__9(x_1, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__12(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; lean_object* x_18; 
x_17 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_18 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___boxed(lean_object** _args) {
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
size_t x_19; lean_object* x_20; 
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3(x_1, x_2, x_3, x_4, x_19, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___boxed(lean_object** _args) {
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
size_t x_18; lean_object* x_19; 
x_18 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4(x_1, x_2, x_3, x_4, x_5, x_18, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 3);
lean_inc(x_8);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
x_19 = lean_ctor_get(x_13, 2);
x_20 = lean_ctor_get(x_13, 3);
x_21 = lean_ctor_get(x_13, 4);
x_22 = lean_ctor_get(x_13, 5);
x_23 = lean_ctor_get(x_13, 6);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_24 = l_Lean_Elab_Structural_preprocess(x_22, x_1, x_8, x_9, x_10);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_ctor_set(x_13, 5, x_25);
x_27 = 1;
x_28 = lean_usize_add(x_3, x_27);
x_29 = lean_array_uset(x_15, x_3, x_13);
x_3 = x_28;
x_4 = x_29;
x_10 = x_26;
goto _start;
}
else
{
uint8_t x_31; 
lean_free_object(x_13);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get_uint8(x_13, sizeof(void*)*7);
x_37 = lean_ctor_get(x_13, 1);
x_38 = lean_ctor_get(x_13, 2);
x_39 = lean_ctor_get(x_13, 3);
x_40 = lean_ctor_get(x_13, 4);
x_41 = lean_ctor_get(x_13, 5);
x_42 = lean_ctor_get(x_13, 6);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_35);
lean_dec(x_13);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_43 = l_Lean_Elab_Structural_preprocess(x_41, x_1, x_8, x_9, x_10);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_46, 0, x_35);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 2, x_38);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_40);
lean_ctor_set(x_46, 5, x_44);
lean_ctor_set(x_46, 6, x_42);
lean_ctor_set_uint8(x_46, sizeof(void*)*7, x_36);
x_47 = 1;
x_48 = lean_usize_add(x_3, x_47);
x_49 = lean_array_uset(x_15, x_3, x_46);
x_3 = x_48;
x_4 = x_49;
x_10 = x_45;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_51 = lean_ctor_get(x_43, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_53 = x_43;
} else {
 lean_dec_ref(x_43);
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
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_eq(x_6, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_6, x_18);
lean_dec(x_6);
x_20 = lean_array_fget(x_5, x_7);
lean_inc(x_2);
x_21 = lean_array_get(x_2, x_3, x_7);
x_22 = lean_ctor_get(x_20, 5);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
x_23 = l_Lean_Elab_FixedParamPerm_instantiateLambda(x_21, x_22, x_4, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_nat_add(x_7, x_18);
lean_dec(x_7);
x_27 = lean_array_push(x_9, x_24);
x_6 = x_19;
x_7 = x_26;
x_8 = lean_box(0);
x_9 = x_27;
x_15 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_9);
lean_ctor_set(x_33, 1, x_15);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = lean_ctor_get(x_5, 2);
lean_inc(x_8);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_8 = l_Lean_Elab_Structural_RecArgInfo_indicesAndRecArgPos(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_5, x_11);
lean_dec(x_5);
x_13 = lean_array_fget(x_4, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_13, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_17 = lean_array_get(x_1, x_16, x_6);
lean_ctor_set(x_13, 1, x_17);
x_18 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_19 = lean_array_push(x_8, x_13);
x_5 = x_12;
x_6 = x_18;
x_7 = lean_box(0);
x_8 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 2);
x_23 = lean_ctor_get(x_13, 3);
x_24 = lean_ctor_get(x_13, 4);
x_25 = lean_ctor_get(x_13, 5);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
x_27 = lean_array_get(x_1, x_26, x_6);
x_28 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_22);
lean_ctor_set(x_28, 3, x_23);
lean_ctor_set(x_28, 4, x_24);
lean_ctor_set(x_28, 5, x_25);
x_29 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
x_30 = lean_array_push(x_8, x_28);
x_5 = x_12;
x_6 = x_29;
x_7 = lean_box(0);
x_8 = x_30;
goto _start;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_apply_1(x_3, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp___rarg(x_1, x_2, x_10, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = l_Array_contains___at___private_Lean_Class_0__Lean_checkOutParam___spec__1(x_1, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = l_Array_contains___at___private_Lean_Class_0__Lean_checkOutParam___spec__1(x_1, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = l_Array_contains___at___private_Lean_Class_0__Lean_checkOutParam___spec__1(x_1, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
x_10 = l_Lean_Meta_getLocalInstances(x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
x_16 = lean_array_get_size(x_11);
x_17 = lean_nat_dec_lt(x_14, x_16);
if (x_15 == 0)
{
lean_dec(x_13);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_11);
x_18 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_19 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(x_9, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_16, x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_11);
x_21 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_22 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(x_9, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = 0;
x_24 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_25 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_26 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__9(x_1, x_11, x_23, x_24, x_25);
lean_dec(x_11);
x_27 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(x_9, x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_13, x_13);
if (x_28 == 0)
{
lean_dec(x_13);
if (x_17 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_16);
lean_dec(x_11);
x_29 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_30 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(x_9, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_16, x_16);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_16);
lean_dec(x_11);
x_32 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_33 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(x_9, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_33;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_36 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_37 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__10(x_1, x_11, x_34, x_35, x_36);
lean_dec(x_11);
x_38 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(x_9, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_38;
}
}
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_withErasedFVars___spec__3(x_1, x_39, x_40, x_9);
if (x_17 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_16);
lean_dec(x_11);
x_42 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_43 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(x_41, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_16, x_16);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_16);
lean_dec(x_11);
x_45 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_46 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(x_41, x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_46;
}
else
{
size_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_48 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
x_49 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__11(x_1, x_11, x_39, x_47, x_48);
lean_dec(x_11);
x_50 = l_Lean_Meta_withLCtx___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__8___rarg(x_41, x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_50;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__15(x_1, x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_2, x_3);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__18(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__17(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__19(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_name_eq(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__17(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__18(x_1, x_3, x_8, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 0;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__19(x_1, x_11, x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__20(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_name_eq(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__16(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__17(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__20(x_1, x_5, x_10, x_11);
return x_12;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__14(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_name_eq(x_1, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_8, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_MetavarContext_getDecl(x_14, x_8);
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__16(x_1, x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = l_Lean_MetavarContext_getDecl(x_21, x_8);
lean_dec(x_8);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__16(x_1, x_24);
lean_dec(x_24);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_29, x_28);
return x_30;
}
}
case 5:
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Expr_getAppFn(x_2);
x_32 = l_Lean_Expr_isMVar(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
x_33 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__15(x_1, x_2, x_3);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_2);
x_34 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_2, x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Expr_getAppFn(x_35);
x_38 = lean_expr_eqv(x_37, x_31);
lean_dec(x_31);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_2);
x_2 = x_35;
x_3 = x_36;
goto _start;
}
else
{
lean_object* x_40; 
lean_dec(x_35);
x_40 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__15(x_1, x_2, x_36);
return x_40;
}
}
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_41, x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_44);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_42, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_42);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
case 7:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
lean_dec(x_2);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_52, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_53, x_57);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_53);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 3);
lean_inc(x_65);
lean_dec(x_2);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_63, x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_64, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_65, x_73);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_65);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_70, 0);
lean_dec(x_76);
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_dec(x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_65);
lean_dec(x_64);
x_79 = !lean_is_exclusive(x_66);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_66, 0);
lean_dec(x_80);
return x_66;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_66, 1);
lean_inc(x_81);
lean_dec(x_66);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_67);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_dec(x_2);
x_84 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_83, x_3);
return x_84;
}
case 11:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_2, 2);
lean_inc(x_85);
lean_dec(x_2);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_85, x_3);
return x_86;
}
default: 
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__14(x_1, x_2, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__23(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__23(x_1, x_4, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_unbox(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_6, 0);
lean_dec(x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
x_15 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_2, x_3);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__26(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__25(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
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
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__27(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_name_eq(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__25(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
x_7 = 0;
return x_7;
}
else
{
size_t x_8; size_t x_9; uint8_t x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__26(x_1, x_3, x_8, x_9);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 0;
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__27(x_1, x_11, x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__28(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_name_eq(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
size_t x_13; size_t x_14; 
x_13 = 1;
x_14 = lean_usize_add(x_3, x_13);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
x_16 = 1;
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__24(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__25(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 0;
return x_9;
}
else
{
size_t x_10; size_t x_11; uint8_t x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__28(x_1, x_5, x_10, x_11);
return x_12;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_name_eq(x_1, x_4);
lean_dec(x_4);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_getExprMVarAssignment_x3f___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__1(x_8, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = l_Lean_MetavarContext_getDecl(x_14, x_8);
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__24(x_1, x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = l_Lean_MetavarContext_getDecl(x_21, x_8);
lean_dec(x_8);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__24(x_1, x_24);
lean_dec(x_24);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = lean_ctor_get(x_10, 0);
lean_inc(x_29);
lean_dec(x_10);
x_30 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_29, x_28);
return x_30;
}
}
case 5:
{
lean_object* x_31; uint8_t x_32; 
x_31 = l_Lean_Expr_getAppFn(x_2);
x_32 = l_Lean_Expr_isMVar(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_31);
x_33 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__23(x_1, x_2, x_3);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_2);
x_34 = l_Lean_instantiateMVars___at___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___spec__7(x_2, x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Expr_getAppFn(x_35);
x_38 = lean_expr_eqv(x_37, x_31);
lean_dec(x_31);
lean_dec(x_37);
if (x_38 == 0)
{
lean_dec(x_2);
x_2 = x_35;
x_3 = x_36;
goto _start;
}
else
{
lean_object* x_40; 
lean_dec(x_35);
x_40 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__23(x_1, x_2, x_36);
return x_40;
}
}
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 2);
lean_inc(x_42);
lean_dec(x_2);
x_43 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_41, x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_44);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_42, x_46);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_42);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
return x_43;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_dec(x_43);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_44);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
case 7:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
lean_dec(x_2);
x_54 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_52, x_3);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_55);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_53, x_57);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_53);
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_dec(x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 3);
lean_inc(x_65);
lean_dec(x_2);
x_66 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_63, x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_67);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_64, x_69);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_71);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_65, x_73);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_65);
x_75 = !lean_is_exclusive(x_70);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_70, 0);
lean_dec(x_76);
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_70, 1);
lean_inc(x_77);
lean_dec(x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_65);
lean_dec(x_64);
x_79 = !lean_is_exclusive(x_66);
if (x_79 == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_66, 0);
lean_dec(x_80);
return x_66;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_66, 1);
lean_inc(x_81);
lean_dec(x_66);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_67);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 10:
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_2, 1);
lean_inc(x_83);
lean_dec(x_2);
x_84 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_83, x_3);
return x_84;
}
case 11:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_2, 2);
lean_inc(x_85);
lean_dec(x_2);
x_86 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_85, x_3);
return x_86;
}
default: 
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
x_87 = 0;
x_88 = lean_box(x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_3);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_shouldVisit(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_unbox(x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = 0;
x_10 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = 0;
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__22(x_1, x_2, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__3;
lean_inc(x_13);
lean_ctor_set(x_9, 1, x_13);
lean_ctor_set(x_9, 0, x_14);
x_15 = l_Lean_Expr_hasFVar(x_1);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = l_Lean_Expr_hasMVar(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_1);
x_17 = lean_st_ref_take(x_5, x_12);
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
lean_ctor_set(x_18, 0, x_13);
x_22 = lean_st_ref_set(x_5, x_18, x_19);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_22, 0, x_26);
return x_22;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = 0;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_18, 1);
x_32 = lean_ctor_get(x_18, 2);
x_33 = lean_ctor_get(x_18, 3);
x_34 = lean_ctor_get(x_18, 4);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_18);
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_32);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_34);
x_36 = lean_st_ref_set(x_5, x_35, x_19);
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
x_39 = 0;
x_40 = lean_box(x_39);
if (lean_is_scalar(x_38)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_38;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_13);
x_42 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_2, x_1, x_9);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_st_ref_take(x_5, x_12);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = !lean_is_exclusive(x_47);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
lean_ctor_set(x_47, 0, x_45);
x_51 = lean_st_ref_set(x_5, x_47, x_48);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_44);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_47, 1);
x_57 = lean_ctor_get(x_47, 2);
x_58 = lean_ctor_get(x_47, 3);
x_59 = lean_ctor_get(x_47, 4);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_47);
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_45);
lean_ctor_set(x_60, 1, x_56);
lean_ctor_set(x_60, 2, x_57);
lean_ctor_set(x_60, 3, x_58);
lean_ctor_set(x_60, 4, x_59);
x_61 = lean_st_ref_set(x_5, x_60, x_48);
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
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_44);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_13);
x_65 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_2, x_1, x_9);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_st_ref_take(x_5, x_12);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_70, 0);
lean_dec(x_73);
lean_ctor_set(x_70, 0, x_68);
x_74 = lean_st_ref_set(x_5, x_70, x_71);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_67);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_70, 1);
x_80 = lean_ctor_get(x_70, 2);
x_81 = lean_ctor_get(x_70, 3);
x_82 = lean_ctor_get(x_70, 4);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_70);
x_83 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_83, 0, x_68);
lean_ctor_set(x_83, 1, x_79);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set(x_83, 3, x_81);
lean_ctor_set(x_83, 4, x_82);
x_84 = lean_st_ref_set(x_5, x_83, x_71);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_86 = x_84;
} else {
 lean_dec_ref(x_84);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_67);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_9, 0);
x_89 = lean_ctor_get(x_9, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_9);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__3;
lean_inc(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
x_93 = l_Lean_Expr_hasFVar(x_1);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = l_Lean_Expr_hasMVar(x_1);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_92);
lean_dec(x_1);
x_95 = lean_st_ref_take(x_5, x_89);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 3);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 4);
lean_inc(x_101);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 lean_ctor_release(x_96, 2);
 lean_ctor_release(x_96, 3);
 lean_ctor_release(x_96, 4);
 x_102 = x_96;
} else {
 lean_dec_ref(x_96);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 5, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_90);
lean_ctor_set(x_103, 1, x_98);
lean_ctor_set(x_103, 2, x_99);
lean_ctor_set(x_103, 3, x_100);
lean_ctor_set(x_103, 4, x_101);
x_104 = lean_st_ref_set(x_5, x_103, x_97);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
x_107 = 0;
x_108 = lean_box(x_107);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_90);
x_110 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_2, x_1, x_92);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_st_ref_take(x_5, x_89);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 2);
lean_inc(x_118);
x_119 = lean_ctor_get(x_115, 3);
lean_inc(x_119);
x_120 = lean_ctor_get(x_115, 4);
lean_inc(x_120);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 lean_ctor_release(x_115, 2);
 lean_ctor_release(x_115, 3);
 lean_ctor_release(x_115, 4);
 x_121 = x_115;
} else {
 lean_dec_ref(x_115);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(0, 5, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_113);
lean_ctor_set(x_122, 1, x_117);
lean_ctor_set(x_122, 2, x_118);
lean_ctor_set(x_122, 3, x_119);
lean_ctor_set(x_122, 4, x_120);
x_123 = lean_st_ref_set(x_5, x_122, x_116);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_112);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_90);
x_127 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_2, x_1, x_92);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_st_ref_take(x_5, x_89);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_132, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_132, 3);
lean_inc(x_136);
x_137 = lean_ctor_get(x_132, 4);
lean_inc(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 lean_ctor_release(x_132, 2);
 lean_ctor_release(x_132, 3);
 lean_ctor_release(x_132, 4);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 5, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_130);
lean_ctor_set(x_139, 1, x_134);
lean_ctor_set(x_139, 2, x_135);
lean_ctor_set(x_139, 3, x_136);
lean_ctor_set(x_139, 4, x_137);
x_140 = lean_st_ref_set(x_5, x_139, x_133);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_142 = x_140;
} else {
 lean_dec_ref(x_140);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_129);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__29(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_tag(x_9, 1);
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
lean_inc(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("its type is an inductive datatype and the datatype parameter", 60, 60);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ndepends on the function parameter", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nwhich cannot be fixed as it is an index or depends on an index, and indices cannot be fixed parameters when using structural recursion.", 136, 136);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_6, x_5);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_7);
x_16 = lean_array_uget(x_4, x_6);
lean_inc(x_2);
x_24 = l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12(x_2, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__1;
x_17 = x_28;
x_18 = x_27;
goto block_23;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_24);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_24, 1);
x_31 = lean_ctor_get(x_24, 0);
lean_dec(x_31);
x_32 = l_Lean_Expr_isFVarOf(x_2, x_16);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_33 = l_Lean_indentExpr(x_2);
x_34 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__3;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_33);
lean_ctor_set(x_24, 0, x_34);
x_35 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__5;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Expr_fvar___override(x_16);
x_38 = l_Lean_indentExpr(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__7;
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__29(x_41, x_8, x_9, x_10, x_11, x_12, x_30);
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
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_16);
x_47 = l_Lean_indentExpr(x_2);
x_48 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__3;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_47);
lean_ctor_set(x_24, 0, x_48);
x_49 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__7;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_24);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__29(x_50, x_8, x_9, x_10, x_11, x_12, x_30);
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
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_24, 1);
lean_inc(x_56);
lean_dec(x_24);
x_57 = l_Lean_Expr_isFVarOf(x_2, x_16);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_58 = l_Lean_indentExpr(x_2);
x_59 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__3;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__5;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Expr_fvar___override(x_16);
x_64 = l_Lean_indentExpr(x_63);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__7;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__29(x_67, x_8, x_9, x_10, x_11, x_12, x_56);
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
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_16);
x_73 = l_Lean_indentExpr(x_2);
x_74 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__3;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__7;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__29(x_77, x_8, x_9, x_10, x_11, x_12, x_56);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
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
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 1;
x_21 = lean_usize_add(x_6, x_20);
x_6 = x_21;
x_7 = x_19;
x_13 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__31(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_17 = lean_array_uget(x_5, x_7);
x_18 = lean_box(0);
x_19 = lean_array_size(x_2);
x_20 = lean_box(0);
x_21 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30(x_2, x_17, x_18, x_2, x_19, x_1, x_20, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; size_t x_23; size_t x_24; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_7, x_23);
x_7 = x_24;
x_8 = x_20;
x_14 = x_22;
goto _start;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__32(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_7, x_6);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_17 = lean_array_uget(x_5, x_7);
x_18 = lean_box(0);
x_19 = lean_ctor_get(x_17, 4);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_array_size(x_20);
x_22 = lean_box(0);
x_23 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__31(x_1, x_2, x_18, x_20, x_20, x_21, x_1, x_22, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; size_t x_25; size_t x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = 1;
x_26 = lean_usize_add(x_7, x_25);
x_7 = x_26;
x_8 = x_22;
x_14 = x_24;
goto _start;
}
else
{
uint8_t x_28; 
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
}
}
LEAN_EXPORT lean_object* l_repr___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__33(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_PreDefinition_Structural_RecArgInfo_0__Lean_Elab_Structural_reprRecArgInfo____x40_Lean_Elab_PreDefinition_Structural_RecArgInfo___hyg_71_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__35(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Lean_Elab_PreDefinition_Structural_RecArgInfo_0__Lean_Elab_Structural_reprRecArgInfo____x40_Lean_Elab_PreDefinition_Structural_RecArgInfo___hyg_71_(x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Elab_PreDefinition_Structural_RecArgInfo_0__Lean_Elab_Structural_reprRecArgInfo____x40_Lean_Elab_PreDefinition_Structural_RecArgInfo___hyg_71_(x_11, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__34(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l___private_Lean_Elab_PreDefinition_Structural_RecArgInfo_0__Lean_Elab_Structural_reprRecArgInfo____x40_Lean_Elab_PreDefinition_Structural_RecArgInfo___hyg_71_(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Lean_Elab_PreDefinition_Structural_RecArgInfo_0__Lean_Elab_Structural_reprRecArgInfo____x40_Lean_Elab_PreDefinition_Structural_RecArgInfo___hyg_71_(x_8, x_9);
x_11 = l_List_foldl___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__35(x_2, x_10, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__36(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_apply_1(x_1, x_6);
x_9 = l_Lean_MessageData_ofFormat(x_8);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_9);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_1);
x_13 = lean_apply_1(x_1, x_11);
x_14 = l_Lean_MessageData_ofFormat(x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
x_2 = x_12;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__36___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
x_9 = lean_apply_1(x_2, x_7);
lean_inc(x_1);
x_10 = lean_apply_1(x_1, x_9);
x_11 = l_Lean_MessageData_ofFormat(x_10);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_11);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_2);
x_15 = lean_apply_1(x_2, x_13);
lean_inc(x_1);
x_16 = lean_apply_1(x_1, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_3 = x_14;
x_4 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__36___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__37___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__38(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_9);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_MessageData_ofFormat(x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__39___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_3, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_FixedParamPerm_forallTelescope___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_FixedParamPerm_forallTelescope___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__39___lambda__1), 8, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_4);
x_11 = l___private_Lean_Elab_PreDefinition_FixedParams_0__Lean_Elab_FixedParamPerm_forallTelescopeImpl___rarg(x_1, x_2, x_10, x_5, x_6, x_7, x_8, x_9);
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
static lean_object* _init_l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__2;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_st_ref_take(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_9, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__3;
lean_ctor_set(x_9, 4, x_14);
lean_ctor_set(x_9, 0, x_1);
x_15 = lean_st_ref_set(x_6, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_18, 1);
lean_dec(x_21);
x_22 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__4;
lean_ctor_set(x_18, 1, x_22);
x_23 = lean_st_ref_set(x_4, x_18, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_18, 0);
x_31 = lean_ctor_get(x_18, 2);
x_32 = lean_ctor_get(x_18, 3);
x_33 = lean_ctor_get(x_18, 4);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_18);
x_34 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__4;
x_35 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_31);
lean_ctor_set(x_35, 3, x_32);
lean_ctor_set(x_35, 4, x_33);
x_36 = lean_st_ref_set(x_4, x_35, x_19);
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_41 = lean_ctor_get(x_9, 1);
x_42 = lean_ctor_get(x_9, 2);
x_43 = lean_ctor_get(x_9, 3);
x_44 = lean_ctor_get(x_9, 5);
x_45 = lean_ctor_get(x_9, 6);
x_46 = lean_ctor_get(x_9, 7);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_47 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__3;
x_48 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_41);
lean_ctor_set(x_48, 2, x_42);
lean_ctor_set(x_48, 3, x_43);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set(x_48, 5, x_44);
lean_ctor_set(x_48, 6, x_45);
lean_ctor_set(x_48, 7, x_46);
x_49 = lean_st_ref_set(x_6, x_48, x_10);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_st_ref_take(x_4, x_50);
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
x_57 = lean_ctor_get(x_52, 4);
lean_inc(x_57);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 lean_ctor_release(x_52, 2);
 lean_ctor_release(x_52, 3);
 lean_ctor_release(x_52, 4);
 x_58 = x_52;
} else {
 lean_dec_ref(x_52);
 x_58 = lean_box(0);
}
x_59 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__4;
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 5, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_55);
lean_ctor_set(x_60, 3, x_56);
lean_ctor_set(x_60, 4, x_57);
x_61 = lean_st_ref_set(x_4, x_60, x_53);
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
x_64 = lean_box(0);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__40(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41(x_1, x_3, x_4, x_5, x_6, x_7, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_apply_6(x_2, x_3, x_4, x_5, x_6, x_7, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41(x_12, x_3, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41(x_12, x_3, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 0, x_23);
return x_25;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__42(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_2);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Elab_addAsAxiom(x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_14;
x_10 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_9);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___boxed), 10, 4);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__1___boxed), 9, 2);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_5);
x_16 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__8___rarg), 8, 2);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Meta_withErasedFVars___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__7(x_6, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(0);
x_13 = lean_array_size(x_1);
x_14 = lean_box(0);
x_15 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__32(x_2, x_3, x_1, x_12, x_1, x_13, x_2, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_7(x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("New recArgInfos ", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__4;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__6;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__7;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[]", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__12;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__13;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__14;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__15;
x_2 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_13 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_1, x_7, x_8, x_9, x_10, x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3(x_2, x_3, x_4, x_5, x_17, x_7, x_8, x_9, x_10, x_11, x_16);
lean_dec(x_2);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
x_22 = lean_array_get_size(x_2);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_inc(x_2);
x_25 = lean_array_to_list(x_2);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__5;
x_27 = l_Std_Format_joinSep___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__34(x_25, x_26);
x_28 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__9;
lean_ctor_set_tag(x_13, 5);
lean_ctor_set(x_13, 1, x_27);
lean_ctor_set(x_13, 0, x_28);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__11;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_13);
lean_ctor_set(x_30, 1, x_29);
x_31 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__8;
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = 1;
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_1, x_39, x_7, x_8, x_9, x_10, x_11, x_20);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3(x_2, x_3, x_4, x_5, x_41, x_7, x_8, x_9, x_10, x_11, x_42);
lean_dec(x_41);
lean_dec(x_2);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_13);
x_44 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__16;
x_45 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_1, x_44, x_7, x_8, x_9, x_10, x_11, x_20);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3(x_2, x_3, x_4, x_5, x_46, x_7, x_8, x_9, x_10, x_11, x_47);
lean_dec(x_46);
lean_dec(x_2);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_13, 1);
lean_inc(x_49);
lean_dec(x_13);
x_50 = lean_array_get_size(x_2);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_50, x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_inc(x_2);
x_53 = lean_array_to_list(x_2);
x_54 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__5;
x_55 = l_Std_Format_joinSep___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__34(x_53, x_54);
x_56 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__9;
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__11;
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__8;
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = 1;
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = l_Lean_MessageData_ofFormat(x_63);
x_65 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__2;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_1, x_68, x_7, x_8, x_9, x_10, x_11, x_49);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3(x_2, x_3, x_4, x_5, x_70, x_7, x_8, x_9, x_10, x_11, x_71);
lean_dec(x_70);
lean_dec(x_2);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__16;
x_74 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_1, x_73, x_7, x_8, x_9, x_10, x_11, x_49);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3(x_2, x_3, x_4, x_5, x_75, x_7, x_8, x_9, x_10, x_11, x_76);
lean_dec(x_75);
lean_dec(x_2);
return x_77;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Reduced fixed params from ", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" to ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", erasing ", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_3);
x_17 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__5(x_1, x_2, x_3);
lean_inc(x_5);
x_18 = l_Lean_Elab_FixedParamPerms_erase(x_4, x_5, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 1);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
x_25 = lean_array_get_size(x_3);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__6(x_6, x_3, x_22, x_3, x_25, x_27, lean_box(0), x_26);
lean_dec(x_3);
lean_inc(x_24);
lean_inc(x_8);
lean_inc(x_28);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_7);
x_29 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2___boxed), 13, 6);
lean_closure_set(x_29, 0, x_7);
lean_closure_set(x_29, 1, x_22);
lean_closure_set(x_29, 2, x_23);
lean_closure_set(x_29, 3, x_28);
lean_closure_set(x_29, 4, x_8);
lean_closure_set(x_29, 5, x_24);
x_30 = lean_array_get_size(x_23);
x_31 = lean_array_get_size(x_5);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_9);
x_33 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_9, x_11, x_12, x_13, x_14, x_15, x_16);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_20);
lean_dec(x_23);
lean_free_object(x_18);
lean_dec(x_5);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
x_38 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(x_9, x_28, x_2, x_24, x_29, x_37, x_11, x_12, x_13, x_14, x_15, x_36);
lean_dec(x_24);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_33);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_40 = lean_ctor_get(x_33, 1);
x_41 = lean_ctor_get(x_33, 0);
lean_dec(x_41);
x_42 = lean_array_to_list(x_5);
x_43 = lean_box(0);
x_44 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_42, x_43);
x_45 = l_Lean_MessageData_ofList(x_44);
x_46 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__2;
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_45);
lean_ctor_set(x_33, 0, x_46);
x_47 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__4;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_47);
lean_ctor_set(x_20, 0, x_33);
x_48 = lean_array_to_list(x_23);
x_49 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_48, x_43);
x_50 = l_Lean_MessageData_ofList(x_49);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_50);
lean_ctor_set(x_18, 0, x_20);
x_51 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__6;
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_18);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_array_size(x_24);
lean_inc(x_24);
x_54 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_53, x_2, x_24);
x_55 = lean_array_to_list(x_54);
x_56 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_55, x_43);
x_57 = l_Lean_MessageData_ofList(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
x_59 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_9);
x_61 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_9, x_60, x_11, x_12, x_13, x_14, x_15, x_40);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(x_9, x_28, x_2, x_24, x_29, x_62, x_11, x_12, x_13, x_14, x_15, x_63);
lean_dec(x_62);
lean_dec(x_24);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; size_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_65 = lean_ctor_get(x_33, 1);
lean_inc(x_65);
lean_dec(x_33);
x_66 = lean_array_to_list(x_5);
x_67 = lean_box(0);
x_68 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_66, x_67);
x_69 = l_Lean_MessageData_ofList(x_68);
x_70 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__2;
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__4;
lean_ctor_set_tag(x_20, 7);
lean_ctor_set(x_20, 1, x_72);
lean_ctor_set(x_20, 0, x_71);
x_73 = lean_array_to_list(x_23);
x_74 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_73, x_67);
x_75 = l_Lean_MessageData_ofList(x_74);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_75);
lean_ctor_set(x_18, 0, x_20);
x_76 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__6;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_18);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_size(x_24);
lean_inc(x_24);
x_79 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_78, x_2, x_24);
x_80 = lean_array_to_list(x_79);
x_81 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_80, x_67);
x_82 = l_Lean_MessageData_ofList(x_81);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_82);
x_84 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_inc(x_9);
x_86 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_9, x_85, x_11, x_12, x_13, x_14, x_15, x_65);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(x_9, x_28, x_2, x_24, x_29, x_87, x_11, x_12, x_13, x_14, x_15, x_88);
lean_dec(x_87);
lean_dec(x_24);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_29);
lean_free_object(x_20);
lean_free_object(x_18);
lean_dec(x_9);
lean_dec(x_5);
x_90 = lean_box(0);
x_91 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2(x_7, x_22, x_23, x_28, x_8, x_24, x_90, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_24);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_92 = lean_ctor_get(x_18, 0);
x_93 = lean_ctor_get(x_20, 0);
x_94 = lean_ctor_get(x_20, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_20);
x_95 = lean_array_get_size(x_3);
x_96 = lean_mk_empty_array_with_capacity(x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__6(x_6, x_3, x_92, x_3, x_95, x_97, lean_box(0), x_96);
lean_dec(x_3);
lean_inc(x_94);
lean_inc(x_8);
lean_inc(x_98);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_7);
x_99 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2___boxed), 13, 6);
lean_closure_set(x_99, 0, x_7);
lean_closure_set(x_99, 1, x_92);
lean_closure_set(x_99, 2, x_93);
lean_closure_set(x_99, 3, x_98);
lean_closure_set(x_99, 4, x_8);
lean_closure_set(x_99, 5, x_94);
x_100 = lean_array_get_size(x_93);
x_101 = lean_array_get_size(x_5);
x_102 = lean_nat_dec_eq(x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
lean_dec(x_92);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_9);
x_103 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_9, x_11, x_12, x_13, x_14, x_15, x_16);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_93);
lean_free_object(x_18);
lean_dec(x_5);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_box(0);
x_108 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(x_9, x_98, x_2, x_94, x_99, x_107, x_11, x_12, x_13, x_14, x_15, x_106);
lean_dec(x_94);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; size_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_110 = x_103;
} else {
 lean_dec_ref(x_103);
 x_110 = lean_box(0);
}
x_111 = lean_array_to_list(x_5);
x_112 = lean_box(0);
x_113 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_111, x_112);
x_114 = l_Lean_MessageData_ofList(x_113);
x_115 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__2;
if (lean_is_scalar(x_110)) {
 x_116 = lean_alloc_ctor(7, 2, 0);
} else {
 x_116 = x_110;
 lean_ctor_set_tag(x_116, 7);
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__4;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_array_to_list(x_93);
x_120 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_119, x_112);
x_121 = l_Lean_MessageData_ofList(x_120);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_121);
lean_ctor_set(x_18, 0, x_118);
x_122 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__6;
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_18);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_size(x_94);
lean_inc(x_94);
x_125 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_124, x_2, x_94);
x_126 = lean_array_to_list(x_125);
x_127 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_126, x_112);
x_128 = l_Lean_MessageData_ofList(x_127);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_128);
x_130 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
lean_inc(x_9);
x_132 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_9, x_131, x_11, x_12, x_13, x_14, x_15, x_109);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(x_9, x_98, x_2, x_94, x_99, x_133, x_11, x_12, x_13, x_14, x_15, x_134);
lean_dec(x_133);
lean_dec(x_94);
return x_135;
}
}
else
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_99);
lean_free_object(x_18);
lean_dec(x_9);
lean_dec(x_5);
x_136 = lean_box(0);
x_137 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2(x_7, x_92, x_93, x_98, x_8, x_94, x_136, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_94);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_138 = lean_ctor_get(x_18, 1);
x_139 = lean_ctor_get(x_18, 0);
lean_inc(x_138);
lean_inc(x_139);
lean_dec(x_18);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_142 = x_138;
} else {
 lean_dec_ref(x_138);
 x_142 = lean_box(0);
}
x_143 = lean_array_get_size(x_3);
x_144 = lean_mk_empty_array_with_capacity(x_143);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__6(x_6, x_3, x_139, x_3, x_143, x_145, lean_box(0), x_144);
lean_dec(x_3);
lean_inc(x_141);
lean_inc(x_8);
lean_inc(x_146);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_7);
x_147 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2___boxed), 13, 6);
lean_closure_set(x_147, 0, x_7);
lean_closure_set(x_147, 1, x_139);
lean_closure_set(x_147, 2, x_140);
lean_closure_set(x_147, 3, x_146);
lean_closure_set(x_147, 4, x_8);
lean_closure_set(x_147, 5, x_141);
x_148 = lean_array_get_size(x_140);
x_149 = lean_array_get_size(x_5);
x_150 = lean_nat_dec_eq(x_148, x_149);
lean_dec(x_149);
lean_dec(x_148);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
lean_dec(x_139);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_9);
x_151 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_9, x_11, x_12, x_13, x_14, x_15, x_16);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_5);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_box(0);
x_156 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(x_9, x_146, x_2, x_141, x_147, x_155, x_11, x_12, x_13, x_14, x_15, x_154);
lean_dec(x_141);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; size_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_157 = lean_ctor_get(x_151, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_158 = x_151;
} else {
 lean_dec_ref(x_151);
 x_158 = lean_box(0);
}
x_159 = lean_array_to_list(x_5);
x_160 = lean_box(0);
x_161 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_159, x_160);
x_162 = l_Lean_MessageData_ofList(x_161);
x_163 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__2;
if (lean_is_scalar(x_158)) {
 x_164 = lean_alloc_ctor(7, 2, 0);
} else {
 x_164 = x_158;
 lean_ctor_set_tag(x_164, 7);
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
x_165 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__4;
if (lean_is_scalar(x_142)) {
 x_166 = lean_alloc_ctor(7, 2, 0);
} else {
 x_166 = x_142;
 lean_ctor_set_tag(x_166, 7);
}
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_array_to_list(x_140);
x_168 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_167, x_160);
x_169 = l_Lean_MessageData_ofList(x_168);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_166);
lean_ctor_set(x_170, 1, x_169);
x_171 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__6;
x_172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_array_size(x_141);
lean_inc(x_141);
x_174 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_173, x_2, x_141);
x_175 = lean_array_to_list(x_174);
x_176 = l_List_mapTR_loop___at_Lean_MessageData_instCoeListExpr___spec__1(x_175, x_160);
x_177 = l_Lean_MessageData_ofList(x_176);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_172);
lean_ctor_set(x_178, 1, x_177);
x_179 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_180 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
lean_inc(x_9);
x_181 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_9, x_180, x_11, x_12, x_13, x_14, x_15, x_157);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(x_9, x_146, x_2, x_141, x_147, x_182, x_11, x_12, x_13, x_14, x_15, x_183);
lean_dec(x_182);
lean_dec(x_141);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_147);
lean_dec(x_142);
lean_dec(x_9);
lean_dec(x_5);
x_185 = lean_box(0);
x_186 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2(x_7, x_139, x_140, x_146, x_8, x_141, x_185, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_141);
return x_186;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Trying argument set ", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_array_size(x_6);
lean_inc(x_6);
x_14 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__4(x_13, x_1, x_6);
x_15 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__5;
x_16 = l_Lean_isTracingEnabledFor___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__2(x_15, x_7, x_8, x_9, x_10, x_11, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5(x_13, x_1, x_6, x_2, x_3, x_4, x_5, x_14, x_15, x_20, x_7, x_8, x_9, x_10, x_11, x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
lean_inc(x_14);
x_25 = lean_array_to_list(x_14);
x_26 = lean_box(0);
x_27 = l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__36___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__37___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__38(x_25, x_26);
x_28 = l_Lean_MessageData_ofList(x_27);
x_29 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__2;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_29);
x_30 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_15, x_31, x_7, x_8, x_9, x_10, x_11, x_23);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5(x_13, x_1, x_6, x_2, x_3, x_4, x_5, x_14, x_15, x_33, x_7, x_8, x_9, x_10, x_11, x_34);
lean_dec(x_33);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_36 = lean_ctor_get(x_16, 1);
lean_inc(x_36);
lean_dec(x_16);
lean_inc(x_14);
x_37 = lean_array_to_list(x_14);
x_38 = lean_box(0);
x_39 = l_List_mapTR_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__36___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__37___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__38(x_37, x_38);
x_40 = l_Lean_MessageData_ofList(x_39);
x_41 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__2;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__3(x_15, x_44, x_7, x_8, x_9, x_10, x_11, x_36);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5(x_13, x_1, x_6, x_2, x_3, x_4, x_5, x_14, x_15, x_46, x_7, x_8, x_9, x_10, x_11, x_47);
lean_dec(x_46);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_array_get_size(x_1);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_2);
x_18 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__3(x_1, x_2, x_3, x_8, x_1, x_15, x_17, lean_box(0), x_16, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box_usize(x_4);
lean_inc(x_8);
lean_inc(x_5);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___boxed), 12, 5);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_8);
lean_closure_set(x_22, 3, x_2);
lean_closure_set(x_22, 4, x_1);
x_23 = l_Lean_Elab_Structural_tryAllArgs___rarg(x_6, x_5, x_8, x_19, x_7, x_22, x_9, x_10, x_11, x_12, x_13, x_20);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
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
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_size(x_1);
x_11 = 0;
lean_inc(x_1);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__1(x_10, x_11, x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_12);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__2(x_12, x_10, x_11, x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_16 = l_Lean_Elab_getFixedParamPerms(x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get(x_20, x_19, x_21);
x_23 = l_Lean_Elab_instInhabitedPreDefinition;
x_24 = lean_array_get(x_23, x_14, x_21);
x_25 = lean_ctor_get(x_24, 4);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8___boxed__const__1;
x_27 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__7___boxed), 14, 7);
lean_closure_set(x_27, 0, x_14);
lean_closure_set(x_27, 1, x_20);
lean_closure_set(x_27, 2, x_19);
lean_closure_set(x_27, 3, x_26);
lean_closure_set(x_27, 4, x_17);
lean_closure_set(x_27, 5, x_12);
lean_closure_set(x_27, 6, x_2);
x_28 = l_Lean_Elab_FixedParamPerm_forallTelescope___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__39(x_22, x_25, x_27, x_4, x_5, x_6, x_7, x_8, x_18);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_13);
if (x_33 == 0)
{
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_13, 0);
x_35 = lean_ctor_get(x_13, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_ReaderT_pure___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__1___rarg___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8___boxed), 9, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
x_13 = lean_st_ref_get(x_7, x_8);
if (x_11 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___closed__1;
x_17 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__8___rarg), 8, 2);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_12);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_Environment_unlockAsync(x_18);
x_20 = l_Lean_withEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__40(x_19, x_17, x_3, x_4, x_5, x_6, x_7, x_15);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_9, x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_1);
x_22 = lean_ctor_get(x_13, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_dec(x_13);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___closed__1;
x_25 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__8___rarg), 8, 2);
lean_closure_set(x_25, 0, x_24);
lean_closure_set(x_25, 1, x_12);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l_Lean_Environment_unlockAsync(x_26);
x_28 = l_Lean_withEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__40(x_27, x_25, x_3, x_4, x_5, x_6, x_7, x_23);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_29 = lean_ctor_get(x_13, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_32 = lean_box(0);
x_33 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed__const__1;
x_34 = lean_box_usize(x_31);
x_35 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__42___boxed), 10, 4);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_33);
lean_closure_set(x_35, 2, x_34);
lean_closure_set(x_35, 3, x_32);
x_36 = lean_alloc_closure((void*)(l_ReaderT_bind___at___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___spec__8___rarg), 8, 2);
lean_closure_set(x_36, 0, x_35);
lean_closure_set(x_36, 1, x_12);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = l_Lean_Environment_unlockAsync(x_37);
x_39 = l_Lean_withEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__40(x_38, x_36, x_3, x_4, x_5, x_6, x_7, x_30);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__9(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__10(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__11(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withErasedFVars___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_withErasedFVars___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__15(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__18___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__18(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__19(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__17___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__17(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__20(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__16___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__16(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__14(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__13(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__23___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitApp___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__23(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__26(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__27(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__25___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyMAux___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__25(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__28___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__28(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__24___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentArray_anyM___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__24(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__22___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visitMain___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__22(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__21(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__29(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__31(x_15, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_18 = l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__32(x_15, x_2, x_3, x_4, x_5, x_16, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__42___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__42(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; lean_object* x_13; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_18 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_19 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5(x_17, x_18, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; lean_object* x_14; 
x_13 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_14 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__7(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_array_get(x_9, x_2, x_1);
x_11 = 0;
x_12 = 1;
x_13 = 1;
x_14 = l_Lean_Meta_mkLambdaFVars(x_2, x_10, x_11, x_12, x_11, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_Structural_reporttermMeasure___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reporttermMeasure___lambda__2___boxed), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_reporttermMeasure___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_reporttermMeasure___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_reporttermMeasure___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Termination", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_reporttermMeasure___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("terminationBy", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Structural_reporttermMeasure___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Structural_reporttermMeasure___closed__2;
x_2 = l_Lean_Elab_Structural_reporttermMeasure___closed__3;
x_3 = l_Lean_Elab_Structural_reporttermMeasure___closed__4;
x_4 = l_Lean_Elab_Structural_reporttermMeasure___closed__5;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Structural_reporttermMeasure___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Try this: ", 10, 10);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 6);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_1, 5);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_reporttermMeasure___lambda__1___boxed), 8, 1);
lean_closure_set(x_14, 0, x_2);
x_15 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_13);
x_16 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg(x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = 1;
x_21 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set_uint8(x_21, sizeof(void*)*2, x_20);
x_22 = l_Lean_Elab_Structural_reporttermMeasure___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_23 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm_doRealize___spec__1___rarg(x_13, x_22, x_15, x_3, x_4, x_5, x_6, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_8, 5);
lean_inc(x_26);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_27 = l_Lean_Elab_TerminationMeasure_delab(x_24, x_26, x_21, x_3, x_4, x_5, x_6, x_25);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_Structural_reporttermMeasure___closed__6;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_32);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_33, 5, x_32);
x_34 = l_Lean_Elab_Structural_reporttermMeasure___closed__7;
x_35 = l_Lean_Meta_Tactic_TryThis_addSuggestion(x_12, x_33, x_32, x_34, x_32, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_12);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
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
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
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
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_16);
if (x_44 == 0)
{
return x_16;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_16, 0);
x_46 = lean_ctor_get(x_16, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_16);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Structural_reporttermMeasure___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_reporttermMeasure___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Structural_reporttermMeasure___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_array_uget(x_3, x_5);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_6, 2);
lean_dec(x_23);
x_24 = lean_ctor_get(x_6, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_6, 0);
lean_dec(x_25);
x_26 = lean_array_fget(x_17, x_18);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_18, x_27);
lean_dec(x_18);
lean_ctor_set(x_6, 1, x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_29 = l_Lean_Elab_Structural_reporttermMeasure(x_26, x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; size_t x_31; size_t x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = 1;
x_32 = lean_usize_add(x_5, x_31);
x_5 = x_32;
x_13 = x_30;
goto _start;
}
else
{
uint8_t x_34; 
lean_dec(x_6);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
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
lean_dec(x_6);
x_38 = lean_array_fget(x_17, x_18);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_18, x_39);
lean_dec(x_18);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_17);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_42 = l_Lean_Elab_Structural_reporttermMeasure(x_38, x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; size_t x_44; size_t x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = 1;
x_45 = lean_usize_add(x_5, x_44);
x_5 = x_45;
x_6 = x_41;
x_13 = x_43;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_41);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_3);
x_12 = l_Lean_Elab_Structural_addSmartUnfoldingDef(x_3, x_1, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_3, 3);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lean_Meta_markAsRecursive(x_14, x_9, x_10, x_13);
lean_dec(x_10);
lean_dec(x_9);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_2);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
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
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_18 = lean_array_uget(x_5, x_7);
x_28 = lean_ctor_get(x_8, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_8, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_lt(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_18);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_8);
x_19 = x_32;
x_20 = x_15;
goto block_27;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; 
x_34 = lean_ctor_get(x_8, 2);
lean_dec(x_34);
x_35 = lean_ctor_get(x_8, 1);
lean_dec(x_35);
x_36 = lean_ctor_get(x_8, 0);
lean_dec(x_36);
x_37 = lean_array_fget(x_28, x_29);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_29, x_38);
lean_dec(x_29);
lean_ctor_set(x_8, 1, x_39);
x_40 = lean_ctor_get_uint8(x_18, sizeof(void*)*7);
x_41 = l_Lean_Elab_DefKind_isTheorem(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_18, 4);
lean_inc(x_42);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_43 = l_Lean_Meta_isProp(x_42, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_47 = l_Lean_Elab_abstractNestedProofs(x_18, x_11, x_12, x_13, x_14, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_array_size(x_3);
lean_inc(x_3);
x_51 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__1(x_50, x_1, x_3);
lean_inc(x_2);
lean_inc(x_37);
lean_inc(x_48);
x_52 = l_Lean_Elab_Structural_registerEqnsInfo(x_48, x_51, x_37, x_2, x_13, x_14, x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_55 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1(x_37, x_8, x_48, x_53, x_9, x_10, x_11, x_12, x_13, x_14, x_54);
lean_dec(x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_19 = x_56;
x_20 = x_57;
goto block_27;
}
else
{
uint8_t x_58; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_62; 
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_62 = !lean_is_exclusive(x_52);
if (x_62 == 0)
{
return x_52;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_52, 0);
x_64 = lean_ctor_get(x_52, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_52);
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
lean_dec(x_8);
lean_dec(x_37);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_66 = !lean_is_exclusive(x_47);
if (x_66 == 0)
{
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_47, 0);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_47);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_43, 1);
lean_inc(x_70);
lean_dec(x_43);
x_71 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_72 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1(x_37, x_8, x_18, x_71, x_9, x_10, x_11, x_12, x_13, x_14, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_19 = x_73;
x_20 = x_74;
goto block_27;
}
else
{
uint8_t x_75; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 0);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_72);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_8);
lean_dec(x_37);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_43);
if (x_79 == 0)
{
return x_43;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_43, 0);
x_81 = lean_ctor_get(x_43, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_43);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_84 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1(x_37, x_8, x_18, x_83, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_19 = x_85;
x_20 = x_86;
goto block_27;
}
else
{
uint8_t x_87; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_87 = !lean_is_exclusive(x_84);
if (x_87 == 0)
{
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_84, 0);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_84);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; 
lean_dec(x_8);
x_91 = lean_array_fget(x_28, x_29);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_29, x_92);
lean_dec(x_29);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_28);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_30);
x_95 = lean_ctor_get_uint8(x_18, sizeof(void*)*7);
x_96 = l_Lean_Elab_DefKind_isTheorem(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_18, 4);
lean_inc(x_97);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_98 = l_Lean_Meta_isProp(x_97, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_102 = l_Lean_Elab_abstractNestedProofs(x_18, x_11, x_12, x_13, x_14, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; size_t x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_array_size(x_3);
lean_inc(x_3);
x_106 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__1(x_105, x_1, x_3);
lean_inc(x_2);
lean_inc(x_91);
lean_inc(x_103);
x_107 = l_Lean_Elab_Structural_registerEqnsInfo(x_103, x_106, x_91, x_2, x_13, x_14, x_104);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_110 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1(x_91, x_94, x_103, x_108, x_9, x_10, x_11, x_12, x_13, x_14, x_109);
lean_dec(x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_19 = x_111;
x_20 = x_112;
goto block_27;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_113 = lean_ctor_get(x_110, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_115 = x_110;
} else {
 lean_dec_ref(x_110);
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
lean_dec(x_103);
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_117 = lean_ctor_get(x_107, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_119 = x_107;
} else {
 lean_dec_ref(x_107);
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
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_121 = lean_ctor_get(x_102, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_123 = x_102;
} else {
 lean_dec_ref(x_102);
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
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_98, 1);
lean_inc(x_125);
lean_dec(x_98);
x_126 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_127 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1(x_91, x_94, x_18, x_126, x_9, x_10, x_11, x_12, x_13, x_14, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_19 = x_128;
x_20 = x_129;
goto block_27;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_130 = lean_ctor_get(x_127, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_132 = x_127;
} else {
 lean_dec_ref(x_127);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_134 = lean_ctor_get(x_98, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_98, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_136 = x_98;
} else {
 lean_dec_ref(x_98);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_139 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1(x_91, x_94, x_18, x_138, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_19 = x_140;
x_20 = x_141;
goto block_27;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_142 = lean_ctor_get(x_139, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_144 = x_139;
} else {
 lean_dec_ref(x_139);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
}
block_27:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 1;
x_25 = lean_usize_add(x_7, x_24);
x_7 = x_25;
x_8 = x_23;
x_15 = x_20;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_16 = lean_array_uget(x_3, x_5);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_17);
x_18 = l_Lean_enableRealizationsForConst(x_17, x_11, x_12, x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Lean_Meta_generateEagerEqns(x_17, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = 1;
x_23 = lean_usize_add(x_5, x_22);
x_24 = lean_box(0);
x_5 = x_23;
x_6 = x_24;
x_13 = x_21;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("structural recursion failed, produced type incorrect term", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_indentD(x_1);
x_3 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__2;
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
x_5 = l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4;
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Elab_eraseRecAppSyntax(x_14, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_1);
x_18 = lean_array_to_list(x_1);
x_19 = 0;
x_20 = lean_box(x_19);
lean_inc(x_7);
lean_inc(x_6);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_addNonRec___boxed), 10, 5);
lean_closure_set(x_21, 0, x_16);
lean_closure_set(x_21, 1, x_20);
lean_closure_set(x_21, 2, x_18);
lean_closure_set(x_21, 3, x_6);
lean_closure_set(x_21, 4, x_7);
x_22 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___closed__1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_mapErrorImp___rarg(x_21, x_22, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_3, x_26);
x_3 = x_27;
x_5 = x_24;
x_12 = x_25;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_23);
if (x_29 == 0)
{
return x_23;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_15, 0);
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_15);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_12);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_14 = lean_apply_5(x_13, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_structuralRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_size(x_1);
x_11 = 0;
lean_inc(x_1);
x_12 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__1(x_10, x_11, x_1);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos), 8, 2);
lean_closure_set(x_13, 0, x_1);
lean_closure_set(x_13, 1, x_2);
x_14 = l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Elab_Structural_run___rarg(x_13, x_14, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; lean_object* x_29; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_array_get_size(x_1);
x_25 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_26 = l_Array_toSubarray___rarg(x_1, x_25, x_24);
x_27 = lean_box(0);
x_28 = lean_array_size(x_21);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_29 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__1(x_21, x_27, x_21, x_28, x_11, x_26, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_array_get_size(x_20);
x_32 = lean_nat_dec_lt(x_25, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_20);
x_33 = x_30;
goto block_78;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_31, x_31);
if (x_79 == 0)
{
lean_dec(x_31);
lean_dec(x_20);
x_33 = x_30;
goto block_78;
}
else
{
size_t x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_81 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_82 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__5(x_20, x_11, x_80, x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_30);
lean_dec(x_20);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_33 = x_83;
goto block_78;
}
else
{
uint8_t x_84; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
return x_82;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_82);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
block_78:
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_34 = lean_array_get_size(x_22);
x_35 = lean_nat_dec_lt(x_25, x_34);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_12);
x_36 = x_33;
goto block_68;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_34, x_34);
if (x_69 == 0)
{
lean_dec(x_34);
lean_dec(x_12);
x_36 = x_33;
goto block_68;
}
else
{
size_t x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_71 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_72 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4(x_12, x_22, x_11, x_70, x_71, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_36 = x_73;
goto block_68;
}
else
{
uint8_t x_74; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_72);
if (x_74 == 0)
{
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_72);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
block_68:
{
lean_object* x_37; 
lean_inc(x_8);
lean_inc(x_7);
x_37 = l_Array_mapMUnsafe_map___at_Lean_Elab_addAndCompileUnsafe___spec__1(x_10, x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_38);
x_40 = l_Lean_Elab_addAndCompilePartialRec(x_38, x_3, x_4, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; size_t x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_array_get_size(x_21);
x_43 = l_Array_toSubarray___rarg(x_21, x_25, x_42);
x_44 = lean_array_size(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_38);
x_45 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2(x_11, x_23, x_38, x_27, x_38, x_44, x_11, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_48 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__3(x_38, x_27, x_38, x_44, x_11, x_47, x_3, x_4, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_38);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = 1;
x_51 = l_Lean_Elab_applyAttributesOf(x_22, x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_49);
lean_dec(x_22);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
return x_48;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_48, 0);
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_48);
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
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_45);
if (x_56 == 0)
{
return x_45;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_45, 0);
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_45);
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
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_40);
if (x_60 == 0)
{
return x_40;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_40, 0);
x_62 = lean_ctor_get(x_40, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_40);
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
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_37);
if (x_64 == 0)
{
return x_37;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_37, 0);
x_66 = lean_ctor_get(x_37, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_37);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_29);
if (x_88 == 0)
{
return x_29;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_29, 0);
x_90 = lean_ctor_get(x_29, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_29);
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
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
return x_15;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_15, 0);
x_94 = lean_ctor_get(x_15, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_15);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__1(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_17 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_18 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_19 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__2(x_16, x_2, x_3, x_4, x_5, x_17, x_18, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_Structural_structuralRecursion___spec__3(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__5(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
lean_object* initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Preprocess(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_BRecOn(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_IndPred(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Mutual(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Preprocess(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_BRecOn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_SmartUnfolding(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__1();
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___spec__1___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_getFixedPrefix___closed__3);
l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1 = _init_l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_withCommonTelescope___rarg___closed__1);
l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1 = _init_l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__1___closed__1);
l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__1 = _init_l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__1();
lean_mark_persistent(l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__1);
l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__2 = _init_l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__2();
lean_mark_persistent(l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__2);
l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__3 = _init_l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__3();
lean_mark_persistent(l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__3);
l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__4 = _init_l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__4();
lean_mark_persistent(l_Lean_getConstInfoInduct___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__2___closed__4);
l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___closed__1 = _init_l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__6___closed__1);
l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__1 = _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__1);
l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__2 = _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__2);
l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__3 = _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__3();
lean_mark_persistent(l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__3);
l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__4 = _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__4();
lean_mark_persistent(l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__4);
l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__5 = _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__5();
lean_mark_persistent(l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__5);
l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__6 = _init_l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__6();
lean_mark_persistent(l_Lean_Elab_Structural_Positions_groupAndSort___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___spec__4___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__3___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__4___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__5___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__7);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__6___closed__9);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__9___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___lambda__10___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_elimMutualRecursion___closed__2);
l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__1 = _init_l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__1();
lean_mark_persistent(l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__1);
l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__2 = _init_l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__2();
lean_mark_persistent(l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__2);
l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__3 = _init_l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__3();
lean_mark_persistent(l_Lean_exprDependsOn___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__12___closed__3);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__1);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__2);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__3 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__3();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__3);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__4 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__4();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__4);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__5 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__5();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__5);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__6 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__6();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__6);
l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__7 = _init_l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__7();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__30___closed__7);
l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__1 = _init_l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__1();
lean_mark_persistent(l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__1);
l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__2 = _init_l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__2();
lean_mark_persistent(l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__2);
l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__3 = _init_l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__3();
lean_mark_persistent(l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__3);
l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__4 = _init_l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__4();
lean_mark_persistent(l_Lean_setEnv___at___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___spec__41___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__7 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__7);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__8 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__8);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__9 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__9);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__10 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__10);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__11 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__11);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__12 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__12);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__13 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__13);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__14 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__14);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__15 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__15);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__16 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__4___closed__16);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__3 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__3);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__4 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__4);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__5 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__5);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__6 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__5___closed__6);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__2 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__6___closed__2);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8___boxed__const__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___lambda__8___boxed__const__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___closed__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___closed__1);
l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed__const__1 = _init_l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed__const__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_Structural_Main_0__Lean_Elab_Structural_inferRecArgPos___boxed__const__1);
l_Lean_Elab_Structural_reporttermMeasure___closed__1 = _init_l_Lean_Elab_Structural_reporttermMeasure___closed__1();
lean_mark_persistent(l_Lean_Elab_Structural_reporttermMeasure___closed__1);
l_Lean_Elab_Structural_reporttermMeasure___closed__2 = _init_l_Lean_Elab_Structural_reporttermMeasure___closed__2();
lean_mark_persistent(l_Lean_Elab_Structural_reporttermMeasure___closed__2);
l_Lean_Elab_Structural_reporttermMeasure___closed__3 = _init_l_Lean_Elab_Structural_reporttermMeasure___closed__3();
lean_mark_persistent(l_Lean_Elab_Structural_reporttermMeasure___closed__3);
l_Lean_Elab_Structural_reporttermMeasure___closed__4 = _init_l_Lean_Elab_Structural_reporttermMeasure___closed__4();
lean_mark_persistent(l_Lean_Elab_Structural_reporttermMeasure___closed__4);
l_Lean_Elab_Structural_reporttermMeasure___closed__5 = _init_l_Lean_Elab_Structural_reporttermMeasure___closed__5();
lean_mark_persistent(l_Lean_Elab_Structural_reporttermMeasure___closed__5);
l_Lean_Elab_Structural_reporttermMeasure___closed__6 = _init_l_Lean_Elab_Structural_reporttermMeasure___closed__6();
lean_mark_persistent(l_Lean_Elab_Structural_reporttermMeasure___closed__6);
l_Lean_Elab_Structural_reporttermMeasure___closed__7 = _init_l_Lean_Elab_Structural_reporttermMeasure___closed__7();
lean_mark_persistent(l_Lean_Elab_Structural_reporttermMeasure___closed__7);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__1);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___lambda__1___closed__2);
l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_Structural_structuralRecursion___spec__4___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
