// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Main
// Imports: Lean.Elab.PreDefinition.MkInhabitant Lean.Elab.PreDefinition.Mutual Lean.Elab.PreDefinition.PartialFixpoint.Eqns Lean.Elab.Tactic.Monotonicity Init.Internal.Order.Basic Lean.Meta.PProdN
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10(lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_logUnassignedUsingErrorInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__13;
static lean_object* l_Lean_Elab_partialFixpoint___closed__3;
extern lean_object* l_Lean_Elab_instInhabitedPreDefinition;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__14(lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__2;
lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__2;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__2;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__4;
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__3;
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__2;
lean_object* l_Lean_indentD(lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__4;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__7;
static lean_object* l_Lean_Elab_partialFixpoint___lambda__2___closed__6;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__6;
static lean_object* l_Lean_Elab_mkInstCCPOPProd___closed__2;
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__1;
lean_object* l_Array_findIdx_x3f_loop___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___lambda__2___closed__4;
lean_object* l_Lean_getRecAppSyntax_x3f(lean_object*);
lean_object* l_Lean_Meta_PProdN_reduceProjs___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___closed__1;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__22;
lean_object* l_Lean_Meta_PProdN_pack(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__3___boxed__const__1;
lean_object* l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__15___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__2;
static lean_object* l_Lean_Elab_mkMonoPProd___lambda__1___closed__1;
lean_object* l_Lean_Elab_Mutual_cleanPreDefs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___lambda__1___closed__1;
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__12;
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__2;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkMonoPProd___lambda__2___closed__1;
static lean_object* l_Lean_Elab_partialFixpoint___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__11;
static lean_object* l_Lean_Elab_partialFixpoint___lambda__3___closed__5;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__6;
static lean_object* l_Lean_Elab_partialFixpoint___lambda__3___closed__3;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__1;
lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTermEnsuringType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__1;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__3;
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___lambda__2___closed__7;
static lean_object* l_Lean_Elab_mkMonoPProd___lambda__1___closed__3;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__2;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__12;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3___closed__1;
lean_object* l_instMonadControlTOfMonadControl___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__11;
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3(lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__17;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__6;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_proj(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__2;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__3;
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_genMk___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_andList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__14___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___lambda__3___closed__7;
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__16;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___lambda__2___closed__1;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__7;
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkMonoPProd___lambda__2___closed__2;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___rarg(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__15___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_reduceProjs___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__19;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__8;
static lean_object* l_Lean_Elab_mkInstCCPOPProd___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__9;
lean_object* l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__2;
static lean_object* l_Lean_Elab_partialFixpoint___lambda__3___closed__8;
static lean_object* l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkInstCCPOPProd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_instInhabitedPartialFixpoint;
static lean_object* l_Lean_Elab_partialFixpoint___lambda__2___closed__8;
static lean_object* l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg___closed__1;
static lean_object* l_Lean_Elab_mkMonoPProd___lambda__3___closed__1;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__2;
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__3;
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__15;
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__1;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_instMonadControlTOfPure___rarg(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___lambda__1___closed__2;
static lean_object* l_Lean_Elab_partialFixpoint___closed__4;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_hasRecAppSyntax___boxed(lean_object*);
static lean_object* l_Lean_Elab_mkMonoPProd___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__4;
static lean_object* l_Lean_Elab_partialFixpoint___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8(size_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__3;
static lean_object* l_Lean_Elab_partialFixpoint___lambda__2___closed__2;
static lean_object* l_Lean_Elab_partialFixpoint___lambda__3___closed__1;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__4;
lean_object* l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__17___boxed(lean_object**);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__9;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__6;
lean_object* l_Lean_Elab_mkInhabitantFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_getFixedPrefix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__8;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__9(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__3;
static lean_object* l_Lean_Elab_partialFixpoint___lambda__3___closed__4;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__1;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__2___boxed(lean_object**);
lean_object* l_Lean_indentExpr(lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__12;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__18;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__14;
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__3;
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__20;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_instMonadControlReaderT___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_PProdN_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8___lambda__1(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Core_instMonadCoreM;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__14___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkMonoPProd___lambda__1___closed__2;
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Meta_Monotonicity_initFn____x40_Lean_Elab_Tactic_Monotonicity___hyg_245____spec__2___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___closed__6;
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__7;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__11;
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__4;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Elab_mkInstCCPOPProd___closed__3;
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___boxed(lean_object**);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__15(lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__1;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__5;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__8;
lean_object* l_Lean_Meta_Monotonicity_solveMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__9;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__10;
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__10;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__10;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__14;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___lambda__3___closed__6;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__17(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_mkInstCCPOPProd___closed__1;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_partialFixpoint___closed__5;
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_partialFixpoint___spec__11(lean_object*);
static lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__15;
lean_object* l_ReaderT_instMonad___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_instMonadControlReaderT___lambda__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_findIdx_x3f_loop___rarg(x_6, x_2, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_array_get_size(x_2);
x_13 = l_Lean_Meta_PProdN_proj(x_12, x_11, x_3, x_4);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_array_get_size(x_2);
x_16 = l_Lean_Meta_PProdN_proj(x_15, x_14, x_3, x_4);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = lean_infer_type(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__2___boxed), 5, 4);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_3);
x_14 = lean_replace_expr(x_13, x_4);
lean_dec(x_13);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__2___boxed), 5, 4);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_3);
x_18 = lean_replace_expr(x_17, x_4);
lean_dec(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = lean_ctor_get(x_6, 3);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_10, x_11);
x_13 = l_Lean_Expr_const___override(x_9, x_12);
x_14 = l_Lean_mkAppN(x_13, x_1);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_17 = lean_array_uset(x_8, x_3, x_14);
x_3 = x_16;
x_4 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Elab_addAsAxiom(x_11, x_5, x_6, x_7, x_8, x_9);
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
lean_dec(x_8);
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
lean_dec(x_8);
lean_dec(x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_9);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_expr_eqv(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_reduceProjs___lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_PProdN_reduceProjs___lambda__2___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get(x_9, x_2, x_10);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_replace_expr(x_12, x_3);
lean_dec(x_12);
x_14 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__1;
x_15 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__2;
x_16 = l_Lean_Core_transform___at_Lean_Core_betaReduce___spec__1(x_13, x_14, x_15, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
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
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_array_get_size(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = lean_st_ref_get(x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
if (x_13 == 0)
{
lean_dec(x_11);
x_18 = x_16;
goto block_61;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_11, x_11);
if (x_62 == 0)
{
lean_dec(x_11);
x_18 = x_16;
goto block_61;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_65 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
x_66 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__2(x_1, x_63, x_64, x_65, x_6, x_7, x_8, x_9, x_16);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_18 = x_67;
goto block_61;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_17, x_6, x_7, x_8, x_9, x_69);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 0);
lean_dec(x_72);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_68);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
block_61:
{
size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_array_size(x_1);
x_20 = 0;
x_21 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__1(x_2, x_19, x_20, x_1);
x_22 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Meta_PProdN_mk(x_22, x_21, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___boxed), 8, 1);
lean_closure_set(x_26, 0, x_24);
x_27 = lean_unsigned_to_nat(1u);
x_28 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = l_Lean_Meta_lambdaBoundedTelescope___at_Lean_Meta_Monotonicity_initFn____x40_Lean_Elab_Tactic_Monotonicity___hyg_245____spec__2___rarg(x_3, x_27, x_26, x_28, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_32 = lean_apply_6(x_4, x_30, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_17, x_6, x_7, x_8, x_9, x_34);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_33);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_17, x_6, x_7, x_8, x_9, x_41);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_4);
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_17, x_6, x_7, x_8, x_9, x_48);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_47);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_dec(x_4);
lean_dec(x_3);
x_54 = lean_ctor_get(x_23, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_23, 1);
lean_inc(x_55);
lean_dec(x_23);
x_56 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_17, x_6, x_7, x_8, x_9, x_55);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected lambda:", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isLambda(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = l_Lean_indentExpr(x_3);
x_12 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__2;
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___at_Lean_Meta_mkSimpCongrTheorem___spec__4(x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3(x_1, x_2, x_3, x_4, x_21, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_mkInstCCPOPProd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkInstCCPOPProd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Order", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkInstCCPOPProd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instCCPOPProd", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkInstCCPOPProd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__2;
x_3 = l_Lean_Elab_mkInstCCPOPProd___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkInstCCPOPProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_mk(x_15);
x_17 = l_Lean_Elab_mkInstCCPOPProd___closed__4;
x_18 = l_Lean_Meta_mkAppOptM(x_17, x_16, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
}
static lean_object* _init_l_Lean_Elab_mkMonoPProd___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PProd", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMonoPProd___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("monotone_mk", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMonoPProd___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__2;
x_3 = l_Lean_Elab_mkMonoPProd___lambda__1___closed__1;
x_4 = l_Lean_Elab_mkMonoPProd___lambda__1___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_11);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
x_29 = l_Lean_Elab_mkMonoPProd___lambda__1___closed__3;
x_30 = l_Lean_Meta_mkAppOptM(x_29, x_28, x_6, x_7, x_8, x_9, x_10);
return x_30;
}
}
static lean_object* _init_l_Lean_Elab_mkMonoPProd___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkMonoPProd: unexpected type of", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMonoPProd___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_mkMonoPProd___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_indentExpr(x_1);
x_9 = l_Lean_Elab_mkMonoPProd___lambda__2___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_mkMonoPProd___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("monotone", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_mkMonoPProd___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__2;
x_3 = l_Lean_Elab_mkMonoPProd___lambda__3___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = lean_infer_type(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_cleanupAnnotations(x_11);
x_14 = l_Lean_Expr_isApp(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_15, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_appFnCleanup(x_13, lean_box(0));
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_19, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Expr_appArg(x_17, lean_box(0));
x_22 = l_Lean_Expr_appFnCleanup(x_17, lean_box(0));
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_24, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Expr_appFnCleanup(x_22, lean_box(0));
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_28, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = l_Lean_Expr_appFnCleanup(x_26, lean_box(0));
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_32, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = l_Lean_Expr_appFnCleanup(x_30, lean_box(0));
x_35 = l_Lean_Elab_mkMonoPProd___lambda__3___closed__2;
x_36 = l_Lean_Expr_isConstOf(x_34, x_35);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_37, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_38;
}
else
{
lean_object* x_39; 
x_39 = l_Lean_Elab_mkMonoPProd___lambda__1(x_4, x_3, x_2, x_1, x_21, x_5, x_6, x_7, x_8, x_12);
return x_39;
}
}
}
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_cleanupAnnotations(x_9);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_13, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_appFnCleanup(x_11, lean_box(0));
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_17, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = l_Lean_Expr_appArg(x_15, lean_box(0));
x_20 = l_Lean_Expr_appFnCleanup(x_15, lean_box(0));
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_2);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_22, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup(x_20, lean_box(0));
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_26, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Expr_appArg(x_24, lean_box(0));
x_29 = l_Lean_Expr_appFnCleanup(x_24, lean_box(0));
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_2);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_31, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Expr_appFnCleanup(x_29, lean_box(0));
x_34 = l_Lean_Elab_mkMonoPProd___lambda__3___closed__2;
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_19);
lean_dec(x_2);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_36, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Elab_mkMonoPProd___lambda__3(x_2, x_1, x_28, x_19, x_3, x_4, x_5, x_6, x_10);
return x_38;
}
}
}
}
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_mkMonoPProd___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_mkMonoPProd___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 6);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 3);
lean_inc(x_8);
lean_dec(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
if (lean_obj_tag(x_8) == 0)
{
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_array_push(x_4, x_12);
x_2 = x_10;
x_4 = x_13;
goto _start;
}
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___closed__1;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_le(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__2(x_1, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg___lambda__1), 10, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
x_12 = lean_box(0);
x_13 = 0;
x_14 = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp___rarg(x_1, x_13, x_12, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
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
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg___boxed), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_10, x_11, x_10, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to compile definition '", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' using `partial_fixpoint`", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nonempty", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__5;
x_2 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__6;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Classical", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNonempty", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__8;
x_2 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__9;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("FlatOrder", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instCCPO", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__2;
x_3 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__11;
x_4 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__12;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_MessageData_ofName(x_13);
x_15 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__4;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_2);
x_19 = lean_array_mk(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Elab_mkInhabitantFor(x_18, x_19, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_mkAppN(x_21, x_4);
lean_inc(x_2);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_array_mk(x_24);
x_26 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__7;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_27 = l_Lean_Meta_mkAppM(x_26, x_25, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
lean_inc(x_2);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_mk(x_33);
x_35 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__10;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_36 = l_Lean_Meta_mkAppOptM(x_35, x_34, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_2);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_30);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_mk(x_41);
x_43 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__13;
x_44 = l_Lean_Meta_mkAppOptM(x_43, x_42, x_8, x_9, x_10, x_11, x_38);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_36);
if (x_45 == 0)
{
return x_36;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_36, 0);
x_47 = lean_ctor_get(x_36, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_36);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_20);
if (x_53 == 0)
{
return x_20;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_20, 0);
x_55 = lean_ctor_get(x_20, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_20);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CCPO", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__2;
x_3 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__3;
x_2 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__4;
x_3 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("No CCPO instance found for ", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", trying inhabitation", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_11);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_2, x_12, x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_87; lean_object* x_88; 
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
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_array_mk(x_18);
x_87 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_88 = l_Lean_Meta_mkAppM(x_87, x_19, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_92 = l_Lean_Meta_synthInstance(x_89, x_91, x_6, x_7, x_8, x_9, x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_1);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = 0;
x_96 = 1;
x_97 = 1;
x_98 = l_Lean_Meta_mkLambdaFVars(x_2, x_93, x_95, x_96, x_95, x_97, x_6, x_7, x_8, x_9, x_94);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_92, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_92, 1);
lean_inc(x_100);
lean_dec(x_92);
x_20 = x_99;
x_21 = x_100;
goto block_86;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_88, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_88, 1);
lean_inc(x_102);
lean_dec(x_88);
x_20 = x_101;
x_21 = x_102;
goto block_86;
}
block_86:
{
uint8_t x_22; 
x_22 = l_Lean_Exception_isInterrupt(x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Exception_isRuntime(x_20);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_20);
lean_dec(x_16);
x_24 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__6;
x_25 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_30 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2(x_1, x_17, x_11, x_2, x_29, x_4, x_5, x_6, x_7, x_8, x_9, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = 0;
x_34 = 1;
x_35 = 1;
x_36 = l_Lean_Meta_mkLambdaFVars(x_2, x_31, x_33, x_34, x_33, x_35, x_6, x_7, x_8, x_9, x_32);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_25, 1);
x_43 = lean_ctor_get(x_25, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_1, 3);
lean_inc(x_44);
x_45 = l_Lean_MessageData_ofName(x_44);
x_46 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__8;
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_45);
lean_ctor_set(x_25, 0, x_46);
x_47 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__10;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_25);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_24, x_48, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_52 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2(x_1, x_17, x_11, x_2, x_50, x_4, x_5, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_50);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = 0;
x_56 = 1;
x_57 = 1;
x_58 = l_Lean_Meta_mkLambdaFVars(x_2, x_53, x_55, x_56, x_55, x_57, x_6, x_7, x_8, x_9, x_54);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_52);
if (x_59 == 0)
{
return x_52;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_52, 0);
x_61 = lean_ctor_get(x_52, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_52);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_63 = lean_ctor_get(x_25, 1);
lean_inc(x_63);
lean_dec(x_25);
x_64 = lean_ctor_get(x_1, 3);
lean_inc(x_64);
x_65 = l_Lean_MessageData_ofName(x_64);
x_66 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__8;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__10;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_24, x_69, x_4, x_5, x_6, x_7, x_8, x_9, x_63);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_73 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2(x_1, x_17, x_11, x_2, x_71, x_4, x_5, x_6, x_7, x_8, x_9, x_72);
lean_dec(x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = 0;
x_77 = 1;
x_78 = 1;
x_79 = l_Lean_Meta_mkLambdaFVars(x_2, x_74, x_76, x_77, x_76, x_78, x_6, x_7, x_8, x_9, x_75);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_73, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_82 = x_73;
} else {
 lean_dec_ref(x_73);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
if (lean_is_scalar(x_16)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_16;
 lean_ctor_set_tag(x_84, 1);
}
lean_ctor_set(x_84, 0, x_20);
lean_ctor_set(x_84, 1, x_21);
return x_84;
}
}
else
{
lean_object* x_85; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
if (lean_is_scalar(x_16)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_16;
 lean_ctor_set_tag(x_85, 1);
}
lean_ctor_set(x_85, 0, x_20);
lean_ctor_set(x_85, 1, x_21);
return x_85;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_13);
if (x_103 == 0)
{
return x_13;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_13, 0);
x_105 = lean_ctor_get(x_13, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_13);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_4, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_4, x_17);
lean_dec(x_4);
x_19 = lean_array_fget(x_3, x_5);
x_20 = l_Lean_Elab_instInhabitedPartialFixpoint;
x_21 = lean_array_get(x_20, x_2, x_5);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_19, 5);
lean_inc(x_23);
x_24 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___boxed), 10, 1);
lean_closure_set(x_24, 0, x_19);
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
x_27 = lean_ctor_get(x_12, 2);
x_28 = lean_ctor_get(x_12, 3);
x_29 = lean_ctor_get(x_12, 4);
x_30 = lean_ctor_get(x_12, 5);
x_31 = lean_ctor_get(x_12, 6);
x_32 = lean_ctor_get(x_12, 7);
x_33 = lean_ctor_get(x_12, 8);
x_34 = lean_ctor_get(x_12, 9);
x_35 = lean_ctor_get(x_12, 10);
x_36 = lean_ctor_get_uint8(x_12, sizeof(void*)*12);
x_37 = lean_ctor_get(x_12, 11);
x_38 = lean_ctor_get_uint8(x_12, sizeof(void*)*12 + 1);
x_39 = l_Lean_replaceRef(x_22, x_30);
lean_dec(x_22);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
x_40 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_40, 0, x_25);
lean_ctor_set(x_40, 1, x_26);
lean_ctor_set(x_40, 2, x_27);
lean_ctor_set(x_40, 3, x_28);
lean_ctor_set(x_40, 4, x_29);
lean_ctor_set(x_40, 5, x_39);
lean_ctor_set(x_40, 6, x_31);
lean_ctor_set(x_40, 7, x_32);
lean_ctor_set(x_40, 8, x_33);
lean_ctor_set(x_40, 9, x_34);
lean_ctor_set(x_40, 10, x_35);
lean_ctor_set(x_40, 11, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*12, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*12 + 1, x_38);
x_41 = 0;
lean_inc(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_42 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg(x_23, x_24, x_41, x_8, x_9, x_10, x_11, x_40, x_13, x_14);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_46 = lean_array_push(x_7, x_43);
x_4 = x_18;
x_5 = x_45;
x_6 = lean_box(0);
x_7 = x_46;
x_14 = x_44;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
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
else
{
lean_object* x_52; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_7);
lean_ctor_set(x_52, 1, x_14);
return x_52;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_9 = l_Lean_Expr_beta(x_6, x_1);
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_12 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_11;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_ctor_get(x_14, 4);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_18 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateForallAux(x_1, x_15, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = 1;
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_16, x_3, x_19);
x_3 = x_22;
x_4 = x_23;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
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
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instCCPOPi", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__2;
x_3 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__1;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_uget(x_3, x_5);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_16);
x_17 = lean_infer_type(x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_mk(x_21);
x_23 = 0;
x_24 = 1;
x_25 = 1;
x_26 = l_Lean_Meta_mkLambdaFVars(x_22, x_6, x_23, x_24, x_23, x_25, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_18);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_27);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_mk(x_34);
x_36 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__2;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_37 = l_Lean_Meta_mkAppOptM(x_36, x_35, x_9, x_10, x_11, x_12, x_28);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; size_t x_40; size_t x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = 1;
x_41 = lean_usize_add(x_5, x_40);
x_5 = x_41;
x_6 = x_38;
x_13 = x_39;
goto _start;
}
else
{
uint8_t x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
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
else
{
uint8_t x_47; 
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_47 = !lean_is_exclusive(x_26);
if (x_47 == 0)
{
return x_26;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
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
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_17, 0);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_17);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = l_Array_reverse___rarg(x_2);
x_13 = lean_array_size(x_12);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7(x_11, x_12, x_12, x_13, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
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
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8(size_t x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_array_uget(x_4, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_box_usize(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8___lambda__1___boxed), 10, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_20 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg(x_14, x_18, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_array_uset(x_16, x_3, x_21);
x_3 = x_24;
x_4 = x_25;
x_11 = x_22;
goto _start;
}
else
{
uint8_t x_27; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_14 = l_Lean_Elab_addAsAxiom(x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_13);
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
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_lt(x_15, x_1);
x_17 = lean_st_ref_get(x_13, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
if (x_16 == 0)
{
x_21 = x_19;
goto block_50;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_1, x_1);
if (x_51 == 0)
{
x_21 = x_19;
goto block_50;
}
else
{
size_t x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_usize_of_nat(x_1);
x_53 = lean_box(0);
lean_inc(x_13);
lean_inc(x_12);
x_54 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__9(x_5, x_6, x_52, x_53, x_8, x_9, x_10, x_11, x_12, x_13, x_19);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_21 = x_55;
goto block_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_57);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_58, 0);
lean_dec(x_60);
lean_ctor_set_tag(x_58, 1);
lean_ctor_set(x_58, 0, x_56);
return x_58;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_56);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
block_50:
{
lean_object* x_22; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_22 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_replaceRecApps(x_2, x_3, x_7, x_4, x_10, x_11, x_12, x_13, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_29);
lean_ctor_set(x_25, 0, x_7);
x_30 = lean_array_mk(x_25);
x_31 = 0;
x_32 = 1;
x_33 = 1;
x_34 = l_Lean_Meta_mkLambdaFVars(x_30, x_23, x_31, x_32, x_31, x_33, x_10, x_11, x_12, x_13, x_27);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_dec(x_25);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_array_mk(x_37);
x_39 = 0;
x_40 = 1;
x_41 = 1;
x_42 = l_Lean_Meta_mkLambdaFVars(x_38, x_23, x_39, x_40, x_39, x_41, x_10, x_11, x_12, x_13, x_35);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_38);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_7);
x_43 = lean_ctor_get(x_22, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_dec(x_22);
x_45 = l_Lean_setEnv___at_Lean_Elab_Term_evalTerm___spec__1(x_20, x_8, x_9, x_10, x_11, x_12, x_13, x_44);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("f", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_9, x_8);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_array_uget(x_10, x_9);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_uset(x_10, x_9, x_21);
x_23 = lean_ctor_get(x_20, 5);
lean_inc(x_23);
lean_dec(x_20);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_24 = l___private_Lean_Meta_Basic_0__Lean_Meta_instantiateLambdaAux(x_6, x_21, x_23, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__2;
x_28 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_27, x_15, x_16, x_26);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box_usize(x_4);
lean_inc(x_1);
lean_inc(x_3);
lean_inc(x_5);
lean_inc(x_2);
x_32 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___lambda__1___boxed), 14, 6);
lean_closure_set(x_32, 0, x_2);
lean_closure_set(x_32, 1, x_5);
lean_closure_set(x_32, 2, x_3);
lean_closure_set(x_32, 3, x_25);
lean_closure_set(x_32, 4, x_1);
lean_closure_set(x_32, 5, x_31);
x_33 = 0;
x_34 = 0;
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_7);
x_35 = l_Lean_Meta_withLocalDecl___at_Lean_Elab_Term_withAuxDecl___spec__1___rarg(x_29, x_33, x_7, x_32, x_34, x_11, x_12, x_13, x_14, x_15, x_16, x_30);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = 1;
x_39 = lean_usize_add(x_9, x_38);
x_40 = lean_array_uset(x_22, x_9, x_36);
x_9 = x_39;
x_10 = x_40;
x_17 = x_37;
goto _start;
}
else
{
uint8_t x_42; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
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
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_24);
if (x_46 == 0)
{
return x_24;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Elab_partialFixpoint___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = 0;
x_8 = l_Lean_MessageData_ofConstName(x_5, x_7);
x_9 = l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_11);
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
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = 0;
x_16 = l_Lean_MessageData_ofConstName(x_13, x_15);
x_17 = l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__2;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
x_1 = x_14;
x_2 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__14___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__15___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__15___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.PartialFixpoint.Main", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.partialFixpoint", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("getRecAppSyntax\? failed", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__1;
x_2 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(117u);
x_4 = lean_unsigned_to_nat(52u);
x_5 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot eliminate recursive call `", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` enclosed in", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_hasRecAppSyntax___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tried to apply ", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", but failed.\nPossible cause: A missing `", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MonoBind", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__2;
x_3 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__16;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__17;
x_2 = 0;
x_3 = l_Lean_MessageData_ofConstName(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` instance.\nUse `set_option trace.Elab.Tactic.monotonicity true` to debug.", 74, 74);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot eliminate recursive call in", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_48 = l_Array_isEmpty___rarg(x_1);
x_49 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__11;
x_50 = lean_find_expr(x_49, x_2);
if (x_48 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_array_to_list(x_1);
x_52 = lean_box(0);
x_53 = l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13(x_51, x_52);
x_54 = l_Lean_MessageData_andList(x_53);
x_55 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__13;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__15;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__18;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__20;
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_63 = l_Lean_indentExpr(x_2);
x_64 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__22;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__10;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
x_69 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__14___rarg(x_70, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_71;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_50, 0);
lean_inc(x_72);
lean_dec(x_50);
x_8 = x_62;
x_9 = x_72;
goto block_47;
}
}
else
{
lean_dec(x_1);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = l_Lean_indentExpr(x_2);
x_74 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__22;
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__10;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__15___rarg(x_80, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_50, 0);
lean_inc(x_82);
lean_dec(x_50);
x_83 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_8 = x_83;
x_9 = x_82;
goto block_47;
}
}
block_47:
{
lean_object* x_10; 
x_10 = l_Lean_getRecAppSyntax_x3f(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_2);
x_11 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__4;
x_12 = l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg(x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_13);
x_14 = l_Lean_MessageData_ofSyntax(x_13);
x_15 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__6;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__8;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_indentExpr(x_2);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__10;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
x_24 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = !lean_is_exclusive(x_5);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_5, 5);
x_28 = l_Lean_replaceRef(x_13, x_27);
lean_dec(x_27);
lean_dec(x_13);
lean_ctor_set(x_5, 5, x_28);
x_29 = l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12___rarg(x_25, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_30 = lean_ctor_get(x_5, 0);
x_31 = lean_ctor_get(x_5, 1);
x_32 = lean_ctor_get(x_5, 2);
x_33 = lean_ctor_get(x_5, 3);
x_34 = lean_ctor_get(x_5, 4);
x_35 = lean_ctor_get(x_5, 5);
x_36 = lean_ctor_get(x_5, 6);
x_37 = lean_ctor_get(x_5, 7);
x_38 = lean_ctor_get(x_5, 8);
x_39 = lean_ctor_get(x_5, 9);
x_40 = lean_ctor_get(x_5, 10);
x_41 = lean_ctor_get_uint8(x_5, sizeof(void*)*12);
x_42 = lean_ctor_get(x_5, 11);
x_43 = lean_ctor_get_uint8(x_5, sizeof(void*)*12 + 1);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_5);
x_44 = l_Lean_replaceRef(x_13, x_35);
lean_dec(x_35);
lean_dec(x_13);
x_45 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_45, 0, x_30);
lean_ctor_set(x_45, 1, x_31);
lean_ctor_set(x_45, 2, x_32);
lean_ctor_set(x_45, 3, x_33);
lean_ctor_set(x_45, 4, x_34);
lean_ctor_set(x_45, 5, x_44);
lean_ctor_set(x_45, 6, x_36);
lean_ctor_set(x_45, 7, x_37);
lean_ctor_set(x_45, 8, x_38);
lean_ctor_set(x_45, 9, x_39);
lean_ctor_set(x_45, 10, x_40);
lean_ctor_set(x_45, 11, x_42);
lean_ctor_set_uint8(x_45, sizeof(void*)*12, x_41);
lean_ctor_set_uint8(x_45, sizeof(void*)*12 + 1, x_43);
x_46 = l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12___rarg(x_25, x_3, x_4, x_45, x_6, x_7);
lean_dec(x_6);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_3);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1), 7, 1);
lean_closure_set(x_11, 0, x_5);
x_12 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg(x_1, x_2, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Could not prove '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to be monotone in its recursive calls:", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_MessageData_ofName(x_3);
x_5 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__2;
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__4;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_indentD(x_2);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("monotonicity proof for ", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25, lean_object* x_26) {
_start:
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_eq(x_16, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_16, x_29);
lean_dec(x_16);
x_31 = lean_array_fget(x_15, x_17);
x_38 = l_Lean_instInhabitedExpr;
x_39 = lean_array_get(x_38, x_8, x_17);
x_40 = lean_array_get(x_38, x_14, x_17);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_39);
x_42 = lean_array_get(x_38, x_10, x_17);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_inc(x_12);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_12);
lean_inc(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_mk(x_45);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_11);
x_47 = l_Lean_Meta_mkAppOptM(x_11, x_46, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_9);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_9);
lean_inc(x_13);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_13);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_48);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_40);
lean_inc(x_12);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_12);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_41);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_array_mk(x_58);
x_60 = l_Lean_Elab_mkMonoPProd___lambda__3___closed__2;
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_61 = l_Lean_Meta_mkAppOptM(x_60, x_59, x_22, x_23, x_24, x_25, x_49);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Elab_instInhabitedPartialFixpoint;
x_65 = lean_array_get(x_64, x_2, x_17);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_box(0);
lean_inc(x_22);
x_68 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_62, x_67, x_22, x_23, x_24, x_25, x_63);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_7);
lean_inc(x_1);
x_72 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__2___boxed), 10, 2);
lean_closure_set(x_72, 0, x_1);
lean_closure_set(x_72, 1, x_7);
x_73 = l_Lean_Expr_mvarId_x21(x_70);
lean_inc(x_31);
x_74 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3), 2, 1);
lean_closure_set(x_74, 0, x_31);
x_75 = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_solveMono), 7, 2);
lean_closure_set(x_75, 0, x_72);
lean_closure_set(x_75, 1, x_73);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_76 = l_Lean_Meta_mapErrorImp___rarg(x_75, x_74, x_22, x_23, x_24, x_25, x_71);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_inc(x_3);
x_78 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_3, x_20, x_21, x_22, x_23, x_24, x_25, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_free_object(x_68);
lean_dec(x_31);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_70, x_20, x_21, x_22, x_23, x_24, x_25, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_32 = x_83;
x_33 = x_84;
goto block_37;
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_78);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_86 = lean_ctor_get(x_78, 1);
x_87 = lean_ctor_get(x_78, 0);
lean_dec(x_87);
x_88 = lean_ctor_get(x_31, 3);
lean_inc(x_88);
lean_dec(x_31);
x_89 = l_Lean_MessageData_ofName(x_88);
x_90 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__2;
lean_ctor_set_tag(x_78, 7);
lean_ctor_set(x_78, 1, x_89);
lean_ctor_set(x_78, 0, x_90);
x_91 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__4;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_91);
lean_ctor_set(x_68, 0, x_78);
lean_inc(x_70);
x_92 = l_Lean_MessageData_ofExpr(x_70);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_68);
lean_ctor_set(x_93, 1, x_92);
x_94 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_3);
x_96 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_3, x_95, x_20, x_21, x_22, x_23, x_24, x_25, x_86);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_70, x_20, x_21, x_22, x_23, x_24, x_25, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_32 = x_99;
x_33 = x_100;
goto block_37;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_101 = lean_ctor_get(x_78, 1);
lean_inc(x_101);
lean_dec(x_78);
x_102 = lean_ctor_get(x_31, 3);
lean_inc(x_102);
lean_dec(x_31);
x_103 = l_Lean_MessageData_ofName(x_102);
x_104 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__2;
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
x_106 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__4;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_106);
lean_ctor_set(x_68, 0, x_105);
lean_inc(x_70);
x_107 = l_Lean_MessageData_ofExpr(x_70);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_68);
lean_ctor_set(x_108, 1, x_107);
x_109 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_inc(x_3);
x_111 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_3, x_110, x_20, x_21, x_22, x_23, x_24, x_25, x_101);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_70, x_20, x_21, x_22, x_23, x_24, x_25, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_32 = x_114;
x_33 = x_115;
goto block_37;
}
}
}
else
{
uint8_t x_116; 
lean_free_object(x_68);
lean_dec(x_70);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_76);
if (x_116 == 0)
{
return x_76;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_76, 0);
x_118 = lean_ctor_get(x_76, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_76);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_68, 0);
x_121 = lean_ctor_get(x_68, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_68);
lean_inc(x_7);
lean_inc(x_1);
x_122 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__2___boxed), 10, 2);
lean_closure_set(x_122, 0, x_1);
lean_closure_set(x_122, 1, x_7);
x_123 = l_Lean_Expr_mvarId_x21(x_120);
lean_inc(x_31);
x_124 = lean_alloc_closure((void*)(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3), 2, 1);
lean_closure_set(x_124, 0, x_31);
x_125 = lean_alloc_closure((void*)(l_Lean_Meta_Monotonicity_solveMono), 7, 2);
lean_closure_set(x_125, 0, x_122);
lean_closure_set(x_125, 1, x_123);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_126 = l_Lean_Meta_mapErrorImp___rarg(x_125, x_124, x_22, x_23, x_24, x_25, x_121);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
lean_inc(x_3);
x_128 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_3, x_20, x_21, x_22, x_23, x_24, x_25, x_127);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_31);
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
x_132 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_120, x_20, x_21, x_22, x_23, x_24, x_25, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_32 = x_133;
x_33 = x_134;
goto block_37;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_136 = x_128;
} else {
 lean_dec_ref(x_128);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_31, 3);
lean_inc(x_137);
lean_dec(x_31);
x_138 = l_Lean_MessageData_ofName(x_137);
x_139 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__2;
if (lean_is_scalar(x_136)) {
 x_140 = lean_alloc_ctor(7, 2, 0);
} else {
 x_140 = x_136;
 lean_ctor_set_tag(x_140, 7);
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
x_141 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__4;
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
lean_inc(x_120);
x_143 = l_Lean_MessageData_ofExpr(x_120);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
lean_inc(x_3);
x_147 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_3, x_146, x_20, x_21, x_22, x_23, x_24, x_25, x_135);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_120, x_20, x_21, x_22, x_23, x_24, x_25, x_148);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_32 = x_150;
x_33 = x_151;
goto block_37;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_120);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_152 = lean_ctor_get(x_126, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_126, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_154 = x_126;
} else {
 lean_dec_ref(x_126);
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
lean_dec(x_31);
x_156 = !lean_is_exclusive(x_66);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_66, 0);
lean_inc(x_62);
lean_ctor_set(x_66, 0, x_62);
x_158 = lean_box(0);
x_159 = 1;
x_160 = lean_box(x_159);
x_161 = lean_box(x_159);
x_162 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_162, 0, x_157);
lean_closure_set(x_162, 1, x_66);
lean_closure_set(x_162, 2, x_160);
lean_closure_set(x_162, 3, x_161);
lean_closure_set(x_162, 4, x_158);
x_163 = 1;
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_164 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_162, x_163, x_20, x_21, x_22, x_23, x_24, x_25, x_63);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_165, x_20, x_21, x_22, x_23, x_24, x_25, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_168);
x_170 = l_Lean_Meta_getMVars(x_168, x_22, x_23, x_24, x_25, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Array_isEmpty___rarg(x_171);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_168);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_174 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_171, x_158, x_20, x_21, x_22, x_23, x_24, x_25, x_172);
lean_dec(x_171);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_176 = l_Lean_Meta_mkSorry(x_62, x_159, x_22, x_23, x_24, x_25, x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_32 = x_177;
x_33 = x_178;
goto block_37;
}
else
{
uint8_t x_179; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
return x_176;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_176, 0);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_176);
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
lean_dec(x_62);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_174);
if (x_183 == 0)
{
return x_174;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_174, 0);
x_185 = lean_ctor_get(x_174, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_174);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
lean_dec(x_171);
lean_dec(x_62);
x_32 = x_168;
x_33 = x_172;
goto block_37;
}
}
else
{
uint8_t x_187; 
lean_dec(x_62);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_164);
if (x_187 == 0)
{
return x_164;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_164, 0);
x_189 = lean_ctor_get(x_164, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_164);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; 
x_191 = lean_ctor_get(x_66, 0);
lean_inc(x_191);
lean_dec(x_66);
lean_inc(x_62);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_62);
x_193 = lean_box(0);
x_194 = 1;
x_195 = lean_box(x_194);
x_196 = lean_box(x_194);
x_197 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabTermEnsuringType___boxed), 12, 5);
lean_closure_set(x_197, 0, x_191);
lean_closure_set(x_197, 1, x_192);
lean_closure_set(x_197, 2, x_195);
lean_closure_set(x_197, 3, x_196);
lean_closure_set(x_197, 4, x_193);
x_198 = 1;
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_199 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_197, x_198, x_20, x_21, x_22, x_23, x_24, x_25, x_63);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l_Lean_instantiateMVars___at_Lean_Elab_Term_MVarErrorInfo_logError___spec__1(x_200, x_20, x_21, x_22, x_23, x_24, x_25, x_201);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
lean_inc(x_203);
x_205 = l_Lean_Meta_getMVars(x_203, x_22, x_23, x_24, x_25, x_204);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Array_isEmpty___rarg(x_206);
if (x_208 == 0)
{
lean_object* x_209; 
lean_dec(x_203);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
x_209 = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(x_206, x_193, x_20, x_21, x_22, x_23, x_24, x_25, x_207);
lean_dec(x_206);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_209, 1);
lean_inc(x_210);
lean_dec(x_209);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_211 = l_Lean_Meta_mkSorry(x_62, x_194, x_22, x_23, x_24, x_25, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_32 = x_212;
x_33 = x_213;
goto block_37;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_214 = lean_ctor_get(x_211, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_216 = x_211;
} else {
 lean_dec_ref(x_211);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_62);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_218 = lean_ctor_get(x_209, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_209, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_220 = x_209;
} else {
 lean_dec_ref(x_209);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_dec(x_206);
lean_dec(x_62);
x_32 = x_203;
x_33 = x_207;
goto block_37;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_62);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_222 = lean_ctor_get(x_199, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_199, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_224 = x_199;
} else {
 lean_dec_ref(x_199);
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
}
}
else
{
uint8_t x_226; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_226 = !lean_is_exclusive(x_61);
if (x_226 == 0)
{
return x_61;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = lean_ctor_get(x_61, 0);
x_228 = lean_ctor_get(x_61, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_61);
x_229 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
return x_229;
}
}
}
else
{
uint8_t x_230; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_230 = !lean_is_exclusive(x_47);
if (x_230 == 0)
{
return x_47;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_47, 0);
x_232 = lean_ctor_get(x_47, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_47);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
block_37:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_nat_add(x_17, x_29);
lean_dec(x_17);
x_35 = lean_array_push(x_19, x_32);
x_16 = x_30;
x_17 = x_34;
x_18 = lean_box(0);
x_19 = x_35;
x_26 = x_33;
goto _start;
}
}
else
{
lean_object* x_234; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_19);
lean_ctor_set(x_234, 1, x_26);
return x_234;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_8, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_8, x_21);
lean_dec(x_8);
x_23 = lean_array_fget(x_7, x_9);
x_24 = lean_box(0);
lean_inc(x_6);
x_25 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_6, x_24);
lean_inc(x_5);
x_26 = l_Lean_Expr_const___override(x_5, x_25);
x_27 = l_Lean_mkAppN(x_26, x_3);
lean_inc(x_4);
lean_inc(x_9);
lean_inc(x_2);
x_28 = l_Lean_Meta_PProdN_proj(x_2, x_9, x_4, x_27);
x_29 = 0;
x_30 = 1;
x_31 = 1;
x_32 = l_Lean_Meta_mkLambdaFVars(x_3, x_28, x_29, x_30, x_29, x_31, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_23, 5);
lean_dec(x_36);
lean_ctor_set(x_23, 5, x_33);
x_37 = lean_nat_add(x_9, x_21);
lean_dec(x_9);
x_38 = lean_array_push(x_11, x_23);
x_8 = x_22;
x_9 = x_37;
x_10 = lean_box(0);
x_11 = x_38;
x_18 = x_34;
goto _start;
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_23, 0);
x_41 = lean_ctor_get_uint8(x_23, sizeof(void*)*7);
x_42 = lean_ctor_get(x_23, 1);
x_43 = lean_ctor_get(x_23, 2);
x_44 = lean_ctor_get(x_23, 3);
x_45 = lean_ctor_get(x_23, 4);
x_46 = lean_ctor_get(x_23, 6);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_40);
lean_dec(x_23);
x_47 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set(x_47, 2, x_43);
lean_ctor_set(x_47, 3, x_44);
lean_ctor_set(x_47, 4, x_45);
lean_ctor_set(x_47, 5, x_33);
lean_ctor_set(x_47, 6, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*7, x_41);
x_48 = lean_nat_add(x_9, x_21);
lean_dec(x_9);
x_49 = lean_array_push(x_11, x_47);
x_8 = x_22;
x_9 = x_48;
x_10 = lean_box(0);
x_11 = x_49;
x_18 = x_34;
goto _start;
}
}
else
{
uint8_t x_51; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_32);
if (x_51 == 0)
{
return x_32;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_32, 0);
x_53 = lean_ctor_get(x_32, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_32);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_11);
lean_ctor_set(x_55, 1, x_18);
return x_55;
}
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mutual", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_partialFixpoint___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; 
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_dec_eq(x_5, x_98);
x_100 = 0;
x_101 = 1;
x_102 = 1;
lean_inc(x_6);
x_103 = l_Lean_Meta_mkForallFVars(x_1, x_6, x_100, x_101, x_102, x_12, x_13, x_14, x_15, x_16);
if (x_99 == 0)
{
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_3, 3);
lean_inc(x_106);
x_107 = l_Lean_Elab_partialFixpoint___lambda__1___closed__2;
x_108 = l_Lean_Name_append(x_106, x_107);
x_17 = x_108;
x_18 = x_104;
x_19 = x_105;
goto block_97;
}
else
{
uint8_t x_109; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_103);
if (x_109 == 0)
{
return x_103;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_103, 0);
x_111 = lean_ctor_get(x_103, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_103);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_103, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_103, 1);
lean_inc(x_114);
lean_dec(x_103);
x_115 = lean_ctor_get(x_3, 3);
lean_inc(x_115);
x_17 = x_115;
x_18 = x_113;
x_19 = x_114;
goto block_97;
}
else
{
uint8_t x_116; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_103);
if (x_116 == 0)
{
return x_103;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_103, 0);
x_118 = lean_ctor_get(x_103, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_103);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
block_97:
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_20 = 0;
x_21 = 1;
x_22 = 1;
x_23 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_20, x_21, x_20, x_22, x_12, x_13, x_14, x_15, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_3);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_3, 1);
x_28 = lean_ctor_get(x_3, 5);
lean_dec(x_28);
x_29 = lean_ctor_get(x_3, 4);
lean_dec(x_29);
x_30 = lean_ctor_get(x_3, 3);
lean_dec(x_30);
lean_inc(x_17);
lean_inc(x_27);
lean_ctor_set(x_3, 5, x_24);
lean_ctor_set(x_3, 4, x_18);
lean_ctor_set(x_3, 3, x_17);
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
lean_inc(x_5);
x_32 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__17(x_4, x_5, x_1, x_6, x_17, x_27, x_4, x_5, x_31, lean_box(0), x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_35 = l_Lean_Elab_Mutual_addPreDefsFromUnary(x_4, x_33, x_3, x_10, x_11, x_12, x_13, x_14, x_15, x_34);
lean_dec(x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_37 = l_Lean_Elab_Mutual_cleanPreDefs(x_4, x_10, x_11, x_12, x_13, x_14, x_15, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_38);
x_40 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(x_38, x_17, x_8, x_12, x_13, x_14, x_15, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Elab_Mutual_addPreDefAttributes(x_38, x_10, x_11, x_12, x_13, x_14, x_15, x_41);
lean_dec(x_38);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_38);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
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
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
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
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
return x_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
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
lean_dec(x_3);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_32);
if (x_55 == 0)
{
return x_32;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_32, 0);
x_57 = lean_ctor_get(x_32, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_32);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_3, 0);
x_60 = lean_ctor_get_uint8(x_3, sizeof(void*)*7);
x_61 = lean_ctor_get(x_3, 1);
x_62 = lean_ctor_get(x_3, 2);
x_63 = lean_ctor_get(x_3, 6);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_59);
lean_dec(x_3);
lean_inc(x_17);
lean_inc(x_61);
x_64 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_61);
lean_ctor_set(x_64, 2, x_62);
lean_ctor_set(x_64, 3, x_17);
lean_ctor_set(x_64, 4, x_18);
lean_ctor_set(x_64, 5, x_24);
lean_ctor_set(x_64, 6, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*7, x_60);
x_65 = lean_unsigned_to_nat(0u);
lean_inc(x_17);
lean_inc(x_5);
x_66 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__17(x_4, x_5, x_1, x_6, x_17, x_61, x_4, x_5, x_65, lean_box(0), x_7, x_10, x_11, x_12, x_13, x_14, x_15, x_25);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_4);
x_69 = l_Lean_Elab_Mutual_addPreDefsFromUnary(x_4, x_67, x_64, x_10, x_11, x_12, x_13, x_14, x_15, x_68);
lean_dec(x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_71 = l_Lean_Elab_Mutual_cleanPreDefs(x_4, x_10, x_11, x_12, x_13, x_14, x_15, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_72);
x_74 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo(x_72, x_17, x_8, x_12, x_13, x_14, x_15, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Elab_Mutual_addPreDefAttributes(x_72, x_10, x_11, x_12, x_13, x_14, x_15, x_75);
lean_dec(x_72);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_72);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_77 = lean_ctor_get(x_74, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_79 = x_74;
} else {
 lean_dec_ref(x_74);
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
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_71, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_83 = x_71;
} else {
 lean_dec_ref(x_71);
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
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
x_85 = lean_ctor_get(x_69, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_69, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_87 = x_69;
} else {
 lean_dec_ref(x_69);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_64);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_4);
x_89 = lean_ctor_get(x_66, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_66, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_91 = x_66;
} else {
 lean_dec_ref(x_66);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_23);
if (x_93 == 0)
{
return x_23;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_23, 0);
x_95 = lean_ctor_get(x_23, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_23);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_mkInstCCPOPProd), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toPartialOrder", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__2;
x_3 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__1;
x_4 = l_Lean_Elab_partialFixpoint___lambda__2___closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_mkMonoPProd), 7, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__2;
x_3 = l_Lean_Elab_partialFixpoint___lambda__2___closed__5;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packedValue: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_partialFixpoint___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
size_t x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_array_size(x_1);
lean_inc(x_14);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__5(x_14, x_23, x_2, x_1);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_4);
x_25 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__6(x_14, x_3, x_2, x_4, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3___closed__1;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_26);
x_29 = l_Lean_Meta_PProdN_pack(x_28, x_26, x_18, x_19, x_20, x_21, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_array_size(x_24);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_33 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8(x_2, x_32, x_2, x_24, x_16, x_17, x_18, x_19, x_20, x_21, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Lean_instInhabitedExpr;
x_37 = l_Lean_Elab_partialFixpoint___lambda__2___closed__1;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_34);
x_38 = l_Lean_Meta_PProdN_genMk___rarg(x_36, x_37, x_34, x_18, x_19, x_20, x_21, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
x_43 = lean_box(0);
lean_inc(x_42);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_array_mk(x_45);
x_47 = l_Lean_Elab_partialFixpoint___lambda__2___closed__3;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_48 = l_Lean_Meta_mkAppOptM(x_47, x_46, x_18, x_19, x_20, x_21, x_40);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_n(x_4, 2);
x_51 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10(x_4, x_5, x_6, x_2, x_7, x_14, x_30, x_3, x_2, x_4, x_16, x_17, x_18, x_19, x_20, x_21, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unsigned_to_nat(0u);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_30);
lean_inc(x_14);
lean_inc(x_9);
lean_inc(x_4);
x_55 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16(x_4, x_8, x_9, x_10, x_10, x_11, x_14, x_26, x_30, x_34, x_47, x_43, x_49, x_52, x_4, x_5, x_54, lean_box(0), x_12, x_16, x_17, x_18, x_19, x_20, x_21, x_53);
lean_dec(x_52);
lean_dec(x_34);
lean_dec(x_26);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Elab_partialFixpoint___lambda__2___closed__4;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_59 = l_Lean_Meta_PProdN_genMk___rarg(x_36, x_58, x_56, x_18, x_19, x_20, x_21, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_30);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_30);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_43);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_41);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_42);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_mk(x_67);
x_69 = l_Lean_Elab_partialFixpoint___lambda__2___closed__6;
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_70 = l_Lean_Meta_mkAppOptM(x_69, x_68, x_18, x_19, x_20, x_21, x_61);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
lean_inc(x_9);
x_73 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_9, x_16, x_17, x_18, x_19, x_20, x_21, x_72);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_9);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_box(0);
x_78 = l_Lean_Elab_partialFixpoint___lambda__1(x_14, x_71, x_13, x_4, x_5, x_30, x_12, x_6, x_77, x_16, x_17, x_18, x_19, x_20, x_21, x_76);
lean_dec(x_14);
return x_78;
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_73);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_73, 1);
x_81 = lean_ctor_get(x_73, 0);
lean_dec(x_81);
lean_inc(x_71);
x_82 = l_Lean_MessageData_ofExpr(x_71);
x_83 = l_Lean_Elab_partialFixpoint___lambda__2___closed__8;
lean_ctor_set_tag(x_73, 7);
lean_ctor_set(x_73, 1, x_82);
lean_ctor_set(x_73, 0, x_83);
x_84 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_85 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_9, x_85, x_16, x_17, x_18, x_19, x_20, x_21, x_80);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Elab_partialFixpoint___lambda__1(x_14, x_71, x_13, x_4, x_5, x_30, x_12, x_6, x_87, x_16, x_17, x_18, x_19, x_20, x_21, x_88);
lean_dec(x_87);
lean_dec(x_14);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_90 = lean_ctor_get(x_73, 1);
lean_inc(x_90);
lean_dec(x_73);
lean_inc(x_71);
x_91 = l_Lean_MessageData_ofExpr(x_71);
x_92 = l_Lean_Elab_partialFixpoint___lambda__2___closed__8;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
x_94 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_9, x_95, x_16, x_17, x_18, x_19, x_20, x_21, x_90);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Elab_partialFixpoint___lambda__1(x_14, x_71, x_13, x_4, x_5, x_30, x_12, x_6, x_97, x_16, x_17, x_18, x_19, x_20, x_21, x_98);
lean_dec(x_97);
lean_dec(x_14);
return x_99;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_100 = !lean_is_exclusive(x_70);
if (x_100 == 0)
{
return x_70;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_70, 0);
x_102 = lean_ctor_get(x_70, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_70);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_42);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_104 = !lean_is_exclusive(x_59);
if (x_104 == 0)
{
return x_59;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_59, 0);
x_106 = lean_ctor_get(x_59, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_59);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_42);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = !lean_is_exclusive(x_55);
if (x_108 == 0)
{
return x_55;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_55, 0);
x_110 = lean_ctor_get(x_55, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_55);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_49);
lean_dec(x_42);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = !lean_is_exclusive(x_51);
if (x_112 == 0)
{
return x_51;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_51, 0);
x_114 = lean_ctor_get(x_51, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_51);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_42);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = !lean_is_exclusive(x_48);
if (x_116 == 0)
{
return x_48;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_48, 0);
x_118 = lean_ctor_get(x_48, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_48);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_120 = !lean_is_exclusive(x_38);
if (x_120 == 0)
{
return x_38;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_38, 0);
x_122 = lean_ctor_get(x_38, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_38);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_124 = !lean_is_exclusive(x_33);
if (x_124 == 0)
{
return x_33;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_33, 0);
x_126 = lean_ctor_get(x_33, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_33);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_128 = !lean_is_exclusive(x_29);
if (x_128 == 0)
{
return x_29;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_29, 0);
x_130 = lean_ctor_get(x_29, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_29);
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
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_132 = !lean_is_exclusive(x_25);
if (x_132 == 0)
{
return x_25;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_25, 0);
x_134 = lean_ctor_get(x_25, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_25);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lambda__2), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instMonadControlReaderT___lambda__3___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_partialFixpoint___lambda__3___closed__1;
x_2 = l_Lean_Elab_partialFixpoint___lambda__3___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_instMonadCoreM;
x_2 = l_ReaderT_instMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_partialFixpoint___lambda__3___closed__4;
x_2 = l_ReaderT_instApplicativeOfMonad___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_partialFixpoint___lambda__3___closed__5;
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_3 = l_instMonadControlTOfPure___rarg(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_partialFixpoint___lambda__3___closed__3;
x_2 = l_Lean_Elab_partialFixpoint___lambda__3___closed__6;
x_3 = l_instMonadControlTOfMonadControl___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_partialFixpoint___lambda__3___closed__3;
x_2 = l_Lean_Elab_partialFixpoint___lambda__3___closed__7;
x_3 = l_instMonadControlTOfMonadControl___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___lambda__3___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_16 = lean_array_size(x_1);
x_17 = 0;
lean_inc(x_1);
x_18 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2(x_16, x_17, x_1);
x_19 = l_Lean_Elab_instInhabitedPreDefinition;
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get(x_19, x_1, x_20);
x_22 = lean_ctor_get(x_21, 4);
lean_inc(x_22);
lean_inc(x_2);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = l_Lean_Elab_partialFixpoint___lambda__3___closed__3;
x_25 = l_Lean_Elab_partialFixpoint___lambda__3___closed__8;
x_26 = l_Lean_Elab_partialFixpoint___lambda__3___boxed__const__1;
x_27 = lean_box_usize(x_16);
x_28 = lean_alloc_closure((void*)(l_Lean_Elab_partialFixpoint___lambda__2___boxed), 22, 13);
lean_closure_set(x_28, 0, x_3);
lean_closure_set(x_28, 1, x_26);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_1);
lean_closure_set(x_28, 4, x_4);
lean_closure_set(x_28, 5, x_2);
lean_closure_set(x_28, 6, x_18);
lean_closure_set(x_28, 7, x_5);
lean_closure_set(x_28, 8, x_6);
lean_closure_set(x_28, 9, x_24);
lean_closure_set(x_28, 10, x_25);
lean_closure_set(x_28, 11, x_7);
lean_closure_set(x_28, 12, x_21);
x_29 = 0;
x_30 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Elab_Term_addAutoBoundImplicits_x27___spec__2___rarg(x_22, x_23, x_28, x_29, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_30;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assertion violation: ", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("preDefs.size = hints.size\n  -- For every function of type `∀ x y, r x y`, an CCPO instance\n  -- ∀ x y, CCPO (r x y), but crucially constructed using `instCCPOPi`\n  ", 168, 164);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_partialFixpoint___closed__1;
x_2 = l_Lean_Elab_partialFixpoint___closed__2;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__1;
x_2 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(66u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_Lean_Elab_partialFixpoint___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fixed prefix size: ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_partialFixpoint___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_partialFixpoint___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_array_get_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1(x_1, x_10, x_9);
x_12 = lean_array_get_size(x_11);
x_13 = lean_nat_dec_eq(x_9, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_1);
x_14 = l_Lean_Elab_partialFixpoint___closed__4;
x_15 = l_panic___at_Lean_Elab_Term_reportStuckSyntheticMVar___spec__1(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_mk_empty_array_with_capacity(x_9);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_16);
lean_inc(x_9);
x_17 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4(x_1, x_11, x_1, x_9, x_10, lean_box(0), x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_20 = l_Lean_Elab_Mutual_getFixedPrefix(x_1, x_4, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__6;
x_24 = l_Lean_isTracingEnabledFor___at_Lean_Elab_Term_traceAtCmdPos___spec__1(x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_22);
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
x_29 = l_Lean_Elab_partialFixpoint___lambda__3(x_1, x_21, x_18, x_9, x_11, x_23, x_16, x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_27);
return x_29;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_24);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_31 = lean_ctor_get(x_24, 1);
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
lean_inc(x_21);
x_33 = l___private_Init_Data_Repr_0__Nat_reprFast(x_21);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_MessageData_ofFormat(x_34);
x_36 = l_Lean_Elab_partialFixpoint___closed__6;
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_35);
lean_ctor_set(x_24, 0, x_36);
x_37 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_23, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_31);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_partialFixpoint___lambda__3(x_1, x_21, x_18, x_9, x_11, x_23, x_16, x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_40);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_dec(x_24);
lean_inc(x_21);
x_44 = l___private_Init_Data_Repr_0__Nat_reprFast(x_21);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = l_Lean_MessageData_ofFormat(x_45);
x_47 = l_Lean_Elab_partialFixpoint___closed__6;
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_49 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4;
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_addTrace___at_Lean_Elab_Term_traceAtCmdPos___spec__2(x_23, x_50, x_2, x_3, x_4, x_5, x_6, x_7, x_43);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Elab_partialFixpoint___lambda__3(x_1, x_21, x_18, x_9, x_11, x_23, x_16, x_52, x_2, x_3, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_20);
if (x_55 == 0)
{
return x_20;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_20, 0);
x_57 = lean_ctor_get(x_20, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_20);
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
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_17);
if (x_59 == 0)
{
return x_17;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_17, 0);
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_17);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_lambdaTelescope___at_Lean_Elab_partialFixpoint___spec__3___rarg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__5(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__6(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; lean_object* x_12; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8___lambda__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__8(x_12, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_partialFixpoint___spec__9(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; lean_object* x_16; 
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___lambda__1(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___boxed(lean_object** _args) {
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
size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_19 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_20 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_21 = l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10(x_1, x_2, x_3, x_18, x_5, x_6, x_7, x_19, x_20, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_6);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__12___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__14___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__14___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Elab_partialFixpoint___spec__15___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___boxed(lean_object** _args) {
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
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
lean_object* x_26 = _args[25];
_start:
{
lean_object* x_27; 
x_27 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__17___boxed(lean_object** _args) {
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
x_19 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__17(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_Elab_partialFixpoint___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_9);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__2___boxed(lean_object** _args) {
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
lean_object* x_21 = _args[20];
lean_object* x_22 = _args[21];
_start:
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_24 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_25 = l_Lean_Elab_partialFixpoint___lambda__2(x_1, x_23, x_24, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_partialFixpoint___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Elab_partialFixpoint___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
return x_16;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__2;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__4;
x_2 = l_Lean_Elab_mkInstCCPOPProd___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__5;
x_2 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PreDefinition", 13, 13);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__6;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PartialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__8;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__10;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__12;
x_2 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__14;
x_2 = lean_unsigned_to_nat(2833u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__6;
x_3 = 0;
x_4 = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__15;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Elab_PreDefinition_MkInhabitant(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Monotonicity(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_PProdN(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_MkInhabitant(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Mutual(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Monotonicity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_PProdN(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___lambda__3___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__2 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__2);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__3 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__3);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Main_0__Lean_Elab_unReplaceRecApps___rarg___closed__4);
l_Lean_Elab_mkInstCCPOPProd___closed__1 = _init_l_Lean_Elab_mkInstCCPOPProd___closed__1();
lean_mark_persistent(l_Lean_Elab_mkInstCCPOPProd___closed__1);
l_Lean_Elab_mkInstCCPOPProd___closed__2 = _init_l_Lean_Elab_mkInstCCPOPProd___closed__2();
lean_mark_persistent(l_Lean_Elab_mkInstCCPOPProd___closed__2);
l_Lean_Elab_mkInstCCPOPProd___closed__3 = _init_l_Lean_Elab_mkInstCCPOPProd___closed__3();
lean_mark_persistent(l_Lean_Elab_mkInstCCPOPProd___closed__3);
l_Lean_Elab_mkInstCCPOPProd___closed__4 = _init_l_Lean_Elab_mkInstCCPOPProd___closed__4();
lean_mark_persistent(l_Lean_Elab_mkInstCCPOPProd___closed__4);
l_Lean_Elab_mkMonoPProd___lambda__1___closed__1 = _init_l_Lean_Elab_mkMonoPProd___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_mkMonoPProd___lambda__1___closed__1);
l_Lean_Elab_mkMonoPProd___lambda__1___closed__2 = _init_l_Lean_Elab_mkMonoPProd___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_mkMonoPProd___lambda__1___closed__2);
l_Lean_Elab_mkMonoPProd___lambda__1___closed__3 = _init_l_Lean_Elab_mkMonoPProd___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_mkMonoPProd___lambda__1___closed__3);
l_Lean_Elab_mkMonoPProd___lambda__2___closed__1 = _init_l_Lean_Elab_mkMonoPProd___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_mkMonoPProd___lambda__2___closed__1);
l_Lean_Elab_mkMonoPProd___lambda__2___closed__2 = _init_l_Lean_Elab_mkMonoPProd___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_mkMonoPProd___lambda__2___closed__2);
l_Lean_Elab_mkMonoPProd___lambda__3___closed__1 = _init_l_Lean_Elab_mkMonoPProd___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_mkMonoPProd___lambda__3___closed__1);
l_Lean_Elab_mkMonoPProd___lambda__3___closed__2 = _init_l_Lean_Elab_mkMonoPProd___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_mkMonoPProd___lambda__3___closed__2);
l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___closed__1 = _init_l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___closed__1();
lean_mark_persistent(l_Array_filterMapM___at_Lean_Elab_partialFixpoint___spec__1___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__2);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__3 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__3();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__3);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__4 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__4();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__4);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__5 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__5();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__5);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__6 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__6();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__6);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__7 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__7();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__7);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__8 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__8();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__8);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__9 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__9();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__9);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__10 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__10();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__10);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__11 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__11();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__11);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__12 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__12();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__12);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__13 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__13();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__2___closed__13);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__2);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__3 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__3();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__3);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__4 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__4();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__4);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__5 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__5();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__5);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__6 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__6();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__6);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__7 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__7();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__7);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__8 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__8();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__8);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__9 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__9();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__9);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__10 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__10();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__4___lambda__3___closed__10);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Elab_partialFixpoint___spec__7___closed__2);
l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__1);
l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lean_Elab_partialFixpoint___spec__10___closed__2);
l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg___closed__1 = _init_l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg___closed__1();
lean_mark_persistent(l_panic___at_Lean_Elab_partialFixpoint___spec__11___rarg___closed__1);
l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__1 = _init_l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__1();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__1);
l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__2 = _init_l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__2();
lean_mark_persistent(l_List_mapTR_loop___at_Lean_Elab_partialFixpoint___spec__13___closed__2);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__2);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__3 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__3();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__3);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__4 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__4();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__4);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__5 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__5();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__5);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__6 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__6();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__6);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__7 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__7();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__7);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__8 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__8();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__8);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__9 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__9();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__9);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__10 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__10();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__10);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__11 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__11();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__11);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__12 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__12();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__12);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__13 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__13();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__13);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__14 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__14();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__14);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__15 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__15();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__15);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__16 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__16();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__16);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__17 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__17();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__17);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__18 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__18();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__18);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__19 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__19();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__19);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__20 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__20();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__20);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__21 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__21();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__21);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__22 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__22();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__1___closed__22);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__2);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__3 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__3();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__3);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__4 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__4();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___lambda__3___closed__4);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__1 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__1();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__1);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__2 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__2();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__2);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__3 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__3();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__3);
l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__4 = _init_l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__4();
lean_mark_persistent(l_Array_mapFinIdxM_map___at_Lean_Elab_partialFixpoint___spec__16___closed__4);
l_Lean_Elab_partialFixpoint___lambda__1___closed__1 = _init_l_Lean_Elab_partialFixpoint___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__1___closed__1);
l_Lean_Elab_partialFixpoint___lambda__1___closed__2 = _init_l_Lean_Elab_partialFixpoint___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__1___closed__2);
l_Lean_Elab_partialFixpoint___lambda__2___closed__1 = _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__2___closed__1);
l_Lean_Elab_partialFixpoint___lambda__2___closed__2 = _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__2___closed__2);
l_Lean_Elab_partialFixpoint___lambda__2___closed__3 = _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__2___closed__3);
l_Lean_Elab_partialFixpoint___lambda__2___closed__4 = _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__2___closed__4);
l_Lean_Elab_partialFixpoint___lambda__2___closed__5 = _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__2___closed__5);
l_Lean_Elab_partialFixpoint___lambda__2___closed__6 = _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__2___closed__6);
l_Lean_Elab_partialFixpoint___lambda__2___closed__7 = _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__2___closed__7);
l_Lean_Elab_partialFixpoint___lambda__2___closed__8 = _init_l_Lean_Elab_partialFixpoint___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__2___closed__8);
l_Lean_Elab_partialFixpoint___lambda__3___closed__1 = _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__3___closed__1);
l_Lean_Elab_partialFixpoint___lambda__3___closed__2 = _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__3___closed__2);
l_Lean_Elab_partialFixpoint___lambda__3___closed__3 = _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__3___closed__3);
l_Lean_Elab_partialFixpoint___lambda__3___closed__4 = _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__3___closed__4);
l_Lean_Elab_partialFixpoint___lambda__3___closed__5 = _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__3___closed__5);
l_Lean_Elab_partialFixpoint___lambda__3___closed__6 = _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__3___closed__6);
l_Lean_Elab_partialFixpoint___lambda__3___closed__7 = _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__3___closed__7);
l_Lean_Elab_partialFixpoint___lambda__3___closed__8 = _init_l_Lean_Elab_partialFixpoint___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__3___closed__8);
l_Lean_Elab_partialFixpoint___lambda__3___boxed__const__1 = _init_l_Lean_Elab_partialFixpoint___lambda__3___boxed__const__1();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___lambda__3___boxed__const__1);
l_Lean_Elab_partialFixpoint___closed__1 = _init_l_Lean_Elab_partialFixpoint___closed__1();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___closed__1);
l_Lean_Elab_partialFixpoint___closed__2 = _init_l_Lean_Elab_partialFixpoint___closed__2();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___closed__2);
l_Lean_Elab_partialFixpoint___closed__3 = _init_l_Lean_Elab_partialFixpoint___closed__3();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___closed__3);
l_Lean_Elab_partialFixpoint___closed__4 = _init_l_Lean_Elab_partialFixpoint___closed__4();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___closed__4);
l_Lean_Elab_partialFixpoint___closed__5 = _init_l_Lean_Elab_partialFixpoint___closed__5();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___closed__5);
l_Lean_Elab_partialFixpoint___closed__6 = _init_l_Lean_Elab_partialFixpoint___closed__6();
lean_mark_persistent(l_Lean_Elab_partialFixpoint___closed__6);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__1 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__1();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__1);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__2 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__2();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__2);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__3 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__3();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__3);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__4 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__4();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__4);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__5 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__5();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__5);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__6 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__6();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__6);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__7 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__7();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__7);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__8 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__8();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__8);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__9 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__9();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__9);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__10 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__10();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__10);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__11 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__11();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__11);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__12 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__12();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__12);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__13 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__13();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__13);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__14 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__14();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__14);
l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__15 = _init_l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__15();
lean_mark_persistent(l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833____closed__15);
if (builtin) {res = l_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Main___hyg_2833_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
