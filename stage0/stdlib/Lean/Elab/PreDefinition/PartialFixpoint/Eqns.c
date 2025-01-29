// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Eqns
// Imports: Lean.Elab.Tactic.Conv Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Split Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Eqns Lean.Meta.ArgsPacker.Basic Init.Data.Array.Basic Init.Internal.Order.Basic
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__5;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__4;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__2;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17;
extern lean_object* l_Lean_Meta_tactic_hygienic;
static lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___closed__5;
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1(lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
static lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___closed__4;
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__3;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___closed__3;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296_(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__1;
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_Option_set___at_Lean_Meta_getEqnsFor_x3f___spec__1(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__2;
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Elab_Eqns_mkEqnTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__5;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__6;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_eqnThmSuffixBase;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3;
lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__8;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__7;
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__2;
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__6;
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__3;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Meta_subst_substEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19;
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2;
x_2 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3;
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_name_eq(x_3, x_1);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = lean_name_eq(x_3, x_2);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("deltaLHSUntilFix", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality expected", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_MVarId_getType_x27(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__2;
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity(x_10, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_15 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__4;
x_16 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__8;
x_17 = l_Lean_Meta_throwTacticEx___rarg(x_15, x_1, x_16, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lean_Expr_appFn_x21(x_10);
x_19 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_20 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1___boxed), 3, 2);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_3);
lean_inc(x_7);
lean_inc(x_6);
x_22 = l_Lean_Meta_deltaExpand(x_19, x_21, x_6, x_7, x_11);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l_Lean_Meta_mkEq(x_23, x_20, x_4, x_5, x_6, x_7, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_26, x_4, x_5, x_6, x_7, x_27);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
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
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_22);
if (x_33 == 0)
{
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
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
uint8_t x_37; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_9);
if (x_37 == 0)
{
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_9, 0);
x_39 = lean_ctor_get(x_9, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_9);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2), 8, 3);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_3, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Order", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rwFixUnder: unexpected expression ", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("p", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
x_3 = lean_unsigned_to_nat(1769u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static size_t _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1;
x_2 = lean_ptr_addr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrFun", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix_eq", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Expr_isApp(x_1);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_isProj(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lean_MessageData_ofExpr(x_1);
x_13 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_16, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_Expr_projExpr_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_18);
x_19 = lean_infer_type(x_18, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Elab_PartialFixpoint_rwFixUnder(x_18, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; size_t x_43; size_t x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
x_43 = lean_ptr_addr(x_42);
lean_dec(x_42);
x_44 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17;
x_45 = lean_usize_dec_eq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_46 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1;
x_47 = l_Lean_Expr_proj___override(x_40, x_41, x_46);
x_23 = x_47;
goto block_39;
}
else
{
lean_dec(x_41);
lean_dec(x_40);
x_23 = x_1;
goto block_39;
}
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
x_49 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_48);
x_23 = x_49;
goto block_39;
}
block_39:
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
x_27 = 0;
x_28 = l_Lean_Expr_lam___override(x_26, x_20, x_23, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_mk(x_31);
x_33 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
x_34 = l_Lean_Meta_mkAppM(x_33, x_32, x_2, x_3, x_4, x_5, x_25);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
else
{
uint8_t x_50; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_19);
if (x_50 == 0)
{
return x_19;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_19, 0);
x_52 = lean_ctor_get(x_19, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_19);
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
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_55 = l_Lean_Elab_PartialFixpoint_rwFixUnder(x_54, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_array_mk(x_61);
x_63 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19;
x_64 = l_Lean_Meta_mkAppM(x_63, x_62, x_2, x_3, x_4, x_5, x_57);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_55);
if (x_65 == 0)
{
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_55, 0);
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_55);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = l_Lean_Expr_getAppFn(x_1);
x_70 = l_Lean_Expr_constLevels_x21(x_69);
lean_dec(x_69);
x_71 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
x_72 = l_Lean_Expr_const___override(x_71, x_70);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_73);
x_75 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22;
lean_inc(x_74);
x_76 = lean_mk_array(x_74, x_75);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_sub(x_74, x_77);
lean_dec(x_74);
x_79 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_76, x_78);
x_80 = l_Lean_mkAppN(x_72, x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_6);
return x_81;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.PartialFixpoint.Eqns", 44, 44);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.PreDefinition.PartialFixpoint.Eqns.0.Lean.Elab.PartialFixpoint.rwFixEq", 89, 89);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(48u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(50u);
x_4 = lean_unsigned_to_nat(51u);
x_5 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType_x27(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__2;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__4;
x_14 = l_panic___at_Lean_Meta_subst_substEq___spec__1(x_13, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = l_Lean_Expr_appFn_x21(x_8);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec(x_15);
x_17 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Elab_PartialFixpoint_rwFixUnder(x_16, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_19);
x_21 = lean_infer_type(x_19, x_2, x_3, x_4, x_5, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_isAppOfArity(x_22, x_10, x_11);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_1);
x_25 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__5;
x_26 = l_panic___at_Lean_Meta_subst_substEq___spec__1(x_25, x_2, x_3, x_4, x_5, x_23);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l_Lean_Meta_mkEq(x_27, x_17, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_box(0);
lean_inc(x_2);
x_32 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_29, x_31, x_2, x_3, x_4, x_5, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_33);
x_35 = l_Lean_Meta_mkEqTrans(x_19, x_33, x_2, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_36, x_2, x_3, x_4, x_5, x_37);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = l_Lean_Expr_mvarId_x21(x_33);
lean_dec(x_33);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lean_Expr_mvarId_x21(x_33);
lean_dec(x_33);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_35);
if (x_45 == 0)
{
return x_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_35, 0);
x_47 = lean_ctor_get(x_35, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_35);
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
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_28);
if (x_49 == 0)
{
return x_28;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_28, 0);
x_51 = lean_ctor_get(x_28, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_28);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_57; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_18);
if (x_57 == 0)
{
return x_18;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_18, 0);
x_59 = lean_ctor_get(x_18, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_18);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_7);
if (x_61 == 0)
{
return x_7;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_7, 0);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_7);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to generate equational theorem for '", 43, 43);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static uint64_t _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__5() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_box(0);
lean_inc(x_4);
x_10 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_14 = l_Lean_Expr_mvarId_x21(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_MVarId_intros(x_14, x_4, x_5, x_6, x_7, x_12);
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
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_20 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(x_2, x_3, x_18, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(x_21, x_4, x_5, x_6, x_7, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_40; uint64_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_40 = lean_ctor_get(x_4, 0);
lean_inc(x_40);
x_41 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_42 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_43 = lean_ctor_get(x_4, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_4, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_4, 3);
lean_inc(x_45);
x_46 = lean_ctor_get(x_4, 4);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 5);
lean_inc(x_47);
x_48 = lean_ctor_get(x_4, 6);
lean_inc(x_48);
x_49 = !lean_is_exclusive(x_40);
if (x_49 == 0)
{
uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; 
x_50 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_51 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_52 = lean_ctor_get_uint8(x_40, 9);
x_53 = 0;
x_54 = l_Lean_Meta_TransparencyMode_lt(x_52, x_53);
x_55 = 2;
x_56 = lean_uint64_shift_right(x_41, x_55);
x_57 = lean_uint64_shift_left(x_56, x_55);
if (x_54 == 0)
{
uint64_t x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = l_Lean_Meta_TransparencyMode_toUInt64(x_52);
x_59 = lean_uint64_lor(x_57, x_58);
x_60 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_60, 0, x_40);
lean_ctor_set(x_60, 1, x_43);
lean_ctor_set(x_60, 2, x_44);
lean_ctor_set(x_60, 3, x_45);
lean_ctor_set(x_60, 4, x_46);
lean_ctor_set(x_60, 5, x_47);
lean_ctor_set(x_60, 6, x_48);
lean_ctor_set_uint64(x_60, sizeof(void*)*7, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 8, x_42);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 9, x_50);
lean_ctor_set_uint8(x_60, sizeof(void*)*7 + 10, x_51);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
x_61 = l_Lean_Elab_Eqns_tryURefl(x_24, x_60, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unbox(x_62);
lean_dec(x_62);
x_26 = x_64;
x_27 = x_63;
goto block_39;
}
else
{
uint8_t x_65; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_61);
if (x_65 == 0)
{
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint64_t x_69; uint64_t x_70; lean_object* x_71; lean_object* x_72; 
lean_ctor_set_uint8(x_40, 9, x_53);
x_69 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__5;
x_70 = lean_uint64_lor(x_57, x_69);
x_71 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_71, 0, x_40);
lean_ctor_set(x_71, 1, x_43);
lean_ctor_set(x_71, 2, x_44);
lean_ctor_set(x_71, 3, x_45);
lean_ctor_set(x_71, 4, x_46);
lean_ctor_set(x_71, 5, x_47);
lean_ctor_set(x_71, 6, x_48);
lean_ctor_set_uint64(x_71, sizeof(void*)*7, x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 8, x_42);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 9, x_50);
lean_ctor_set_uint8(x_71, sizeof(void*)*7 + 10, x_51);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
x_72 = l_Lean_Elab_Eqns_tryURefl(x_24, x_71, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_26 = x_75;
x_27 = x_74;
goto block_39;
}
else
{
uint8_t x_76; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_72);
if (x_76 == 0)
{
return x_72;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_72, 0);
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_72);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; 
x_80 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_81 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_82 = lean_ctor_get_uint8(x_40, 0);
x_83 = lean_ctor_get_uint8(x_40, 1);
x_84 = lean_ctor_get_uint8(x_40, 2);
x_85 = lean_ctor_get_uint8(x_40, 3);
x_86 = lean_ctor_get_uint8(x_40, 4);
x_87 = lean_ctor_get_uint8(x_40, 5);
x_88 = lean_ctor_get_uint8(x_40, 6);
x_89 = lean_ctor_get_uint8(x_40, 7);
x_90 = lean_ctor_get_uint8(x_40, 8);
x_91 = lean_ctor_get_uint8(x_40, 9);
x_92 = lean_ctor_get_uint8(x_40, 10);
x_93 = lean_ctor_get_uint8(x_40, 11);
x_94 = lean_ctor_get_uint8(x_40, 12);
x_95 = lean_ctor_get_uint8(x_40, 13);
x_96 = lean_ctor_get_uint8(x_40, 14);
x_97 = lean_ctor_get_uint8(x_40, 15);
x_98 = lean_ctor_get_uint8(x_40, 16);
x_99 = lean_ctor_get_uint8(x_40, 17);
lean_dec(x_40);
x_100 = 0;
x_101 = l_Lean_Meta_TransparencyMode_lt(x_91, x_100);
x_102 = 2;
x_103 = lean_uint64_shift_right(x_41, x_102);
x_104 = lean_uint64_shift_left(x_103, x_102);
if (x_101 == 0)
{
lean_object* x_105; uint64_t x_106; uint64_t x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_105, 0, x_82);
lean_ctor_set_uint8(x_105, 1, x_83);
lean_ctor_set_uint8(x_105, 2, x_84);
lean_ctor_set_uint8(x_105, 3, x_85);
lean_ctor_set_uint8(x_105, 4, x_86);
lean_ctor_set_uint8(x_105, 5, x_87);
lean_ctor_set_uint8(x_105, 6, x_88);
lean_ctor_set_uint8(x_105, 7, x_89);
lean_ctor_set_uint8(x_105, 8, x_90);
lean_ctor_set_uint8(x_105, 9, x_91);
lean_ctor_set_uint8(x_105, 10, x_92);
lean_ctor_set_uint8(x_105, 11, x_93);
lean_ctor_set_uint8(x_105, 12, x_94);
lean_ctor_set_uint8(x_105, 13, x_95);
lean_ctor_set_uint8(x_105, 14, x_96);
lean_ctor_set_uint8(x_105, 15, x_97);
lean_ctor_set_uint8(x_105, 16, x_98);
lean_ctor_set_uint8(x_105, 17, x_99);
x_106 = l_Lean_Meta_TransparencyMode_toUInt64(x_91);
x_107 = lean_uint64_lor(x_104, x_106);
x_108 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_43);
lean_ctor_set(x_108, 2, x_44);
lean_ctor_set(x_108, 3, x_45);
lean_ctor_set(x_108, 4, x_46);
lean_ctor_set(x_108, 5, x_47);
lean_ctor_set(x_108, 6, x_48);
lean_ctor_set_uint64(x_108, sizeof(void*)*7, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 8, x_42);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 9, x_80);
lean_ctor_set_uint8(x_108, sizeof(void*)*7 + 10, x_81);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
x_109 = l_Lean_Elab_Eqns_tryURefl(x_24, x_108, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_unbox(x_110);
lean_dec(x_110);
x_26 = x_112;
x_27 = x_111;
goto block_39;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_113 = lean_ctor_get(x_109, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_109, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_115 = x_109;
} else {
 lean_dec_ref(x_109);
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
lean_object* x_117; uint64_t x_118; uint64_t x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_117, 0, x_82);
lean_ctor_set_uint8(x_117, 1, x_83);
lean_ctor_set_uint8(x_117, 2, x_84);
lean_ctor_set_uint8(x_117, 3, x_85);
lean_ctor_set_uint8(x_117, 4, x_86);
lean_ctor_set_uint8(x_117, 5, x_87);
lean_ctor_set_uint8(x_117, 6, x_88);
lean_ctor_set_uint8(x_117, 7, x_89);
lean_ctor_set_uint8(x_117, 8, x_90);
lean_ctor_set_uint8(x_117, 9, x_100);
lean_ctor_set_uint8(x_117, 10, x_92);
lean_ctor_set_uint8(x_117, 11, x_93);
lean_ctor_set_uint8(x_117, 12, x_94);
lean_ctor_set_uint8(x_117, 13, x_95);
lean_ctor_set_uint8(x_117, 14, x_96);
lean_ctor_set_uint8(x_117, 15, x_97);
lean_ctor_set_uint8(x_117, 16, x_98);
lean_ctor_set_uint8(x_117, 17, x_99);
x_118 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__5;
x_119 = lean_uint64_lor(x_104, x_118);
x_120 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_43);
lean_ctor_set(x_120, 2, x_44);
lean_ctor_set(x_120, 3, x_45);
lean_ctor_set(x_120, 4, x_46);
lean_ctor_set(x_120, 5, x_47);
lean_ctor_set(x_120, 6, x_48);
lean_ctor_set_uint64(x_120, sizeof(void*)*7, x_119);
lean_ctor_set_uint8(x_120, sizeof(void*)*7 + 8, x_42);
lean_ctor_set_uint8(x_120, sizeof(void*)*7 + 9, x_80);
lean_ctor_set_uint8(x_120, sizeof(void*)*7 + 10, x_81);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
x_121 = l_Lean_Elab_Eqns_tryURefl(x_24, x_120, x_5, x_6, x_7, x_25);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_unbox(x_122);
lean_dec(x_122);
x_26 = x_124;
x_27 = x_123;
goto block_39;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_125 = lean_ctor_get(x_121, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_127 = x_121;
} else {
 lean_dec_ref(x_121);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
block_39:
{
if (x_26 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
x_28 = l_Lean_MessageData_ofName(x_2);
x_29 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__2;
if (lean_is_scalar(x_19)) {
 x_30 = lean_alloc_ctor(7, 2, 0);
} else {
 x_30 = x_19;
 lean_ctor_set_tag(x_30, 7);
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__4;
if (lean_is_scalar(x_13)) {
 x_32 = lean_alloc_ctor(7, 2, 0);
} else {
 x_32 = x_13;
 lean_ctor_set_tag(x_32, 7);
}
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_24);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_36, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_37;
}
else
{
lean_object* x_38; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_2);
x_38 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_11, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_38;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_23);
if (x_129 == 0)
{
return x_23;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_23, 0);
x_131 = lean_ctor_get(x_23, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_23);
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
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_133 = !lean_is_exclusive(x_20);
if (x_133 == 0)
{
return x_20;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_20, 0);
x_135 = lean_ctor_get(x_20, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_20);
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
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = !lean_is_exclusive(x_15);
if (x_137 == 0)
{
return x_15;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_15, 0);
x_139 = lean_ctor_get(x_15, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_15);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
x_11 = 0;
x_12 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__2;
x_3 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proving: ", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__4;
x_10 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__2(x_3, x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_10, 1);
x_18 = lean_ctor_get(x_10, 0);
lean_dec(x_18);
lean_inc(x_3);
x_19 = l_Lean_MessageData_ofExpr(x_3);
x_20 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__6;
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_20);
x_21 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_9, x_22, x_4, x_5, x_6, x_7, x_17);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__2(x_3, x_1, x_2, x_24, x_4, x_5, x_6, x_7, x_25);
lean_dec(x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
lean_inc(x_3);
x_28 = l_Lean_MessageData_ofExpr(x_3);
x_29 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__6;
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_9, x_32, x_4, x_5, x_6, x_7, x_27);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__2(x_3, x_1, x_2, x_34, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = l_Lean_Meta_eqnThmSuffixBase;
lean_inc(x_1);
x_15 = l_Lean_Name_str___override(x_1, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
x_18 = lean_name_append_index_after(x_15, x_17);
lean_inc(x_18);
x_19 = lean_array_push(x_7, x_18);
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
lean_dec(x_3);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_4);
x_21 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof(x_1, x_20, x_4, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(x_4, x_22, x_11, x_12, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_ctor_get(x_25, 1);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_18);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set_tag(x_25, 1);
lean_ctor_set(x_25, 1, x_6);
lean_ctor_set(x_25, 0, x_18);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_25);
x_33 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = l_Lean_addDecl(x_33, x_11, x_12, x_26);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_19);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_19);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_19);
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
return x_34;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_34, 0);
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_inc(x_18);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_18);
lean_ctor_set(x_49, 1, x_6);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_49);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lean_addDecl(x_51, x_11, x_12, x_26);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_19);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_19);
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
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
uint8_t x_61; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_21);
if (x_61 == 0)
{
return x_21;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_21, 0);
x_63 = lean_ctor_get(x_21, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_21);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_7, 1);
x_18 = lean_nat_dec_lt(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_array_fget(x_4, x_9);
x_21 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__4;
x_22 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_21, x_12, x_13, x_14, x_15, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___lambda__1(x_1, x_9, x_2, x_20, x_3, x_5, x_8, x_26, x_12, x_13, x_14, x_15, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_7, 2);
x_38 = lean_nat_add(x_9, x_37);
lean_dec(x_9);
x_8 = x_36;
x_9 = x_38;
x_10 = lean_box(0);
x_11 = lean_box(0);
x_16 = x_35;
goto _start;
}
}
else
{
uint8_t x_40; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
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
x_44 = !lean_is_exclusive(x_22);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_22, 1);
x_46 = lean_ctor_get(x_22, 0);
lean_dec(x_46);
lean_inc(x_20);
x_47 = l_Lean_MessageData_ofExpr(x_20);
x_48 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_47);
lean_ctor_set(x_22, 0, x_48);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_22);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_21, x_49, x_12, x_13, x_14, x_15, x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_53 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___lambda__1(x_1, x_9, x_2, x_20, x_3, x_5, x_8, x_51, x_12, x_13, x_14, x_15, x_52);
lean_dec(x_51);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_54, 0);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_53, 0, x_57);
return x_53;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_ctor_get(x_54, 0);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
lean_dec(x_53);
x_62 = lean_ctor_get(x_54, 0);
lean_inc(x_62);
lean_dec(x_54);
x_63 = lean_ctor_get(x_7, 2);
x_64 = lean_nat_add(x_9, x_63);
lean_dec(x_9);
x_8 = x_62;
x_9 = x_64;
x_10 = lean_box(0);
x_11 = lean_box(0);
x_16 = x_61;
goto _start;
}
}
else
{
uint8_t x_66; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_53);
if (x_66 == 0)
{
return x_53;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_22, 1);
lean_inc(x_70);
lean_dec(x_22);
lean_inc(x_20);
x_71 = l_Lean_MessageData_ofExpr(x_20);
x_72 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
x_75 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_21, x_74, x_12, x_13, x_14, x_15, x_70);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_78 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___lambda__1(x_1, x_9, x_2, x_20, x_3, x_5, x_8, x_76, x_12, x_13, x_14, x_15, x_77);
lean_dec(x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
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
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_ctor_get(x_79, 0);
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_ctor_get(x_7, 2);
x_87 = lean_nat_add(x_9, x_86);
lean_dec(x_9);
x_8 = x_85;
x_9 = x_87;
x_10 = lean_box(0);
x_11 = lean_box(0);
x_16 = x_84;
goto _start;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_78, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_78, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_91 = x_78;
} else {
 lean_dec_ref(x_78);
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
}
}
}
static uint64_t _init_l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___closed__1() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_11, x_12);
x_14 = l_Lean_Expr_const___override(x_2, x_13);
x_15 = l_Lean_mkAppN(x_14, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_mkEq(x_15, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
lean_inc(x_6);
x_20 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_17, x_19, x_6, x_7, x_8, x_9, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
lean_dec(x_3);
x_24 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_6);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_6, 0);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
uint64_t x_28; uint8_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; lean_object* x_35; 
x_28 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_29 = 2;
lean_ctor_set_uint8(x_26, 9, x_29);
x_30 = 2;
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_shift_left(x_31, x_30);
x_33 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___closed__1;
x_34 = lean_uint64_lor(x_32, x_33);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_34);
x_35 = l_Lean_Elab_Eqns_mkEqnTypes(x_23, x_24, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
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
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_35);
if (x_40 == 0)
{
return x_35;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_35);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint64_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; uint64_t x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; lean_object* x_69; 
x_44 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_45 = lean_ctor_get_uint8(x_26, 0);
x_46 = lean_ctor_get_uint8(x_26, 1);
x_47 = lean_ctor_get_uint8(x_26, 2);
x_48 = lean_ctor_get_uint8(x_26, 3);
x_49 = lean_ctor_get_uint8(x_26, 4);
x_50 = lean_ctor_get_uint8(x_26, 5);
x_51 = lean_ctor_get_uint8(x_26, 6);
x_52 = lean_ctor_get_uint8(x_26, 7);
x_53 = lean_ctor_get_uint8(x_26, 8);
x_54 = lean_ctor_get_uint8(x_26, 10);
x_55 = lean_ctor_get_uint8(x_26, 11);
x_56 = lean_ctor_get_uint8(x_26, 12);
x_57 = lean_ctor_get_uint8(x_26, 13);
x_58 = lean_ctor_get_uint8(x_26, 14);
x_59 = lean_ctor_get_uint8(x_26, 15);
x_60 = lean_ctor_get_uint8(x_26, 16);
x_61 = lean_ctor_get_uint8(x_26, 17);
lean_dec(x_26);
x_62 = 2;
x_63 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_63, 0, x_45);
lean_ctor_set_uint8(x_63, 1, x_46);
lean_ctor_set_uint8(x_63, 2, x_47);
lean_ctor_set_uint8(x_63, 3, x_48);
lean_ctor_set_uint8(x_63, 4, x_49);
lean_ctor_set_uint8(x_63, 5, x_50);
lean_ctor_set_uint8(x_63, 6, x_51);
lean_ctor_set_uint8(x_63, 7, x_52);
lean_ctor_set_uint8(x_63, 8, x_53);
lean_ctor_set_uint8(x_63, 9, x_62);
lean_ctor_set_uint8(x_63, 10, x_54);
lean_ctor_set_uint8(x_63, 11, x_55);
lean_ctor_set_uint8(x_63, 12, x_56);
lean_ctor_set_uint8(x_63, 13, x_57);
lean_ctor_set_uint8(x_63, 14, x_58);
lean_ctor_set_uint8(x_63, 15, x_59);
lean_ctor_set_uint8(x_63, 16, x_60);
lean_ctor_set_uint8(x_63, 17, x_61);
x_64 = 2;
x_65 = lean_uint64_shift_right(x_44, x_64);
x_66 = lean_uint64_shift_left(x_65, x_64);
x_67 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___closed__1;
x_68 = lean_uint64_lor(x_66, x_67);
lean_ctor_set(x_6, 0, x_63);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_68);
x_69 = l_Lean_Elab_Eqns_mkEqnTypes(x_23, x_24, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
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
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
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
lean_object* x_78; uint64_t x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; lean_object* x_114; lean_object* x_115; 
x_78 = lean_ctor_get(x_6, 0);
x_79 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_80 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_81 = lean_ctor_get(x_6, 1);
x_82 = lean_ctor_get(x_6, 2);
x_83 = lean_ctor_get(x_6, 3);
x_84 = lean_ctor_get(x_6, 4);
x_85 = lean_ctor_get(x_6, 5);
x_86 = lean_ctor_get(x_6, 6);
x_87 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_88 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_78);
lean_dec(x_6);
x_89 = lean_ctor_get_uint8(x_78, 0);
x_90 = lean_ctor_get_uint8(x_78, 1);
x_91 = lean_ctor_get_uint8(x_78, 2);
x_92 = lean_ctor_get_uint8(x_78, 3);
x_93 = lean_ctor_get_uint8(x_78, 4);
x_94 = lean_ctor_get_uint8(x_78, 5);
x_95 = lean_ctor_get_uint8(x_78, 6);
x_96 = lean_ctor_get_uint8(x_78, 7);
x_97 = lean_ctor_get_uint8(x_78, 8);
x_98 = lean_ctor_get_uint8(x_78, 10);
x_99 = lean_ctor_get_uint8(x_78, 11);
x_100 = lean_ctor_get_uint8(x_78, 12);
x_101 = lean_ctor_get_uint8(x_78, 13);
x_102 = lean_ctor_get_uint8(x_78, 14);
x_103 = lean_ctor_get_uint8(x_78, 15);
x_104 = lean_ctor_get_uint8(x_78, 16);
x_105 = lean_ctor_get_uint8(x_78, 17);
if (lean_is_exclusive(x_78)) {
 x_106 = x_78;
} else {
 lean_dec_ref(x_78);
 x_106 = lean_box(0);
}
x_107 = 2;
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 0, 18);
} else {
 x_108 = x_106;
}
lean_ctor_set_uint8(x_108, 0, x_89);
lean_ctor_set_uint8(x_108, 1, x_90);
lean_ctor_set_uint8(x_108, 2, x_91);
lean_ctor_set_uint8(x_108, 3, x_92);
lean_ctor_set_uint8(x_108, 4, x_93);
lean_ctor_set_uint8(x_108, 5, x_94);
lean_ctor_set_uint8(x_108, 6, x_95);
lean_ctor_set_uint8(x_108, 7, x_96);
lean_ctor_set_uint8(x_108, 8, x_97);
lean_ctor_set_uint8(x_108, 9, x_107);
lean_ctor_set_uint8(x_108, 10, x_98);
lean_ctor_set_uint8(x_108, 11, x_99);
lean_ctor_set_uint8(x_108, 12, x_100);
lean_ctor_set_uint8(x_108, 13, x_101);
lean_ctor_set_uint8(x_108, 14, x_102);
lean_ctor_set_uint8(x_108, 15, x_103);
lean_ctor_set_uint8(x_108, 16, x_104);
lean_ctor_set_uint8(x_108, 17, x_105);
x_109 = 2;
x_110 = lean_uint64_shift_right(x_79, x_109);
x_111 = lean_uint64_shift_left(x_110, x_109);
x_112 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___closed__1;
x_113 = lean_uint64_lor(x_111, x_112);
x_114 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_81);
lean_ctor_set(x_114, 2, x_82);
lean_ctor_set(x_114, 3, x_83);
lean_ctor_set(x_114, 4, x_84);
lean_ctor_set(x_114, 5, x_85);
lean_ctor_set(x_114, 6, x_86);
lean_ctor_set_uint64(x_114, sizeof(void*)*7, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*7 + 8, x_80);
lean_ctor_set_uint8(x_114, sizeof(void*)*7 + 9, x_87);
lean_ctor_set_uint8(x_114, sizeof(void*)*7 + 10, x_88);
x_115 = l_Lean_Elab_Eqns_mkEqnTypes(x_23, x_24, x_114, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_122 = x_115;
} else {
 lean_dec_ref(x_115);
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
else
{
uint8_t x_124; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_124 = !lean_is_exclusive(x_16);
if (x_124 == 0)
{
return x_16;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_16, 0);
x_126 = lean_ctor_get(x_16, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_16);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_10, 4);
lean_dec(x_14);
x_15 = lean_ctor_get(x_10, 2);
lean_dec(x_15);
x_16 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__1;
x_17 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_16);
lean_ctor_set(x_10, 4, x_17);
lean_ctor_set(x_10, 2, x_1);
lean_ctor_set_uint8(x_10, sizeof(void*)*12, x_2);
x_18 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_3, x_18, x_4, x_5, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_box(0);
x_23 = lean_array_get_size(x_20);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__2;
x_28 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1(x_6, x_7, x_8, x_20, x_22, x_26, x_26, x_27, x_24, lean_box(0), lean_box(0), x_4, x_5, x_10, x_11, x_21);
lean_dec(x_26);
lean_dec(x_20);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
return x_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
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
lean_dec(x_10);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_19);
if (x_37 == 0)
{
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_19, 0);
x_39 = lean_ctor_get(x_19, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_19);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
x_43 = lean_ctor_get(x_10, 3);
x_44 = lean_ctor_get(x_10, 5);
x_45 = lean_ctor_get(x_10, 6);
x_46 = lean_ctor_get(x_10, 7);
x_47 = lean_ctor_get(x_10, 8);
x_48 = lean_ctor_get(x_10, 9);
x_49 = lean_ctor_get(x_10, 10);
x_50 = lean_ctor_get(x_10, 11);
x_51 = lean_ctor_get_uint8(x_10, sizeof(void*)*12 + 1);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_52 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__1;
x_53 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_52);
x_54 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_54, 0, x_41);
lean_ctor_set(x_54, 1, x_42);
lean_ctor_set(x_54, 2, x_1);
lean_ctor_set(x_54, 3, x_43);
lean_ctor_set(x_54, 4, x_53);
lean_ctor_set(x_54, 5, x_44);
lean_ctor_set(x_54, 6, x_45);
lean_ctor_set(x_54, 7, x_46);
lean_ctor_set(x_54, 8, x_47);
lean_ctor_set(x_54, 9, x_48);
lean_ctor_set(x_54, 10, x_49);
lean_ctor_set(x_54, 11, x_50);
lean_ctor_set_uint8(x_54, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_54, sizeof(void*)*12 + 1, x_51);
x_55 = 0;
lean_inc(x_11);
lean_inc(x_54);
lean_inc(x_5);
lean_inc(x_4);
x_56 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_3, x_55, x_4, x_5, x_54, x_11, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_box(0);
x_60 = lean_array_get_size(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_62);
x_64 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__2;
x_65 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1(x_6, x_7, x_8, x_57, x_59, x_63, x_63, x_64, x_61, lean_box(0), lean_box(0), x_4, x_5, x_54, x_11, x_58);
lean_dec(x_63);
lean_dec(x_57);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_65, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_72 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_dec(x_54);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_74 = lean_ctor_get(x_56, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_56, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_76 = x_56;
} else {
 lean_dec_ref(x_56);
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_hygienic;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkEqns___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkEqns___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___boxed), 10, 3);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
x_11 = 1;
x_12 = lean_box(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg___boxed), 8, 3);
lean_closure_set(x_13, 0, x_9);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_12);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
x_15 = l_Lean_Elab_PartialFixpoint_mkEqns___closed__1;
x_16 = 0;
x_17 = l_Lean_Option_set___at_Lean_Meta_getEqnsFor_x3f___spec__1(x_14, x_15, x_16);
x_18 = l_Lean_Elab_PartialFixpoint_mkEqns___closed__2;
x_19 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_17, x_18);
x_20 = lean_st_ref_get(x_6, x_7);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Kernel_isDiagnosticsEnabled(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
if (x_19 == 0)
{
x_25 = x_11;
goto block_54;
}
else
{
x_25 = x_16;
goto block_54;
}
}
else
{
if (x_19 == 0)
{
x_25 = x_16;
goto block_54;
}
else
{
x_25 = x_11;
goto block_54;
}
}
block_54:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_st_ref_take(x_6, x_22);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 4);
lean_dec(x_31);
x_32 = l_Lean_Kernel_enableDiag(x_30, x_19);
x_33 = l_Lean_Elab_PartialFixpoint_mkEqns___closed__5;
lean_ctor_set(x_27, 4, x_33);
lean_ctor_set(x_27, 0, x_32);
x_34 = lean_st_ref_set(x_6, x_27, x_28);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_box(0);
x_37 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2(x_17, x_19, x_13, x_3, x_4, x_1, x_2, x_8, x_36, x_5, x_6, x_35);
lean_dec(x_8);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
x_40 = lean_ctor_get(x_27, 2);
x_41 = lean_ctor_get(x_27, 3);
x_42 = lean_ctor_get(x_27, 5);
x_43 = lean_ctor_get(x_27, 6);
x_44 = lean_ctor_get(x_27, 7);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_45 = l_Lean_Kernel_enableDiag(x_38, x_19);
x_46 = l_Lean_Elab_PartialFixpoint_mkEqns___closed__5;
x_47 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_40);
lean_ctor_set(x_47, 3, x_41);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_42);
lean_ctor_set(x_47, 6, x_43);
lean_ctor_set(x_47, 7, x_44);
x_48 = lean_st_ref_set(x_6, x_47, x_28);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = lean_box(0);
x_51 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2(x_17, x_19, x_13, x_3, x_4, x_1, x_2, x_8, x_50, x_5, x_6, x_49);
lean_dec(x_8);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2(x_17, x_19, x_13, x_3, x_4, x_1, x_2, x_8, x_52, x_5, x_6, x_22);
lean_dec(x_8);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at_Lean_Elab_PartialFixpoint_mkEqns___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec(x_8);
return x_14;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PartialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqnInfoExt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__1;
x_3 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__1;
x_4 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__2;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__3;
x_3 = l_Lean_mkMapDeclarationExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
lean_dec(x_5);
x_7 = l_Lean_Elab_DefKind_isTheorem(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
else
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
goto _start;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2(size_t x_1, size_t x_2, lean_object* x_3) {
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_9 = lean_array_uget(x_4, x_5);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 5);
lean_inc(x_13);
lean_dec(x_9);
lean_inc(x_10);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_3);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_1);
lean_ctor_set(x_15, 3, x_2);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
x_17 = l_Lean_MapDeclarationExtension_insert___rarg(x_16, x_7, x_10, x_15);
x_18 = 1;
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_7 = x_17;
goto _start;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_1, x_2);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Meta_isProp(x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = 1;
x_18 = lean_box(x_17);
lean_ctor_set(x_12, 0, x_18);
return x_12;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_12, 1);
lean_inc(x_23);
lean_dec(x_12);
x_24 = 1;
x_25 = lean_usize_add(x_2, x_24);
x_2 = x_25;
x_8 = x_23;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_8);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Meta_ensureEqnReservedNamesAvailable(x_12, x_7, x_8, x_9);
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
x_9 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
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
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_9);
return x_23;
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkEqns___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_82; uint8_t x_83; 
x_9 = lean_array_get_size(x_1);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_nat_dec_lt(x_82, x_9);
if (x_83 == 0)
{
x_10 = x_8;
goto block_81;
}
else
{
uint8_t x_84; 
x_84 = lean_nat_dec_le(x_9, x_9);
if (x_84 == 0)
{
x_10 = x_8;
goto block_81;
}
else
{
size_t x_85; size_t x_86; lean_object* x_87; lean_object* x_88; 
x_85 = 0;
x_86 = lean_usize_of_nat(x_9);
x_87 = lean_box(0);
x_88 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5(x_1, x_85, x_86, x_87, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_10 = x_89;
goto block_81;
}
else
{
uint8_t x_90; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_88);
if (x_90 == 0)
{
return x_88;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_88, 0);
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_88);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
block_81:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_9);
x_17 = l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1(x_1, x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_70; 
lean_inc(x_7);
lean_inc(x_5);
x_70 = l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4(x_1, x_15, x_16, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = 1;
x_20 = x_74;
x_21 = x_73;
goto block_69;
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_dec(x_70);
x_76 = 0;
x_20 = x_76;
x_21 = x_75;
goto block_69;
}
}
else
{
uint8_t x_77; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_70);
if (x_77 == 0)
{
return x_70;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_70, 0);
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_70);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
block_69:
{
if (x_20 == 0)
{
size_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_65; 
x_22 = lean_array_size(x_1);
lean_inc(x_1);
x_23 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2(x_22, x_15, x_1);
x_24 = lean_st_ref_take(x_7, x_21);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_25, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_25, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_25, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 7);
lean_inc(x_33);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 lean_ctor_release(x_25, 2);
 lean_ctor_release(x_25, 3);
 lean_ctor_release(x_25, 4);
 lean_ctor_release(x_25, 5);
 lean_ctor_release(x_25, 6);
 lean_ctor_release(x_25, 7);
 x_34 = x_25;
} else {
 lean_dec_ref(x_25);
 x_34 = lean_box(0);
}
x_65 = lean_nat_dec_le(x_9, x_9);
lean_dec(x_9);
if (x_65 == 0)
{
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = x_27;
goto block_64;
}
else
{
lean_object* x_66; 
x_66 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3(x_2, x_3, x_23, x_1, x_15, x_16, x_27);
lean_dec(x_1);
x_35 = x_66;
goto block_64;
}
block_64:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_36 = l_Lean_Elab_PartialFixpoint_mkEqns___closed__5;
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 8, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_29);
lean_ctor_set(x_37, 3, x_30);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_31);
lean_ctor_set(x_37, 6, x_32);
lean_ctor_set(x_37, 7, x_33);
x_38 = lean_st_ref_set(x_7, x_37, x_26);
lean_dec(x_7);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_st_ref_take(x_5, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_41, 1);
lean_dec(x_44);
x_45 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1;
lean_ctor_set(x_41, 1, x_45);
x_46 = lean_st_ref_set(x_5, x_41, x_42);
lean_dec(x_5);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 2);
x_55 = lean_ctor_get(x_41, 3);
x_56 = lean_ctor_get(x_41, 4);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_57 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1;
x_58 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_54);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_58, 4, x_56);
x_59 = lean_st_ref_set(x_5, x_58, x_42);
lean_dec(x_5);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_21);
return x_68;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getEqnsFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
lean_inc(x_1);
x_14 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_12, x_13, x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
uint8_t x_16; 
lean_free_object(x_7);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = l_Lean_Elab_PartialFixpoint_mkEqns(x_1, x_17, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_14, 0, x_20);
lean_ctor_set(x_18, 0, x_14);
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
lean_ctor_set(x_14, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_free_object(x_14);
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
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_Elab_PartialFixpoint_mkEqns(x_1, x_28, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_alloc_ctor(1, 1, 0);
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
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_37 = x_29;
} else {
 lean_dec_ref(x_29);
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
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_43 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
lean_inc(x_1);
x_44 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_42, x_43, x_41, x_1);
lean_dec(x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_49 = l_Lean_Elab_PartialFixpoint_mkEqns(x_1, x_47, x_2, x_3, x_4, x_5, x_40);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
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
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_50);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_48);
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_57 = x_49;
} else {
 lean_dec_ref(x_49);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_5 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
x_6 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_4, x_5, x_1, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_ctor_set(x_6, 0, x_10);
return x_6;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1___boxed), 3, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
x_12 = l_Lean_Elab_Eqns_getUnfoldFor_x3f(x_1, x_11, x_2, x_3, x_4, x_5, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_getEqnsFor_x3f), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__1;
x_3 = l_Lean_Meta_registerGetEqnsFn(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__2;
x_6 = l_Lean_Meta_registerGetUnfoldEqnFn(x_5, x_4);
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
lean_object* initialize_Lean_Elab_Tactic_Conv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_ArgsPacker_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Internal_Order_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_PartialFixpoint_Eqns(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Conv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ArgsPacker_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Internal_Order_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1 = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2 = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3 = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4 = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__2);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__3 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__3);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__4 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__4);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__5 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__5);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__6 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__6);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__7 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__7);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__8 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__8);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17();
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__4);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__5 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__5);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__2);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__3);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__4);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__5 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___lambda__1___closed__5();
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__2 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__2);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__3 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__3);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__4 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__4);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__5 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__5);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__6 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_mkProof___closed__6);
l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkEqns___lambda__1___closed__1();
l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__1);
l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkEqns___lambda__2___closed__2);
l_Lean_Elab_PartialFixpoint_mkEqns___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkEqns___closed__1);
l_Lean_Elab_PartialFixpoint_mkEqns___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkEqns___closed__2);
l_Lean_Elab_PartialFixpoint_mkEqns___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkEqns___closed__3);
l_Lean_Elab_PartialFixpoint_mkEqns___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkEqns___closed__4);
l_Lean_Elab_PartialFixpoint_mkEqns___closed__5 = _init_l_Lean_Elab_PartialFixpoint_mkEqns___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkEqns___closed__5);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__1 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__2 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__2);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__3 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296____closed__3);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1296_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_PartialFixpoint_eqnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_eqnInfoExt);
lean_dec_ref(res);
}l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__1 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__2 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569____closed__2);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1569_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
