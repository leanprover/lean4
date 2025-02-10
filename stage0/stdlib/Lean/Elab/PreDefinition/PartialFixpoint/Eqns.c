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
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__2;
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__4;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
lean_object* l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4;
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___closed__1;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17;
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1(lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__9___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__2;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__3;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618_(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_smartUnfolding;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static uint64_t l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__1;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4;
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__1;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55_(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__3;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__4;
lean_object* l_Lean_Option_set___at_Lean_Meta_evalExprCore___spec__1(lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__1;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__9;
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__2;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__5;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__5;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3;
lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__4;
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__5;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__7;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__5;
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__3;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__6;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__6;
static size_t l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__4;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_mkEqns(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Meta_subst_substEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PartialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqnInfoExt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__3;
x_4 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__5;
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
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
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
x_36 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
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
x_45 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4;
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
x_57 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4;
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
x_1 = lean_mk_string_unchecked("Order", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
x_3 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rwFixUnder: unexpected expression ", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("p", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
x_3 = lean_unsigned_to_nat(1770u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static size_t _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1;
x_2 = lean_ptr_addr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrFun", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix_eq", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
x_3 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21() {
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
x_7 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3;
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
x_13 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
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
x_44 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
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
x_48 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
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
x_26 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
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
x_33 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
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
x_63 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
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
x_71 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
x_72 = l_Lean_Expr_const___override(x_71, x_70);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_73);
x_75 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
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
x_3 = lean_unsigned_to_nat(60u);
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
x_3 = lean_unsigned_to_nat(62u);
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_dec(x_12);
x_13 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___closed__1;
x_14 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_13);
lean_ctor_set(x_7, 4, x_14);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*12, x_2);
x_15 = l_Lean_MVarId_refl(x_3, x_4, x_5, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
x_18 = lean_ctor_get(x_7, 3);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_7);
x_27 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___closed__1;
x_28 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_27);
x_29 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_29, 0, x_16);
lean_ctor_set(x_29, 1, x_17);
lean_ctor_set(x_29, 2, x_1);
lean_ctor_set(x_29, 3, x_18);
lean_ctor_set(x_29, 4, x_28);
lean_ctor_set(x_29, 5, x_19);
lean_ctor_set(x_29, 6, x_20);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_22);
lean_ctor_set(x_29, 9, x_23);
lean_ctor_set(x_29, 10, x_24);
lean_ctor_set(x_29, 11, x_25);
lean_ctor_set_uint8(x_29, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_29, sizeof(void*)*12 + 1, x_26);
x_30 = l_Lean_MVarId_refl(x_3, x_4, x_5, x_29, x_8, x_9);
return x_30;
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq rfl succeeded", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_smartUnfolding;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint64_t _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__5() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_28; lean_object* x_38; uint64_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_38 = lean_ctor_get(x_6, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_40 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_41 = lean_ctor_get(x_6, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_6, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_6, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_6, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_6, 5);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 6);
lean_inc(x_46);
x_47 = !lean_is_exclusive(x_38);
if (x_47 == 0)
{
uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; 
x_48 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_49 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_50 = lean_ctor_get_uint8(x_38, 9);
x_51 = 0;
x_52 = l_Lean_Meta_TransparencyMode_lt(x_50, x_51);
x_53 = 2;
x_54 = lean_uint64_shift_right(x_39, x_53);
x_55 = lean_uint64_shift_left(x_54, x_53);
if (x_52 == 0)
{
uint64_t x_56; uint64_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; 
x_56 = l_Lean_Meta_TransparencyMode_toUInt64(x_50);
x_57 = lean_uint64_lor(x_55, x_56);
x_58 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_58, 0, x_38);
lean_ctor_set(x_58, 1, x_41);
lean_ctor_set(x_58, 2, x_42);
lean_ctor_set(x_58, 3, x_43);
lean_ctor_set(x_58, 4, x_44);
lean_ctor_set(x_58, 5, x_45);
lean_ctor_set(x_58, 6, x_46);
lean_ctor_set_uint64(x_58, sizeof(void*)*7, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 8, x_40);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 10, x_49);
x_59 = lean_ctor_get(x_8, 2);
lean_inc(x_59);
x_60 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__3;
x_61 = 0;
x_62 = l_Lean_Option_set___at_Lean_Meta_evalExprCore___spec__1(x_59, x_60, x_61);
x_63 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4;
x_64 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_62, x_63);
x_65 = lean_st_ref_get(x_9, x_10);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Kernel_isDiagnosticsEnabled(x_68);
lean_dec(x_68);
if (x_69 == 0)
{
if (x_64 == 0)
{
uint8_t x_117; 
x_117 = 1;
x_70 = x_117;
goto block_116;
}
else
{
x_70 = x_61;
goto block_116;
}
}
else
{
if (x_64 == 0)
{
x_70 = x_61;
goto block_116;
}
else
{
uint8_t x_118; 
x_118 = 1;
x_70 = x_118;
goto block_116;
}
}
block_116:
{
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_st_ref_take(x_9, x_67);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_71, 1);
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_ctor_get(x_73, 4);
lean_dec(x_77);
x_78 = l_Lean_Kernel_enableDiag(x_76, x_64);
lean_inc(x_4);
lean_ctor_set(x_71, 1, x_4);
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_73, 4, x_71);
lean_ctor_set(x_73, 0, x_78);
x_79 = lean_st_ref_set(x_9, x_73, x_75);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_82 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_62, x_64, x_3, x_58, x_7, x_81, x_8, x_9, x_80);
x_28 = x_82;
goto block_37;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_83 = lean_ctor_get(x_71, 1);
x_84 = lean_ctor_get(x_73, 0);
x_85 = lean_ctor_get(x_73, 1);
x_86 = lean_ctor_get(x_73, 2);
x_87 = lean_ctor_get(x_73, 3);
x_88 = lean_ctor_get(x_73, 5);
x_89 = lean_ctor_get(x_73, 6);
x_90 = lean_ctor_get(x_73, 7);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_73);
x_91 = l_Lean_Kernel_enableDiag(x_84, x_64);
lean_inc(x_4);
lean_ctor_set(x_71, 1, x_4);
lean_ctor_set(x_71, 0, x_4);
x_92 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_85);
lean_ctor_set(x_92, 2, x_86);
lean_ctor_set(x_92, 3, x_87);
lean_ctor_set(x_92, 4, x_71);
lean_ctor_set(x_92, 5, x_88);
lean_ctor_set(x_92, 6, x_89);
lean_ctor_set(x_92, 7, x_90);
x_93 = lean_st_ref_set(x_9, x_92, x_83);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_96 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_62, x_64, x_3, x_58, x_7, x_95, x_8, x_9, x_94);
x_28 = x_96;
goto block_37;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_97 = lean_ctor_get(x_71, 0);
x_98 = lean_ctor_get(x_71, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_71);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_97, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_97, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_97, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_97, 6);
lean_inc(x_104);
x_105 = lean_ctor_get(x_97, 7);
lean_inc(x_105);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 lean_ctor_release(x_97, 2);
 lean_ctor_release(x_97, 3);
 lean_ctor_release(x_97, 4);
 lean_ctor_release(x_97, 5);
 lean_ctor_release(x_97, 6);
 lean_ctor_release(x_97, 7);
 x_106 = x_97;
} else {
 lean_dec_ref(x_97);
 x_106 = lean_box(0);
}
x_107 = l_Lean_Kernel_enableDiag(x_99, x_64);
lean_inc(x_4);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_4);
lean_ctor_set(x_108, 1, x_4);
if (lean_is_scalar(x_106)) {
 x_109 = lean_alloc_ctor(0, 8, 0);
} else {
 x_109 = x_106;
}
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_101);
lean_ctor_set(x_109, 3, x_102);
lean_ctor_set(x_109, 4, x_108);
lean_ctor_set(x_109, 5, x_103);
lean_ctor_set(x_109, 6, x_104);
lean_ctor_set(x_109, 7, x_105);
x_110 = lean_st_ref_set(x_9, x_109, x_98);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_113 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_62, x_64, x_3, x_58, x_7, x_112, x_8, x_9, x_111);
x_28 = x_113;
goto block_37;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_4);
x_114 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_115 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_62, x_64, x_3, x_58, x_7, x_114, x_8, x_9, x_67);
x_28 = x_115;
goto block_37;
}
}
}
else
{
uint64_t x_119; uint64_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
lean_ctor_set_uint8(x_38, 9, x_51);
x_119 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__5;
x_120 = lean_uint64_lor(x_55, x_119);
x_121 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_121, 0, x_38);
lean_ctor_set(x_121, 1, x_41);
lean_ctor_set(x_121, 2, x_42);
lean_ctor_set(x_121, 3, x_43);
lean_ctor_set(x_121, 4, x_44);
lean_ctor_set(x_121, 5, x_45);
lean_ctor_set(x_121, 6, x_46);
lean_ctor_set_uint64(x_121, sizeof(void*)*7, x_120);
lean_ctor_set_uint8(x_121, sizeof(void*)*7 + 8, x_40);
lean_ctor_set_uint8(x_121, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_121, sizeof(void*)*7 + 10, x_49);
x_122 = lean_ctor_get(x_8, 2);
lean_inc(x_122);
x_123 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__3;
x_124 = 0;
x_125 = l_Lean_Option_set___at_Lean_Meta_evalExprCore___spec__1(x_122, x_123, x_124);
x_126 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4;
x_127 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_125, x_126);
x_128 = lean_st_ref_get(x_9, x_10);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_Kernel_isDiagnosticsEnabled(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
if (x_127 == 0)
{
uint8_t x_180; 
x_180 = 1;
x_133 = x_180;
goto block_179;
}
else
{
x_133 = x_124;
goto block_179;
}
}
else
{
if (x_127 == 0)
{
x_133 = x_124;
goto block_179;
}
else
{
uint8_t x_181; 
x_181 = 1;
x_133 = x_181;
goto block_179;
}
}
block_179:
{
if (x_133 == 0)
{
lean_object* x_134; uint8_t x_135; 
x_134 = lean_st_ref_take(x_9, x_130);
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_134, 1);
x_139 = lean_ctor_get(x_136, 0);
x_140 = lean_ctor_get(x_136, 4);
lean_dec(x_140);
x_141 = l_Lean_Kernel_enableDiag(x_139, x_127);
lean_inc(x_4);
lean_ctor_set(x_134, 1, x_4);
lean_ctor_set(x_134, 0, x_4);
lean_ctor_set(x_136, 4, x_134);
lean_ctor_set(x_136, 0, x_141);
x_142 = lean_st_ref_set(x_9, x_136, x_138);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_144 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_145 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_125, x_127, x_3, x_121, x_7, x_144, x_8, x_9, x_143);
x_28 = x_145;
goto block_37;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_146 = lean_ctor_get(x_134, 1);
x_147 = lean_ctor_get(x_136, 0);
x_148 = lean_ctor_get(x_136, 1);
x_149 = lean_ctor_get(x_136, 2);
x_150 = lean_ctor_get(x_136, 3);
x_151 = lean_ctor_get(x_136, 5);
x_152 = lean_ctor_get(x_136, 6);
x_153 = lean_ctor_get(x_136, 7);
lean_inc(x_153);
lean_inc(x_152);
lean_inc(x_151);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_136);
x_154 = l_Lean_Kernel_enableDiag(x_147, x_127);
lean_inc(x_4);
lean_ctor_set(x_134, 1, x_4);
lean_ctor_set(x_134, 0, x_4);
x_155 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_148);
lean_ctor_set(x_155, 2, x_149);
lean_ctor_set(x_155, 3, x_150);
lean_ctor_set(x_155, 4, x_134);
lean_ctor_set(x_155, 5, x_151);
lean_ctor_set(x_155, 6, x_152);
lean_ctor_set(x_155, 7, x_153);
x_156 = lean_st_ref_set(x_9, x_155, x_146);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
lean_dec(x_156);
x_158 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_159 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_125, x_127, x_3, x_121, x_7, x_158, x_8, x_9, x_157);
x_28 = x_159;
goto block_37;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_160 = lean_ctor_get(x_134, 0);
x_161 = lean_ctor_get(x_134, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_134);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_160, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 5);
lean_inc(x_166);
x_167 = lean_ctor_get(x_160, 6);
lean_inc(x_167);
x_168 = lean_ctor_get(x_160, 7);
lean_inc(x_168);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 lean_ctor_release(x_160, 2);
 lean_ctor_release(x_160, 3);
 lean_ctor_release(x_160, 4);
 lean_ctor_release(x_160, 5);
 lean_ctor_release(x_160, 6);
 lean_ctor_release(x_160, 7);
 x_169 = x_160;
} else {
 lean_dec_ref(x_160);
 x_169 = lean_box(0);
}
x_170 = l_Lean_Kernel_enableDiag(x_162, x_127);
lean_inc(x_4);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_4);
lean_ctor_set(x_171, 1, x_4);
if (lean_is_scalar(x_169)) {
 x_172 = lean_alloc_ctor(0, 8, 0);
} else {
 x_172 = x_169;
}
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_163);
lean_ctor_set(x_172, 2, x_164);
lean_ctor_set(x_172, 3, x_165);
lean_ctor_set(x_172, 4, x_171);
lean_ctor_set(x_172, 5, x_166);
lean_ctor_set(x_172, 6, x_167);
lean_ctor_set(x_172, 7, x_168);
x_173 = lean_st_ref_set(x_9, x_172, x_161);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_176 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_125, x_127, x_3, x_121, x_7, x_175, x_8, x_9, x_174);
x_28 = x_176;
goto block_37;
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_4);
x_177 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_178 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_125, x_127, x_3, x_121, x_7, x_177, x_8, x_9, x_130);
x_28 = x_178;
goto block_37;
}
}
}
}
else
{
uint8_t x_182; uint8_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; uint8_t x_191; uint8_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint64_t x_204; uint64_t x_205; uint64_t x_206; 
x_182 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_183 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_184 = lean_ctor_get_uint8(x_38, 0);
x_185 = lean_ctor_get_uint8(x_38, 1);
x_186 = lean_ctor_get_uint8(x_38, 2);
x_187 = lean_ctor_get_uint8(x_38, 3);
x_188 = lean_ctor_get_uint8(x_38, 4);
x_189 = lean_ctor_get_uint8(x_38, 5);
x_190 = lean_ctor_get_uint8(x_38, 6);
x_191 = lean_ctor_get_uint8(x_38, 7);
x_192 = lean_ctor_get_uint8(x_38, 8);
x_193 = lean_ctor_get_uint8(x_38, 9);
x_194 = lean_ctor_get_uint8(x_38, 10);
x_195 = lean_ctor_get_uint8(x_38, 11);
x_196 = lean_ctor_get_uint8(x_38, 12);
x_197 = lean_ctor_get_uint8(x_38, 13);
x_198 = lean_ctor_get_uint8(x_38, 14);
x_199 = lean_ctor_get_uint8(x_38, 15);
x_200 = lean_ctor_get_uint8(x_38, 16);
x_201 = lean_ctor_get_uint8(x_38, 17);
lean_dec(x_38);
x_202 = 0;
x_203 = l_Lean_Meta_TransparencyMode_lt(x_193, x_202);
x_204 = 2;
x_205 = lean_uint64_shift_right(x_39, x_204);
x_206 = lean_uint64_shift_left(x_205, x_204);
if (x_203 == 0)
{
lean_object* x_207; uint64_t x_208; uint64_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; uint8_t x_222; 
x_207 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_207, 0, x_184);
lean_ctor_set_uint8(x_207, 1, x_185);
lean_ctor_set_uint8(x_207, 2, x_186);
lean_ctor_set_uint8(x_207, 3, x_187);
lean_ctor_set_uint8(x_207, 4, x_188);
lean_ctor_set_uint8(x_207, 5, x_189);
lean_ctor_set_uint8(x_207, 6, x_190);
lean_ctor_set_uint8(x_207, 7, x_191);
lean_ctor_set_uint8(x_207, 8, x_192);
lean_ctor_set_uint8(x_207, 9, x_193);
lean_ctor_set_uint8(x_207, 10, x_194);
lean_ctor_set_uint8(x_207, 11, x_195);
lean_ctor_set_uint8(x_207, 12, x_196);
lean_ctor_set_uint8(x_207, 13, x_197);
lean_ctor_set_uint8(x_207, 14, x_198);
lean_ctor_set_uint8(x_207, 15, x_199);
lean_ctor_set_uint8(x_207, 16, x_200);
lean_ctor_set_uint8(x_207, 17, x_201);
x_208 = l_Lean_Meta_TransparencyMode_toUInt64(x_193);
x_209 = lean_uint64_lor(x_206, x_208);
x_210 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_41);
lean_ctor_set(x_210, 2, x_42);
lean_ctor_set(x_210, 3, x_43);
lean_ctor_set(x_210, 4, x_44);
lean_ctor_set(x_210, 5, x_45);
lean_ctor_set(x_210, 6, x_46);
lean_ctor_set_uint64(x_210, sizeof(void*)*7, x_209);
lean_ctor_set_uint8(x_210, sizeof(void*)*7 + 8, x_40);
lean_ctor_set_uint8(x_210, sizeof(void*)*7 + 9, x_182);
lean_ctor_set_uint8(x_210, sizeof(void*)*7 + 10, x_183);
x_211 = lean_ctor_get(x_8, 2);
lean_inc(x_211);
x_212 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__3;
x_213 = 0;
x_214 = l_Lean_Option_set___at_Lean_Meta_evalExprCore___spec__1(x_211, x_212, x_213);
x_215 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4;
x_216 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_214, x_215);
x_217 = lean_st_ref_get(x_9, x_10);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
lean_dec(x_218);
x_221 = l_Lean_Kernel_isDiagnosticsEnabled(x_220);
lean_dec(x_220);
if (x_221 == 0)
{
if (x_216 == 0)
{
uint8_t x_245; 
x_245 = 1;
x_222 = x_245;
goto block_244;
}
else
{
x_222 = x_213;
goto block_244;
}
}
else
{
if (x_216 == 0)
{
x_222 = x_213;
goto block_244;
}
else
{
uint8_t x_246; 
x_246 = 1;
x_222 = x_246;
goto block_244;
}
}
block_244:
{
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_223 = lean_st_ref_take(x_9, x_219);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 2);
lean_inc(x_229);
x_230 = lean_ctor_get(x_224, 3);
lean_inc(x_230);
x_231 = lean_ctor_get(x_224, 5);
lean_inc(x_231);
x_232 = lean_ctor_get(x_224, 6);
lean_inc(x_232);
x_233 = lean_ctor_get(x_224, 7);
lean_inc(x_233);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 lean_ctor_release(x_224, 2);
 lean_ctor_release(x_224, 3);
 lean_ctor_release(x_224, 4);
 lean_ctor_release(x_224, 5);
 lean_ctor_release(x_224, 6);
 lean_ctor_release(x_224, 7);
 x_234 = x_224;
} else {
 lean_dec_ref(x_224);
 x_234 = lean_box(0);
}
x_235 = l_Lean_Kernel_enableDiag(x_227, x_216);
lean_inc(x_4);
if (lean_is_scalar(x_226)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_226;
}
lean_ctor_set(x_236, 0, x_4);
lean_ctor_set(x_236, 1, x_4);
if (lean_is_scalar(x_234)) {
 x_237 = lean_alloc_ctor(0, 8, 0);
} else {
 x_237 = x_234;
}
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_228);
lean_ctor_set(x_237, 2, x_229);
lean_ctor_set(x_237, 3, x_230);
lean_ctor_set(x_237, 4, x_236);
lean_ctor_set(x_237, 5, x_231);
lean_ctor_set(x_237, 6, x_232);
lean_ctor_set(x_237, 7, x_233);
x_238 = lean_st_ref_set(x_9, x_237, x_225);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
x_240 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_241 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_214, x_216, x_3, x_210, x_7, x_240, x_8, x_9, x_239);
x_28 = x_241;
goto block_37;
}
else
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_4);
x_242 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_243 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_214, x_216, x_3, x_210, x_7, x_242, x_8, x_9, x_219);
x_28 = x_243;
goto block_37;
}
}
}
else
{
lean_object* x_247; uint64_t x_248; uint64_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; uint8_t x_262; 
x_247 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_247, 0, x_184);
lean_ctor_set_uint8(x_247, 1, x_185);
lean_ctor_set_uint8(x_247, 2, x_186);
lean_ctor_set_uint8(x_247, 3, x_187);
lean_ctor_set_uint8(x_247, 4, x_188);
lean_ctor_set_uint8(x_247, 5, x_189);
lean_ctor_set_uint8(x_247, 6, x_190);
lean_ctor_set_uint8(x_247, 7, x_191);
lean_ctor_set_uint8(x_247, 8, x_192);
lean_ctor_set_uint8(x_247, 9, x_202);
lean_ctor_set_uint8(x_247, 10, x_194);
lean_ctor_set_uint8(x_247, 11, x_195);
lean_ctor_set_uint8(x_247, 12, x_196);
lean_ctor_set_uint8(x_247, 13, x_197);
lean_ctor_set_uint8(x_247, 14, x_198);
lean_ctor_set_uint8(x_247, 15, x_199);
lean_ctor_set_uint8(x_247, 16, x_200);
lean_ctor_set_uint8(x_247, 17, x_201);
x_248 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__5;
x_249 = lean_uint64_lor(x_206, x_248);
x_250 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_41);
lean_ctor_set(x_250, 2, x_42);
lean_ctor_set(x_250, 3, x_43);
lean_ctor_set(x_250, 4, x_44);
lean_ctor_set(x_250, 5, x_45);
lean_ctor_set(x_250, 6, x_46);
lean_ctor_set_uint64(x_250, sizeof(void*)*7, x_249);
lean_ctor_set_uint8(x_250, sizeof(void*)*7 + 8, x_40);
lean_ctor_set_uint8(x_250, sizeof(void*)*7 + 9, x_182);
lean_ctor_set_uint8(x_250, sizeof(void*)*7 + 10, x_183);
x_251 = lean_ctor_get(x_8, 2);
lean_inc(x_251);
x_252 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__3;
x_253 = 0;
x_254 = l_Lean_Option_set___at_Lean_Meta_evalExprCore___spec__1(x_251, x_252, x_253);
x_255 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4;
x_256 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_254, x_255);
x_257 = lean_st_ref_get(x_9, x_10);
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
lean_dec(x_258);
x_261 = l_Lean_Kernel_isDiagnosticsEnabled(x_260);
lean_dec(x_260);
if (x_261 == 0)
{
if (x_256 == 0)
{
uint8_t x_285; 
x_285 = 1;
x_262 = x_285;
goto block_284;
}
else
{
x_262 = x_253;
goto block_284;
}
}
else
{
if (x_256 == 0)
{
x_262 = x_253;
goto block_284;
}
else
{
uint8_t x_286; 
x_286 = 1;
x_262 = x_286;
goto block_284;
}
}
block_284:
{
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_263 = lean_st_ref_take(x_9, x_259);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
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
x_267 = lean_ctor_get(x_264, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_264, 2);
lean_inc(x_269);
x_270 = lean_ctor_get(x_264, 3);
lean_inc(x_270);
x_271 = lean_ctor_get(x_264, 5);
lean_inc(x_271);
x_272 = lean_ctor_get(x_264, 6);
lean_inc(x_272);
x_273 = lean_ctor_get(x_264, 7);
lean_inc(x_273);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 lean_ctor_release(x_264, 2);
 lean_ctor_release(x_264, 3);
 lean_ctor_release(x_264, 4);
 lean_ctor_release(x_264, 5);
 lean_ctor_release(x_264, 6);
 lean_ctor_release(x_264, 7);
 x_274 = x_264;
} else {
 lean_dec_ref(x_264);
 x_274 = lean_box(0);
}
x_275 = l_Lean_Kernel_enableDiag(x_267, x_256);
lean_inc(x_4);
if (lean_is_scalar(x_266)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_266;
}
lean_ctor_set(x_276, 0, x_4);
lean_ctor_set(x_276, 1, x_4);
if (lean_is_scalar(x_274)) {
 x_277 = lean_alloc_ctor(0, 8, 0);
} else {
 x_277 = x_274;
}
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_268);
lean_ctor_set(x_277, 2, x_269);
lean_ctor_set(x_277, 3, x_270);
lean_ctor_set(x_277, 4, x_276);
lean_ctor_set(x_277, 5, x_271);
lean_ctor_set(x_277, 6, x_272);
lean_ctor_set(x_277, 7, x_273);
x_278 = lean_st_ref_set(x_9, x_277, x_265);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_280 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_281 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_254, x_256, x_3, x_250, x_7, x_280, x_8, x_9, x_279);
x_28 = x_281;
goto block_37;
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_4);
x_282 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_283 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_254, x_256, x_3, x_250, x_7, x_282, x_8, x_9, x_259);
x_28 = x_283;
goto block_37;
}
}
}
}
block_27:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_6, x_7, x_8, x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_6, x_7, x_8, x_9, x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__2;
x_20 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_19, x_6, x_7, x_8, x_9, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
return x_11;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_ctor_get(x_11, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_11);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
block_37:
{
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
x_11 = x_28;
goto block_27;
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
x_11 = x_32;
goto block_27;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
x_11 = x_28;
goto block_27;
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
x_11 = x_36;
goto block_27;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq after rwFixEq:", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_11 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_2);
x_14 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_6, x_7, x_8, x_9, x_13);
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
x_19 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3(x_2, x_3, x_12, x_4, x_18, x_6, x_7, x_8, x_9, x_17);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_14, 1);
x_22 = lean_ctor_get(x_14, 0);
lean_dec(x_22);
lean_inc(x_12);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_12);
x_24 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__2;
lean_ctor_set_tag(x_14, 7);
lean_ctor_set(x_14, 1, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_2);
x_27 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_2, x_26, x_6, x_7, x_8, x_9, x_21);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3(x_2, x_3, x_12, x_4, x_28, x_6, x_7, x_8, x_9, x_29);
lean_dec(x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
lean_inc(x_12);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_12);
x_33 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__2;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
lean_inc(x_2);
x_37 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_2, x_36, x_6, x_7, x_8, x_9, x_31);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3(x_2, x_3, x_12, x_4, x_38, x_6, x_7, x_8, x_9, x_39);
lean_dec(x_38);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_41 = !lean_is_exclusive(x_11);
if (x_41 == 0)
{
return x_11;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_11, 0);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_11);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq after deltaLHS:", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_14 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_4);
x_17 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_8, x_9, x_10, x_11, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4(x_15, x_4, x_5, x_6, x_21, x_8, x_9, x_10, x_11, x_20);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_17, 1);
x_25 = lean_ctor_get(x_17, 0);
lean_dec(x_25);
lean_inc(x_15);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_15);
x_27 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__2;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_26);
lean_ctor_set(x_17, 0, x_27);
x_28 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
lean_inc(x_4);
x_30 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_29, x_8, x_9, x_10, x_11, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4(x_15, x_4, x_5, x_6, x_31, x_8, x_9, x_10, x_11, x_32);
lean_dec(x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_dec(x_17);
lean_inc(x_15);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_15);
x_36 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__2;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_4);
x_40 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_39, x_8, x_9, x_10, x_11, x_34);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4(x_15, x_4, x_5, x_6, x_41, x_8, x_9, x_10, x_11, x_42);
lean_dec(x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_14);
if (x_44 == 0)
{
return x_14;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_14, 0);
x_46 = lean_ctor_get(x_14, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_14);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to generate unfold theorem for '", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("':\n", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__2;
x_2 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__5;
x_3 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__6;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq start:", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_box(0);
lean_inc(x_5);
x_28 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_27, x_5, x_6, x_7, x_8, x_9);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = l_Lean_Expr_mvarId_x21(x_30);
x_33 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__7;
x_34 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_33, x_5, x_6, x_7, x_8, x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_28);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_39 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5(x_3, x_1, x_32, x_33, x_30, x_4, x_38, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_10 = x_40;
x_11 = x_41;
goto block_26;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_34, 1);
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
lean_inc(x_32);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_32);
x_46 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__9;
lean_ctor_set_tag(x_34, 7);
lean_ctor_set(x_34, 1, x_45);
lean_ctor_set(x_34, 0, x_46);
x_47 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_47);
lean_ctor_set(x_28, 0, x_34);
x_48 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_33, x_28, x_5, x_6, x_7, x_8, x_43);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_51 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5(x_3, x_1, x_32, x_33, x_30, x_4, x_49, x_5, x_6, x_7, x_8, x_50);
lean_dec(x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_10 = x_52;
x_11 = x_53;
goto block_26;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_34, 1);
lean_inc(x_54);
lean_dec(x_34);
lean_inc(x_32);
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_32);
x_56 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__9;
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
lean_ctor_set_tag(x_28, 7);
lean_ctor_set(x_28, 1, x_58);
lean_ctor_set(x_28, 0, x_57);
x_59 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_33, x_28, x_5, x_6, x_7, x_8, x_54);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_62 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5(x_3, x_1, x_32, x_33, x_30, x_4, x_60, x_5, x_6, x_7, x_8, x_61);
lean_dec(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_10 = x_63;
x_11 = x_64;
goto block_26;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_65 = lean_ctor_get(x_28, 0);
x_66 = lean_ctor_get(x_28, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_28);
x_67 = l_Lean_Expr_mvarId_x21(x_65);
x_68 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__7;
x_69 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_68, x_5, x_6, x_7, x_8, x_66);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_74 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5(x_3, x_1, x_67, x_68, x_65, x_4, x_73, x_5, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_10 = x_75;
x_11 = x_76;
goto block_26;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_78 = x_69;
} else {
 lean_dec_ref(x_69);
 x_78 = lean_box(0);
}
lean_inc(x_67);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_67);
x_80 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__9;
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(7, 2, 0);
} else {
 x_81 = x_78;
 lean_ctor_set_tag(x_81, 7);
}
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
x_82 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_68, x_83, x_5, x_6, x_7, x_8, x_77);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_87 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5(x_3, x_1, x_67, x_68, x_65, x_4, x_85, x_5, x_6, x_7, x_8, x_86);
lean_dec(x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_10 = x_88;
x_11 = x_89;
goto block_26;
}
}
}
block_26:
{
uint8_t x_12; 
x_12 = l_Lean_Exception_isInterrupt(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Exception_isRuntime(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = l_Lean_MessageData_ofName(x_1);
x_15 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__2;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__4;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Exception_toMessageData(x_10);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_22, x_5, x_6, x_7, x_8, x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_10);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_10);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
lean_inc(x_12);
x_14 = l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(x_12, x_13);
lean_inc(x_2);
x_15 = l_Lean_Expr_const___override(x_2, x_14);
x_16 = l_Lean_mkAppN(x_15, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Meta_mkEq(x_16, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_18);
lean_inc(x_2);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6), 9, 4);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_3);
lean_closure_set(x_20, 3, x_4);
x_21 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_20, x_21, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = 1;
x_27 = l_Lean_Meta_mkForallFVars(x_5, x_18, x_21, x_25, x_26, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_mkLambdaFVars(x_5, x_23, x_21, x_25, x_21, x_26, x_7, x_8, x_9, x_10, x_29);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_unfoldThmSuffix;
x_34 = l_Lean_Name_str___override(x_2, x_33);
lean_inc(x_34);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_12);
lean_ctor_set(x_35, 2, x_28);
lean_inc(x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_13);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = l_Lean_addDecl(x_38, x_9, x_10, x_32);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set(x_39, 0, x_34);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_34);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
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
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_30);
if (x_48 == 0)
{
return x_30;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_30, 0);
x_50 = lean_ctor_get(x_30, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_30);
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
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_27);
if (x_52 == 0)
{
return x_27;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_27, 0);
x_54 = lean_ctor_get(x_27, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_27);
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
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_56 = !lean_is_exclusive(x_22);
if (x_56 == 0)
{
return x_22;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_22, 0);
x_58 = lean_ctor_get(x_22, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_22);
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
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_17);
if (x_60 == 0)
{
return x_17;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_17, 0);
x_62 = lean_ctor_get(x_17, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_17);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_8, 4);
lean_dec(x_12);
x_13 = lean_ctor_get(x_8, 2);
lean_dec(x_13);
x_14 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___closed__1;
x_15 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_14);
lean_ctor_set(x_8, 4, x_15);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*12, x_2);
x_16 = 0;
x_17 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_3, x_4, x_16, x_5, x_6, x_8, x_9, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
x_20 = lean_ctor_get(x_8, 3);
x_21 = lean_ctor_get(x_8, 5);
x_22 = lean_ctor_get(x_8, 6);
x_23 = lean_ctor_get(x_8, 7);
x_24 = lean_ctor_get(x_8, 8);
x_25 = lean_ctor_get(x_8, 9);
x_26 = lean_ctor_get(x_8, 10);
x_27 = lean_ctor_get(x_8, 11);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*12 + 1);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
x_29 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___closed__1;
x_30 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_29);
x_31 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_19);
lean_ctor_set(x_31, 2, x_1);
lean_ctor_set(x_31, 3, x_20);
lean_ctor_set(x_31, 4, x_30);
lean_ctor_set(x_31, 5, x_21);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set(x_31, 7, x_23);
lean_ctor_set(x_31, 8, x_24);
lean_ctor_set(x_31, 9, x_25);
lean_ctor_set(x_31, 10, x_26);
lean_ctor_set(x_31, 11, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_31, sizeof(void*)*12 + 1, x_28);
x_32 = 0;
x_33 = l_Lean_Meta_lambdaTelescope___at___private_Lean_Meta_Eqns_0__Lean_Meta_mkSimpleEqThm___spec__1___rarg(x_3, x_4, x_32, x_5, x_6, x_31, x_9, x_10);
return x_33;
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__9___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_hygienic;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_9 = lean_ctor_get(x_6, 2);
lean_inc(x_9);
x_10 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__9___closed__1;
x_11 = 0;
x_12 = l_Lean_Option_set___at_Lean_Meta_evalExprCore___spec__1(x_9, x_10, x_11);
x_13 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4;
x_14 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_12, x_13);
x_15 = lean_st_ref_get(x_7, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Kernel_isDiagnosticsEnabled(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
if (x_14 == 0)
{
uint8_t x_67; 
x_67 = 1;
x_20 = x_67;
goto block_66;
}
else
{
x_20 = x_11;
goto block_66;
}
}
else
{
if (x_14 == 0)
{
x_20 = x_11;
goto block_66;
}
else
{
uint8_t x_68; 
x_68 = 1;
x_20 = x_68;
goto block_66;
}
}
block_66:
{
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_st_ref_take(x_7, x_17);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_21, 1);
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 4);
lean_dec(x_27);
x_28 = l_Lean_Kernel_enableDiag(x_26, x_14);
lean_inc(x_3);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 0, x_28);
x_29 = lean_st_ref_set(x_7, x_23, x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__8(x_12, x_14, x_1, x_2, x_4, x_5, x_31, x_6, x_7, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_21, 1);
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
x_36 = lean_ctor_get(x_23, 2);
x_37 = lean_ctor_get(x_23, 3);
x_38 = lean_ctor_get(x_23, 5);
x_39 = lean_ctor_get(x_23, 6);
x_40 = lean_ctor_get(x_23, 7);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_41 = l_Lean_Kernel_enableDiag(x_34, x_14);
lean_inc(x_3);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 0, x_3);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 4, x_21);
lean_ctor_set(x_42, 5, x_38);
lean_ctor_set(x_42, 6, x_39);
lean_ctor_set(x_42, 7, x_40);
x_43 = lean_st_ref_set(x_7, x_42, x_33);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__8(x_12, x_14, x_1, x_2, x_4, x_5, x_45, x_6, x_7, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_47 = lean_ctor_get(x_21, 0);
x_48 = lean_ctor_get(x_21, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_21);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_47, 7);
lean_inc(x_55);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 lean_ctor_release(x_47, 4);
 lean_ctor_release(x_47, 5);
 lean_ctor_release(x_47, 6);
 lean_ctor_release(x_47, 7);
 x_56 = x_47;
} else {
 lean_dec_ref(x_47);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Kernel_enableDiag(x_49, x_14);
lean_inc(x_3);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_3);
lean_ctor_set(x_58, 1, x_3);
if (lean_is_scalar(x_56)) {
 x_59 = lean_alloc_ctor(0, 8, 0);
} else {
 x_59 = x_56;
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_50);
lean_ctor_set(x_59, 2, x_51);
lean_ctor_set(x_59, 3, x_52);
lean_ctor_set(x_59, 4, x_58);
lean_ctor_set(x_59, 5, x_53);
lean_ctor_set(x_59, 6, x_54);
lean_ctor_set(x_59, 7, x_55);
x_60 = lean_st_ref_set(x_7, x_59, x_48);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__8(x_12, x_14, x_1, x_2, x_4, x_5, x_62, x_6, x_7, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
x_64 = lean_box(0);
x_65 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__8(x_12, x_14, x_1, x_2, x_4, x_5, x_64, x_6, x_7, x_17);
return x_65;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__3() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__1;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
x_2 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 3);
lean_inc(x_9);
x_10 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__7___boxed), 11, 4);
lean_closure_set(x_11, 0, x_8);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__9), 8, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_10);
x_13 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__4;
x_14 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3;
x_15 = l_Lean_Meta_withLCtx___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore___spec__2___rarg(x_13, x_14, x_12, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__8(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
lean_inc(x_2);
x_11 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_9, x_10, x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq(x_2, x_15, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_ctor_set(x_11, 0, x_18);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_11);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
x_27 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq(x_2, x_26, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_30 = x_27;
} else {
 lean_dec_ref(x_27);
 x_30 = lean_box(0);
}
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
if (lean_is_scalar(x_30)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_30;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_35 = x_27;
} else {
 lean_dec_ref(x_27);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_1);
x_8 = l_Lean_Name_str___override(x_1, x_7);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_8);
lean_inc(x_13);
x_14 = l_Lean_Environment_contains(x_13, x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(x_13, x_1, x_15, x_2, x_3, x_4, x_5, x_12);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_9, 0, x_17);
return x_9;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_8);
lean_inc(x_20);
x_21 = l_Lean_Environment_contains(x_20, x_8);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_22 = lean_box(0);
x_23 = l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(x_20, x_1, x_22, x_2, x_3, x_4, x_5, x_19);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_8);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
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
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = 1;
x_20 = l_Lean_Elab_Eqns_mkEqns(x_1, x_18, x_19, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_14, 0, x_22);
lean_ctor_set(x_20, 0, x_14);
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
lean_ctor_set(x_14, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_14);
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
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 1;
x_33 = l_Lean_Elab_Eqns_mkEqns(x_1, x_31, x_32, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
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
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_34);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_33, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_47 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
lean_inc(x_1);
x_48 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_46, x_47, x_45, x_1);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = 1;
x_55 = l_Lean_Elab_Eqns_mkEqns(x_1, x_53, x_54, x_2, x_3, x_4, x_5, x_44);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_58 = x_55;
} else {
 lean_dec_ref(x_55);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_52;
}
lean_ctor_set(x_59, 0, x_56);
if (lean_is_scalar(x_58)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_58;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_57);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_52);
x_61 = lean_ctor_get(x_55, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_63 = x_55;
} else {
 lean_dec_ref(x_55);
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
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_getEqnsFor_x3f), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__1;
x_3 = l_Lean_Meta_registerGetEqnsFn(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__2;
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
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__1 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__2 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__2);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__3 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__3);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__4 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__4);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__5 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55____closed__5);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_55_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_PartialFixpoint_eqnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_eqnInfoExt);
lean_dec_ref(res);
}l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4);
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
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
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
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__2___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__3);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__4);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__5 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__3___closed__5();
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__4___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__5___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__3);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__4);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__5 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__5);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__6 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__6);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__7 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__7);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__8 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__8();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__8);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__9 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__9();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__6___closed__9);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__9___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__9___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___lambda__9___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__3);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__4);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__1 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__2 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618____closed__2);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1618_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
