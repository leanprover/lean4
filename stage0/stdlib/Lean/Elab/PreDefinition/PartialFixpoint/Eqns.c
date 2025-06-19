// Lean compiler output
// Module: Lean.Elab.PreDefinition.PartialFixpoint.Eqns
// Imports: Lean.Elab.Tactic.Conv Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Split Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Eqns Lean.Elab.PreDefinition.FixedParams Lean.Meta.ArgsPacker.Basic Init.Data.Array.Basic Init.Internal.Order.Basic
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
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__6;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__1;
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
lean_object* l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__7;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__4;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____lambda__1(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__2;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__8;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__2;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__5;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17;
extern lean_object* l_Lean_Meta_tactic_hygienic;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__2(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1(lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
extern lean_object* l_Lean_maxRecDepth;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__6;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* l_List_mapTR_loop___at_Lean_mkConstWithLevelParams___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_smartUnfolding;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__25;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__23;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__1;
extern lean_object* l_Lean_levelZero;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_appFn_x21___spec__1(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__2;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__7;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__5;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__2;
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__3;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3;
lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1___boxed(lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__5;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1(lean_object*);
static lean_object* l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__3;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__2___closed__7;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1;
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_unfoldThmSuffix;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__6;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__26;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679_(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__9;
lean_object* l_Lean_Elab_Eqns_mkEqns(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_panic___at_Lean_Meta_subst_substEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1;
static size_t l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19;
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4;
x_2 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5;
x_3 = lean_box(0);
x_4 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__6;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__7;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Lean_RBNode_fold___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__2(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
static lean_object* _init_l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1___closed__1;
x_3 = l_Lean_RBNode_fold___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PartialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqnInfoExt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__2;
x_3 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__3;
x_4 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____lambda__1___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__5;
x_3 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__6;
x_4 = l_Lean_mkMapDeclarationExtension___rarg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____lambda__1(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_10 = lean_array_uget(x_5, x_6);
x_11 = lean_ctor_get(x_10, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 5);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_11);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_4);
x_16 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
lean_ctor_set(x_16, 2, x_1);
lean_ctor_set(x_16, 3, x_2);
lean_ctor_set(x_16, 4, x_3);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
x_18 = l_Lean_MapDeclarationExtension_insert___rarg(x_17, x_8, x_11, x_16);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_8 = x_18;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_84; uint8_t x_85; 
x_10 = lean_array_get_size(x_1);
x_84 = lean_unsigned_to_nat(0u);
x_85 = lean_nat_dec_lt(x_84, x_10);
if (x_85 == 0)
{
x_11 = x_9;
goto block_83;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_10, x_10);
if (x_86 == 0)
{
x_11 = x_9;
goto block_83;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_10);
x_89 = lean_box(0);
x_90 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__5(x_1, x_87, x_88, x_89, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_11 = x_91;
goto block_83;
}
else
{
uint8_t x_92; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_90);
if (x_92 == 0)
{
return x_90;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_90, 0);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_90);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
block_83:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_10);
x_18 = l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__1(x_1, x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; lean_object* x_72; 
lean_inc(x_8);
lean_inc(x_6);
x_72 = l_Array_anyMUnsafe_any___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__4(x_1, x_16, x_17, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = 1;
x_21 = x_76;
x_22 = x_75;
goto block_71;
}
else
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
lean_dec(x_72);
x_78 = 0;
x_21 = x_78;
x_22 = x_77;
goto block_71;
}
}
else
{
uint8_t x_79; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_72);
if (x_79 == 0)
{
return x_72;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_72, 0);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_72);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
block_71:
{
if (x_21 == 0)
{
size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_67; 
x_23 = lean_array_size(x_1);
lean_inc(x_1);
x_24 = l_Array_mapMUnsafe_map___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__2(x_23, x_16, x_1);
x_25 = lean_st_ref_take(x_8, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 7);
lean_inc(x_34);
x_35 = lean_ctor_get(x_26, 8);
lean_inc(x_35);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 lean_ctor_release(x_26, 6);
 lean_ctor_release(x_26, 7);
 lean_ctor_release(x_26, 8);
 x_36 = x_26;
} else {
 lean_dec_ref(x_26);
 x_36 = lean_box(0);
}
x_67 = lean_nat_dec_le(x_10, x_10);
lean_dec(x_10);
if (x_67 == 0)
{
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = x_28;
goto block_66;
}
else
{
lean_object* x_68; 
x_68 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3(x_2, x_3, x_4, x_24, x_1, x_16, x_17, x_28);
lean_dec(x_1);
x_37 = x_68;
goto block_66;
}
block_66:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_38 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
if (lean_is_scalar(x_36)) {
 x_39 = lean_alloc_ctor(0, 9, 0);
} else {
 x_39 = x_36;
}
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_30);
lean_ctor_set(x_39, 3, x_31);
lean_ctor_set(x_39, 4, x_32);
lean_ctor_set(x_39, 5, x_38);
lean_ctor_set(x_39, 6, x_33);
lean_ctor_set(x_39, 7, x_34);
lean_ctor_set(x_39, 8, x_35);
x_40 = lean_st_ref_set(x_8, x_39, x_27);
lean_dec(x_8);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_ref_take(x_6, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_43, 1);
lean_dec(x_46);
x_47 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4;
lean_ctor_set(x_43, 1, x_47);
x_48 = lean_st_ref_set(x_6, x_43, x_44);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(0);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_55 = lean_ctor_get(x_43, 0);
x_56 = lean_ctor_get(x_43, 2);
x_57 = lean_ctor_get(x_43, 3);
x_58 = lean_ctor_get(x_43, 4);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_43);
x_59 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4;
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_57);
lean_ctor_set(x_60, 4, x_58);
x_61 = lean_st_ref_set(x_6, x_60, x_44);
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
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_22);
return x_70;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec(x_5);
return x_11;
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
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1;
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
x_1 = lean_mk_string_unchecked("lfp_monotone", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
x_3 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rwFixUnder: unexpected expression ", 34, 34);
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
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("p", 1, 1);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrArg", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
x_3 = lean_unsigned_to_nat(1809u);
x_4 = lean_unsigned_to_nat(18u);
x_5 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static size_t _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
x_2 = lean_ptr_addr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congrFun", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lfp_monotone_fix", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
x_3 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix_eq", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
x_3 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__25;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
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
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5;
x_11 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isApp(x_1);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_isProj(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = l_Lean_MessageData_ofExpr(x_1);
x_15 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_18, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Expr_projExpr_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_20);
x_21 = lean_infer_type(x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_24 = l_Lean_Elab_PartialFixpoint_rwFixUnder(x_20, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
x_45 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_46 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19;
x_47 = lean_usize_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_1);
x_48 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
x_49 = l_Lean_Expr_proj___override(x_42, x_43, x_48);
x_25 = x_49;
goto block_41;
}
else
{
lean_dec(x_43);
lean_dec(x_42);
x_25 = x_1;
goto block_41;
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_50 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
x_51 = l_panic___at_Lean_Expr_appFn_x21___spec__1(x_50);
x_25 = x_51;
goto block_41;
}
block_41:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
x_29 = 0;
x_30 = l_Lean_Expr_lam___override(x_28, x_22, x_25, x_29);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_array_mk(x_33);
x_35 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
x_36 = l_Lean_Meta_mkAppM(x_35, x_34, x_2, x_3, x_4, x_5, x_27);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
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
uint8_t x_52; 
lean_dec(x_20);
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
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_57 = l_Lean_Elab_PartialFixpoint_rwFixUnder(x_56, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_Expr_appArg_x21(x_1);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_mk(x_63);
x_65 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
x_66 = l_Lean_Meta_mkAppM(x_65, x_64, x_2, x_3, x_4, x_5, x_59);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_57);
if (x_67 == 0)
{
return x_57;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_57, 0);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_57);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = l_Lean_Expr_getAppFn(x_1);
x_72 = l_Lean_Expr_constLevels_x21(x_71);
lean_dec(x_71);
x_73 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__23;
x_74 = l_Lean_Expr_const___override(x_73, x_72);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_75);
x_77 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24;
lean_inc(x_76);
x_78 = lean_mk_array(x_76, x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_nat_sub(x_76, x_79);
lean_dec(x_76);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_78, x_80);
x_82 = l_Lean_mkAppN(x_74, x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_6);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = l_Lean_Expr_getAppFn(x_1);
x_85 = l_Lean_Expr_constLevels_x21(x_84);
lean_dec(x_84);
x_86 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__26;
x_87 = l_Lean_Expr_const___override(x_86, x_85);
x_88 = lean_unsigned_to_nat(0u);
x_89 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_88);
x_90 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24;
lean_inc(x_89);
x_91 = lean_mk_array(x_89, x_90);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_sub(x_89, x_92);
lean_dec(x_89);
x_94 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_91, x_93);
x_95 = l_Lean_mkAppN(x_87, x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_6);
return x_96;
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
x_3 = lean_unsigned_to_nat(65u);
x_4 = lean_unsigned_to_nat(41u);
x_5 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__1;
x_2 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__2;
x_3 = lean_unsigned_to_nat(67u);
x_4 = lean_unsigned_to_nat(51u);
x_5 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lambda__1___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_13 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___closed__1;
x_14 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_13);
lean_ctor_set(x_7, 4, x_14);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*13, x_2);
x_15 = l_Lean_MVarId_refl(x_3, x_4, x_5, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
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
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_27 = lean_ctor_get(x_7, 12);
lean_inc(x_27);
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
x_28 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___closed__1;
x_29 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_28);
x_30 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_17);
lean_ctor_set(x_30, 2, x_1);
lean_ctor_set(x_30, 3, x_18);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_19);
lean_ctor_set(x_30, 6, x_20);
lean_ctor_set(x_30, 7, x_21);
lean_ctor_set(x_30, 8, x_22);
lean_ctor_set(x_30, 9, x_23);
lean_ctor_set(x_30, 10, x_24);
lean_ctor_set(x_30, 11, x_25);
lean_ctor_set(x_30, 12, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_30, sizeof(void*)*13 + 1, x_26);
x_31 = l_Lean_MVarId_refl(x_3, x_4, x_5, x_30, x_8, x_9);
return x_31;
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq rfl succeeded", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_smartUnfolding;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static uint64_t _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__5() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 0;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_27; uint64_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_ctor_get(x_5, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint64(x_5, sizeof(void*)*7);
x_29 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_5, 2);
lean_inc(x_31);
x_32 = lean_ctor_get(x_5, 3);
lean_inc(x_32);
x_33 = lean_ctor_get(x_5, 4);
lean_inc(x_33);
x_34 = lean_ctor_get(x_5, 5);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 6);
lean_inc(x_35);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; 
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_38 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_39 = lean_ctor_get_uint8(x_27, 9);
x_40 = 0;
x_41 = l_Lean_Meta_TransparencyMode_lt(x_39, x_40);
x_42 = 2;
x_43 = lean_uint64_shift_right(x_28, x_42);
x_44 = lean_uint64_shift_left(x_43, x_42);
if (x_41 == 0)
{
uint64_t x_45; uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_87; 
x_45 = l_Lean_Meta_TransparencyMode_toUInt64(x_39);
x_46 = lean_uint64_lor(x_44, x_45);
x_47 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_47, 0, x_27);
lean_ctor_set(x_47, 1, x_30);
lean_ctor_set(x_47, 2, x_31);
lean_ctor_set(x_47, 3, x_32);
lean_ctor_set(x_47, 4, x_33);
lean_ctor_set(x_47, 5, x_34);
lean_ctor_set(x_47, 6, x_35);
lean_ctor_set_uint64(x_47, sizeof(void*)*7, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*7 + 8, x_29);
lean_ctor_set_uint8(x_47, sizeof(void*)*7 + 9, x_37);
lean_ctor_set_uint8(x_47, sizeof(void*)*7 + 10, x_38);
x_48 = lean_ctor_get(x_7, 2);
lean_inc(x_48);
x_49 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__3;
x_50 = 0;
x_51 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(x_48, x_49, x_50);
x_52 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4;
x_53 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_51, x_52);
x_54 = lean_st_ref_get(x_8, x_9);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_87 = l_Lean_Kernel_isDiagnosticsEnabled(x_57);
lean_dec(x_57);
if (x_87 == 0)
{
if (x_53 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_89 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_51, x_53, x_3, x_47, x_6, x_88, x_7, x_8, x_56);
x_10 = x_89;
goto block_26;
}
else
{
lean_object* x_90; 
x_90 = lean_box(0);
x_58 = x_90;
goto block_86;
}
}
else
{
if (x_53 == 0)
{
lean_object* x_91; 
x_91 = lean_box(0);
x_58 = x_91;
goto block_86;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_93 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_51, x_53, x_3, x_47, x_6, x_92, x_7, x_8, x_56);
x_10 = x_93;
goto block_26;
}
}
block_86:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_58);
x_59 = lean_st_ref_take(x_8, x_56);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = !lean_is_exclusive(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_60, 0);
x_64 = lean_ctor_get(x_60, 5);
lean_dec(x_64);
x_65 = l_Lean_Kernel_enableDiag(x_63, x_53);
x_66 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
lean_ctor_set(x_60, 5, x_66);
lean_ctor_set(x_60, 0, x_65);
x_67 = lean_st_ref_set(x_8, x_60, x_61);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_70 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_51, x_53, x_3, x_47, x_6, x_69, x_7, x_8, x_68);
x_10 = x_70;
goto block_26;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_71 = lean_ctor_get(x_60, 0);
x_72 = lean_ctor_get(x_60, 1);
x_73 = lean_ctor_get(x_60, 2);
x_74 = lean_ctor_get(x_60, 3);
x_75 = lean_ctor_get(x_60, 4);
x_76 = lean_ctor_get(x_60, 6);
x_77 = lean_ctor_get(x_60, 7);
x_78 = lean_ctor_get(x_60, 8);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_60);
x_79 = l_Lean_Kernel_enableDiag(x_71, x_53);
x_80 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
x_81 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_72);
lean_ctor_set(x_81, 2, x_73);
lean_ctor_set(x_81, 3, x_74);
lean_ctor_set(x_81, 4, x_75);
lean_ctor_set(x_81, 5, x_80);
lean_ctor_set(x_81, 6, x_76);
lean_ctor_set(x_81, 7, x_77);
lean_ctor_set(x_81, 8, x_78);
x_82 = lean_st_ref_set(x_8, x_81, x_61);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_85 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_51, x_53, x_3, x_47, x_6, x_84, x_7, x_8, x_83);
x_10 = x_85;
goto block_26;
}
}
}
else
{
uint64_t x_94; uint64_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_136; 
lean_ctor_set_uint8(x_27, 9, x_40);
x_94 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__5;
x_95 = lean_uint64_lor(x_44, x_94);
x_96 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_96, 0, x_27);
lean_ctor_set(x_96, 1, x_30);
lean_ctor_set(x_96, 2, x_31);
lean_ctor_set(x_96, 3, x_32);
lean_ctor_set(x_96, 4, x_33);
lean_ctor_set(x_96, 5, x_34);
lean_ctor_set(x_96, 6, x_35);
lean_ctor_set_uint64(x_96, sizeof(void*)*7, x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*7 + 8, x_29);
lean_ctor_set_uint8(x_96, sizeof(void*)*7 + 9, x_37);
lean_ctor_set_uint8(x_96, sizeof(void*)*7 + 10, x_38);
x_97 = lean_ctor_get(x_7, 2);
lean_inc(x_97);
x_98 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__3;
x_99 = 0;
x_100 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(x_97, x_98, x_99);
x_101 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4;
x_102 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_100, x_101);
x_103 = lean_st_ref_get(x_8, x_9);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_ctor_get(x_104, 0);
lean_inc(x_106);
lean_dec(x_104);
x_136 = l_Lean_Kernel_isDiagnosticsEnabled(x_106);
lean_dec(x_106);
if (x_136 == 0)
{
if (x_102 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_138 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_100, x_102, x_3, x_96, x_6, x_137, x_7, x_8, x_105);
x_10 = x_138;
goto block_26;
}
else
{
lean_object* x_139; 
x_139 = lean_box(0);
x_107 = x_139;
goto block_135;
}
}
else
{
if (x_102 == 0)
{
lean_object* x_140; 
x_140 = lean_box(0);
x_107 = x_140;
goto block_135;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_142 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_100, x_102, x_3, x_96, x_6, x_141, x_7, x_8, x_105);
x_10 = x_142;
goto block_26;
}
}
block_135:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
lean_dec(x_107);
x_108 = lean_st_ref_take(x_8, x_105);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = !lean_is_exclusive(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_ctor_get(x_109, 0);
x_113 = lean_ctor_get(x_109, 5);
lean_dec(x_113);
x_114 = l_Lean_Kernel_enableDiag(x_112, x_102);
x_115 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
lean_ctor_set(x_109, 5, x_115);
lean_ctor_set(x_109, 0, x_114);
x_116 = lean_st_ref_set(x_8, x_109, x_110);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_119 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_100, x_102, x_3, x_96, x_6, x_118, x_7, x_8, x_117);
x_10 = x_119;
goto block_26;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_ctor_get(x_109, 0);
x_121 = lean_ctor_get(x_109, 1);
x_122 = lean_ctor_get(x_109, 2);
x_123 = lean_ctor_get(x_109, 3);
x_124 = lean_ctor_get(x_109, 4);
x_125 = lean_ctor_get(x_109, 6);
x_126 = lean_ctor_get(x_109, 7);
x_127 = lean_ctor_get(x_109, 8);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_109);
x_128 = l_Lean_Kernel_enableDiag(x_120, x_102);
x_129 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
x_130 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_121);
lean_ctor_set(x_130, 2, x_122);
lean_ctor_set(x_130, 3, x_123);
lean_ctor_set(x_130, 4, x_124);
lean_ctor_set(x_130, 5, x_129);
lean_ctor_set(x_130, 6, x_125);
lean_ctor_set(x_130, 7, x_126);
lean_ctor_set(x_130, 8, x_127);
x_131 = lean_st_ref_set(x_8, x_130, x_110);
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_134 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_100, x_102, x_3, x_96, x_6, x_133, x_7, x_8, x_132);
x_10 = x_134;
goto block_26;
}
}
}
}
else
{
uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; uint8_t x_150; uint8_t x_151; uint8_t x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint64_t x_165; uint64_t x_166; uint64_t x_167; 
x_143 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_144 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
x_145 = lean_ctor_get_uint8(x_27, 0);
x_146 = lean_ctor_get_uint8(x_27, 1);
x_147 = lean_ctor_get_uint8(x_27, 2);
x_148 = lean_ctor_get_uint8(x_27, 3);
x_149 = lean_ctor_get_uint8(x_27, 4);
x_150 = lean_ctor_get_uint8(x_27, 5);
x_151 = lean_ctor_get_uint8(x_27, 6);
x_152 = lean_ctor_get_uint8(x_27, 7);
x_153 = lean_ctor_get_uint8(x_27, 8);
x_154 = lean_ctor_get_uint8(x_27, 9);
x_155 = lean_ctor_get_uint8(x_27, 10);
x_156 = lean_ctor_get_uint8(x_27, 11);
x_157 = lean_ctor_get_uint8(x_27, 12);
x_158 = lean_ctor_get_uint8(x_27, 13);
x_159 = lean_ctor_get_uint8(x_27, 14);
x_160 = lean_ctor_get_uint8(x_27, 15);
x_161 = lean_ctor_get_uint8(x_27, 16);
x_162 = lean_ctor_get_uint8(x_27, 17);
lean_dec(x_27);
x_163 = 0;
x_164 = l_Lean_Meta_TransparencyMode_lt(x_154, x_163);
x_165 = 2;
x_166 = lean_uint64_shift_right(x_28, x_165);
x_167 = lean_uint64_shift_left(x_166, x_165);
if (x_164 == 0)
{
lean_object* x_168; uint64_t x_169; uint64_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_203; 
x_168 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_168, 0, x_145);
lean_ctor_set_uint8(x_168, 1, x_146);
lean_ctor_set_uint8(x_168, 2, x_147);
lean_ctor_set_uint8(x_168, 3, x_148);
lean_ctor_set_uint8(x_168, 4, x_149);
lean_ctor_set_uint8(x_168, 5, x_150);
lean_ctor_set_uint8(x_168, 6, x_151);
lean_ctor_set_uint8(x_168, 7, x_152);
lean_ctor_set_uint8(x_168, 8, x_153);
lean_ctor_set_uint8(x_168, 9, x_154);
lean_ctor_set_uint8(x_168, 10, x_155);
lean_ctor_set_uint8(x_168, 11, x_156);
lean_ctor_set_uint8(x_168, 12, x_157);
lean_ctor_set_uint8(x_168, 13, x_158);
lean_ctor_set_uint8(x_168, 14, x_159);
lean_ctor_set_uint8(x_168, 15, x_160);
lean_ctor_set_uint8(x_168, 16, x_161);
lean_ctor_set_uint8(x_168, 17, x_162);
x_169 = l_Lean_Meta_TransparencyMode_toUInt64(x_154);
x_170 = lean_uint64_lor(x_167, x_169);
x_171 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_30);
lean_ctor_set(x_171, 2, x_31);
lean_ctor_set(x_171, 3, x_32);
lean_ctor_set(x_171, 4, x_33);
lean_ctor_set(x_171, 5, x_34);
lean_ctor_set(x_171, 6, x_35);
lean_ctor_set_uint64(x_171, sizeof(void*)*7, x_170);
lean_ctor_set_uint8(x_171, sizeof(void*)*7 + 8, x_29);
lean_ctor_set_uint8(x_171, sizeof(void*)*7 + 9, x_143);
lean_ctor_set_uint8(x_171, sizeof(void*)*7 + 10, x_144);
x_172 = lean_ctor_get(x_7, 2);
lean_inc(x_172);
x_173 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__3;
x_174 = 0;
x_175 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(x_172, x_173, x_174);
x_176 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4;
x_177 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_175, x_176);
x_178 = lean_st_ref_get(x_8, x_9);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
lean_dec(x_179);
x_203 = l_Lean_Kernel_isDiagnosticsEnabled(x_181);
lean_dec(x_181);
if (x_203 == 0)
{
if (x_177 == 0)
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_205 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_175, x_177, x_3, x_171, x_6, x_204, x_7, x_8, x_180);
x_10 = x_205;
goto block_26;
}
else
{
lean_object* x_206; 
x_206 = lean_box(0);
x_182 = x_206;
goto block_202;
}
}
else
{
if (x_177 == 0)
{
lean_object* x_207; 
x_207 = lean_box(0);
x_182 = x_207;
goto block_202;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_209 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_175, x_177, x_3, x_171, x_6, x_208, x_7, x_8, x_180);
x_10 = x_209;
goto block_26;
}
}
block_202:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_182);
x_183 = lean_st_ref_take(x_8, x_180);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_ctor_get(x_184, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 2);
lean_inc(x_188);
x_189 = lean_ctor_get(x_184, 3);
lean_inc(x_189);
x_190 = lean_ctor_get(x_184, 4);
lean_inc(x_190);
x_191 = lean_ctor_get(x_184, 6);
lean_inc(x_191);
x_192 = lean_ctor_get(x_184, 7);
lean_inc(x_192);
x_193 = lean_ctor_get(x_184, 8);
lean_inc(x_193);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 lean_ctor_release(x_184, 2);
 lean_ctor_release(x_184, 3);
 lean_ctor_release(x_184, 4);
 lean_ctor_release(x_184, 5);
 lean_ctor_release(x_184, 6);
 lean_ctor_release(x_184, 7);
 lean_ctor_release(x_184, 8);
 x_194 = x_184;
} else {
 lean_dec_ref(x_184);
 x_194 = lean_box(0);
}
x_195 = l_Lean_Kernel_enableDiag(x_186, x_177);
x_196 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
if (lean_is_scalar(x_194)) {
 x_197 = lean_alloc_ctor(0, 9, 0);
} else {
 x_197 = x_194;
}
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_187);
lean_ctor_set(x_197, 2, x_188);
lean_ctor_set(x_197, 3, x_189);
lean_ctor_set(x_197, 4, x_190);
lean_ctor_set(x_197, 5, x_196);
lean_ctor_set(x_197, 6, x_191);
lean_ctor_set(x_197, 7, x_192);
lean_ctor_set(x_197, 8, x_193);
x_198 = lean_st_ref_set(x_8, x_197, x_185);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_201 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_175, x_177, x_3, x_171, x_6, x_200, x_7, x_8, x_199);
x_10 = x_201;
goto block_26;
}
}
else
{
lean_object* x_210; uint64_t x_211; uint64_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_245; 
x_210 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_210, 0, x_145);
lean_ctor_set_uint8(x_210, 1, x_146);
lean_ctor_set_uint8(x_210, 2, x_147);
lean_ctor_set_uint8(x_210, 3, x_148);
lean_ctor_set_uint8(x_210, 4, x_149);
lean_ctor_set_uint8(x_210, 5, x_150);
lean_ctor_set_uint8(x_210, 6, x_151);
lean_ctor_set_uint8(x_210, 7, x_152);
lean_ctor_set_uint8(x_210, 8, x_153);
lean_ctor_set_uint8(x_210, 9, x_163);
lean_ctor_set_uint8(x_210, 10, x_155);
lean_ctor_set_uint8(x_210, 11, x_156);
lean_ctor_set_uint8(x_210, 12, x_157);
lean_ctor_set_uint8(x_210, 13, x_158);
lean_ctor_set_uint8(x_210, 14, x_159);
lean_ctor_set_uint8(x_210, 15, x_160);
lean_ctor_set_uint8(x_210, 16, x_161);
lean_ctor_set_uint8(x_210, 17, x_162);
x_211 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__5;
x_212 = lean_uint64_lor(x_167, x_211);
x_213 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_30);
lean_ctor_set(x_213, 2, x_31);
lean_ctor_set(x_213, 3, x_32);
lean_ctor_set(x_213, 4, x_33);
lean_ctor_set(x_213, 5, x_34);
lean_ctor_set(x_213, 6, x_35);
lean_ctor_set_uint64(x_213, sizeof(void*)*7, x_212);
lean_ctor_set_uint8(x_213, sizeof(void*)*7 + 8, x_29);
lean_ctor_set_uint8(x_213, sizeof(void*)*7 + 9, x_143);
lean_ctor_set_uint8(x_213, sizeof(void*)*7 + 10, x_144);
x_214 = lean_ctor_get(x_7, 2);
lean_inc(x_214);
x_215 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__3;
x_216 = 0;
x_217 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(x_214, x_215, x_216);
x_218 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4;
x_219 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_217, x_218);
x_220 = lean_st_ref_get(x_8, x_9);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_221, 0);
lean_inc(x_223);
lean_dec(x_221);
x_245 = l_Lean_Kernel_isDiagnosticsEnabled(x_223);
lean_dec(x_223);
if (x_245 == 0)
{
if (x_219 == 0)
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_247 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_217, x_219, x_3, x_213, x_6, x_246, x_7, x_8, x_222);
x_10 = x_247;
goto block_26;
}
else
{
lean_object* x_248; 
x_248 = lean_box(0);
x_224 = x_248;
goto block_244;
}
}
else
{
if (x_219 == 0)
{
lean_object* x_249; 
x_249 = lean_box(0);
x_224 = x_249;
goto block_244;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_251 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_217, x_219, x_3, x_213, x_6, x_250, x_7, x_8, x_222);
x_10 = x_251;
goto block_26;
}
}
block_244:
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_224);
x_225 = lean_st_ref_take(x_8, x_222);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_226, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_226, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_226, 3);
lean_inc(x_231);
x_232 = lean_ctor_get(x_226, 4);
lean_inc(x_232);
x_233 = lean_ctor_get(x_226, 6);
lean_inc(x_233);
x_234 = lean_ctor_get(x_226, 7);
lean_inc(x_234);
x_235 = lean_ctor_get(x_226, 8);
lean_inc(x_235);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 lean_ctor_release(x_226, 3);
 lean_ctor_release(x_226, 4);
 lean_ctor_release(x_226, 5);
 lean_ctor_release(x_226, 6);
 lean_ctor_release(x_226, 7);
 lean_ctor_release(x_226, 8);
 x_236 = x_226;
} else {
 lean_dec_ref(x_226);
 x_236 = lean_box(0);
}
x_237 = l_Lean_Kernel_enableDiag(x_228, x_219);
x_238 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
if (lean_is_scalar(x_236)) {
 x_239 = lean_alloc_ctor(0, 9, 0);
} else {
 x_239 = x_236;
}
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_229);
lean_ctor_set(x_239, 2, x_230);
lean_ctor_set(x_239, 3, x_231);
lean_ctor_set(x_239, 4, x_232);
lean_ctor_set(x_239, 5, x_238);
lean_ctor_set(x_239, 6, x_233);
lean_ctor_set(x_239, 7, x_234);
lean_ctor_set(x_239, 8, x_235);
x_240 = lean_st_ref_set(x_8, x_239, x_227);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_243 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_217, x_219, x_3, x_213, x_6, x_242, x_7, x_8, x_241);
x_10 = x_243;
goto block_26;
}
}
}
block_26:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_1, x_5, x_6, x_7, x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__2;
x_19 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_1, x_18, x_5, x_6, x_7, x_8, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_2, x_5, x_6, x_7, x_8, x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
return x_10;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_10);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq after rwFixEq:", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_2);
x_13 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_2, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3(x_2, x_3, x_11, x_17, x_5, x_6, x_7, x_8, x_16);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_13, 1);
x_21 = lean_ctor_get(x_13, 0);
lean_dec(x_21);
lean_inc(x_11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_11);
x_23 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__2;
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_22);
lean_ctor_set(x_13, 0, x_23);
x_24 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_2);
x_26 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_2, x_25, x_5, x_6, x_7, x_8, x_20);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3(x_2, x_3, x_11, x_27, x_5, x_6, x_7, x_8, x_28);
lean_dec(x_27);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_13, 1);
lean_inc(x_30);
lean_dec(x_13);
lean_inc(x_11);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_11);
x_32 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__2;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_inc(x_2);
x_36 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_2, x_35, x_5, x_6, x_7, x_8, x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3(x_2, x_3, x_11, x_37, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_37);
return x_39;
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
lean_dec(x_3);
lean_dec(x_2);
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq after deltaLHS:", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(x_2, x_12, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_4);
x_16 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_4, x_7, x_8, x_9, x_10, x_15);
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
x_21 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4(x_14, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_16, 1);
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
lean_inc(x_14);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_14);
x_26 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__2;
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_25);
lean_ctor_set(x_16, 0, x_26);
x_27 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_16);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_4);
x_29 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_28, x_7, x_8, x_9, x_10, x_23);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4(x_14, x_4, x_5, x_30, x_7, x_8, x_9, x_10, x_31);
lean_dec(x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
lean_inc(x_14);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_14);
x_35 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__2;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_4);
x_39 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_4, x_38, x_7, x_8, x_9, x_10, x_33);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4(x_14, x_4, x_5, x_40, x_7, x_8, x_9, x_10, x_41);
lean_dec(x_40);
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
lean_dec(x_5);
lean_dec(x_4);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to generate unfold theorem for '", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("':\n", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__2;
x_2 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__5;
x_3 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__6;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq start:", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_box(0);
lean_inc(x_4);
x_27 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_26, x_4, x_5, x_6, x_7, x_8);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = l_Lean_Expr_mvarId_x21(x_29);
x_32 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__7;
x_33 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_32, x_4, x_5, x_6, x_7, x_30);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_27);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_38 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5(x_3, x_1, x_31, x_32, x_29, x_37, x_4, x_5, x_6, x_7, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_9 = x_39;
x_10 = x_40;
goto block_25;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_33, 1);
x_43 = lean_ctor_get(x_33, 0);
lean_dec(x_43);
lean_inc(x_31);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_31);
x_45 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__9;
lean_ctor_set_tag(x_33, 7);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_45);
x_46 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_46);
lean_ctor_set(x_27, 0, x_33);
x_47 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_32, x_27, x_4, x_5, x_6, x_7, x_42);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_50 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5(x_3, x_1, x_31, x_32, x_29, x_48, x_4, x_5, x_6, x_7, x_49);
lean_dec(x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_9 = x_51;
x_10 = x_52;
goto block_25;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_33, 1);
lean_inc(x_53);
lean_dec(x_33);
lean_inc(x_31);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_31);
x_55 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__9;
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_57);
lean_ctor_set(x_27, 0, x_56);
x_58 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_32, x_27, x_4, x_5, x_6, x_7, x_53);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_61 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5(x_3, x_1, x_31, x_32, x_29, x_59, x_4, x_5, x_6, x_7, x_60);
lean_dec(x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_9 = x_62;
x_10 = x_63;
goto block_25;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_27, 0);
x_65 = lean_ctor_get(x_27, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_27);
x_66 = l_Lean_Expr_mvarId_x21(x_64);
x_67 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__7;
x_68 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_67, x_4, x_5, x_6, x_7, x_65);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_73 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5(x_3, x_1, x_66, x_67, x_64, x_72, x_4, x_5, x_6, x_7, x_71);
if (lean_obj_tag(x_73) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_9 = x_74;
x_10 = x_75;
goto block_25;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_77 = x_68;
} else {
 lean_dec_ref(x_68);
 x_77 = lean_box(0);
}
lean_inc(x_66);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_66);
x_79 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__9;
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(7, 2, 0);
} else {
 x_80 = x_77;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
x_81 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_67, x_82, x_4, x_5, x_6, x_7, x_76);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_86 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5(x_3, x_1, x_66, x_67, x_64, x_84, x_4, x_5, x_6, x_7, x_85);
lean_dec(x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_9 = x_87;
x_10 = x_88;
goto block_25;
}
}
}
block_25:
{
uint8_t x_11; 
x_11 = l_Lean_Exception_isInterrupt(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Lean_Exception_isRuntime(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = l_Lean_MessageData_ofName(x_1);
x_14 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__2;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__4;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Exception_toMessageData(x_9);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_21, x_4, x_5, x_6, x_7, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6), 8, 3);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_3);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_4);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_12);
lean_ctor_set(x_33, 2, x_28);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_13);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lean_addDecl(x_36, x_9, x_10, x_32);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_28);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
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
else
{
uint8_t x_42; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
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
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__8(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_14 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___closed__1;
x_15 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_14);
lean_ctor_set(x_8, 4, x_15);
lean_ctor_set(x_8, 2, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*13, x_2);
x_16 = 0;
x_17 = l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg(x_3, x_4, x_16, x_5, x_6, x_8, x_9, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
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
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_29 = lean_ctor_get(x_8, 12);
lean_inc(x_29);
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
x_30 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___closed__1;
x_31 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_30);
x_32 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_1);
lean_ctor_set(x_32, 3, x_20);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set(x_32, 5, x_21);
lean_ctor_set(x_32, 6, x_22);
lean_ctor_set(x_32, 7, x_23);
lean_ctor_set(x_32, 8, x_24);
lean_ctor_set(x_32, 9, x_25);
lean_ctor_set(x_32, 10, x_26);
lean_ctor_set(x_32, 11, x_27);
lean_ctor_set(x_32, 12, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*13, x_2);
lean_ctor_set_uint8(x_32, sizeof(void*)*13 + 1, x_28);
x_33 = 0;
x_34 = l_Lean_Meta_lambdaTelescope___at_Lean_PrettyPrinter_Delaborator_returnsPi___spec__1___rarg(x_3, x_4, x_33, x_5, x_6, x_32, x_9, x_10);
return x_34;
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_hygienic;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_51; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__7___boxed), 11, 4);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__1;
x_14 = 0;
x_15 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__3(x_12, x_13, x_14);
x_16 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4;
x_17 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_15, x_16);
x_18 = lean_st_ref_get(x_7, x_8);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_51 = l_Lean_Kernel_isDiagnosticsEnabled(x_21);
lean_dec(x_21);
if (x_51 == 0)
{
if (x_17 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_box(0);
x_53 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__8(x_15, x_17, x_10, x_11, x_4, x_5, x_52, x_6, x_7, x_20);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_box(0);
x_22 = x_54;
goto block_50;
}
}
else
{
if (x_17 == 0)
{
lean_object* x_55; 
x_55 = lean_box(0);
x_22 = x_55;
goto block_50;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
x_57 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__8(x_15, x_17, x_10, x_11, x_4, x_5, x_56, x_6, x_7, x_20);
return x_57;
}
}
block_50:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_22);
x_23 = lean_st_ref_take(x_7, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 5);
lean_dec(x_28);
x_29 = l_Lean_Kernel_enableDiag(x_27, x_17);
x_30 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
lean_ctor_set(x_24, 5, x_30);
lean_ctor_set(x_24, 0, x_29);
x_31 = lean_st_ref_set(x_7, x_24, x_25);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__8(x_15, x_17, x_10, x_11, x_4, x_5, x_33, x_6, x_7, x_32);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_35 = lean_ctor_get(x_24, 0);
x_36 = lean_ctor_get(x_24, 1);
x_37 = lean_ctor_get(x_24, 2);
x_38 = lean_ctor_get(x_24, 3);
x_39 = lean_ctor_get(x_24, 4);
x_40 = lean_ctor_get(x_24, 6);
x_41 = lean_ctor_get(x_24, 7);
x_42 = lean_ctor_get(x_24, 8);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_24);
x_43 = l_Lean_Kernel_enableDiag(x_35, x_17);
x_44 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
x_45 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_36);
lean_ctor_set(x_45, 2, x_37);
lean_ctor_set(x_45, 3, x_38);
lean_ctor_set(x_45, 4, x_39);
lean_ctor_set(x_45, 5, x_44);
lean_ctor_set(x_45, 6, x_40);
lean_ctor_set(x_45, 7, x_41);
lean_ctor_set(x_45, 8, x_42);
x_46 = lean_st_ref_set(x_7, x_45, x_25);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_box(0);
x_49 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__8(x_15, x_17, x_10, x_11, x_4, x_5, x_48, x_6, x_7, x_47);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__8(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_1);
x_13 = l_Lean_Meta_mkEqLikeNameFor(x_11, x_1, x_12);
lean_inc(x_13);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize), 8, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_13);
lean_inc(x_13);
x_15 = l_Lean_Meta_realizeConst(x_1, x_13, x_14, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_13);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_13);
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
x_11 = 0;
lean_inc(x_2);
x_12 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_9, x_10, x_1, x_2, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq(x_2, x_16, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_ctor_set(x_12, 0, x_19);
lean_ctor_set(x_17, 0, x_12);
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
lean_ctor_set(x_12, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_free_object(x_12);
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
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec(x_12);
x_28 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq(x_2, x_27, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_29);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_36 = x_28;
} else {
 lean_dec_ref(x_28);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_unfoldThmSuffix;
lean_inc(x_1);
x_12 = l_Lean_Meta_mkEqLikeNameFor(x_10, x_1, x_11);
x_13 = lean_st_ref_get(x_5, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = 1;
lean_inc(x_12);
lean_inc(x_17);
x_19 = l_Lean_Environment_contains(x_17, x_12, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_13);
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(x_17, x_1, x_20, x_2, x_3, x_4, x_5, x_16);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_13, 0, x_22);
return x_13;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 1;
lean_inc(x_12);
lean_inc(x_25);
x_27 = l_Lean_Environment_contains(x_25, x_12, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_12);
x_28 = lean_box(0);
x_29 = l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f___lambda__1(x_25, x_1, x_28, x_2, x_3, x_4, x_5, x_24);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_12);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
return x_31;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_13 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
x_14 = 0;
lean_inc(x_1);
x_15 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_12, x_13, x_11, x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
lean_ctor_set(x_7, 0, x_16);
return x_7;
}
else
{
uint8_t x_17; 
lean_free_object(x_7);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_15, 0);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = 1;
x_21 = l_Lean_Elab_Eqns_mkEqns(x_1, x_19, x_20, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_15, 0, x_23);
lean_ctor_set(x_21, 0, x_15);
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
lean_ctor_set(x_15, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_15);
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
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = 1;
x_34 = l_Lean_Elab_Eqns_mkEqns(x_1, x_32, x_33, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_48 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_PartialFixpoint_registerEqnsInfo___spec__3___closed__1;
x_49 = 0;
lean_inc(x_1);
x_50 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_47, x_48, x_46, x_1, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_50, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = 1;
x_57 = l_Lean_Elab_Eqns_mkEqns(x_1, x_55, x_56, x_2, x_3, x_4, x_5, x_45);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_54;
}
lean_ctor_set(x_61, 0, x_58);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_54);
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_65 = x_57;
} else {
 lean_dec_ref(x_57);
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_getEqnsFor_x3f), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__1;
x_3 = l_Lean_Meta_registerGetEqnsFn(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__2;
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
lean_object* initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin, lean_io_mk_world());
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
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5 = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__6 = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__6);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__7 = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__7);
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo);
l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1___closed__1 = _init_l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1___closed__1();
lean_mark_persistent(l_Lean_RBMap_toArray___at_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____spec__1___closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__2 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__2);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__3 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__3);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__4 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__4);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__5 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__5);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__6 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____closed__6);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_(lean_io_mk_world());
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
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19();
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__23 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__23();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__23);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__25 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__25();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__25);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__26 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__26();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__26);
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
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__2___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__3);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__4);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__5 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__3___closed__5();
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__4___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__5___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__3);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__4);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__5 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__5);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__6 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__6);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__7 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__7);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__8 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__8();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__8);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__9 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__9();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lambda__6___closed__9);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__1 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__1);
l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__2 = _init_l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679____closed__2);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1679_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
