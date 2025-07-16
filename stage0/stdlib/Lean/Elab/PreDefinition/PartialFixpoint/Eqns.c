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
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_eqnInfoExt;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__2____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__6;
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__6;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__0;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__7;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__5;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2;
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__3____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_projExpr_x21(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__0;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17;
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7;
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__25;
static size_t l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__0;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4;
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__7;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__0;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__23;
static lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4;
static lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__4____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
lean_object* l_Lean_RBMap_toArray___at___Lean_initFn____x40_Lean_ProjFns___hyg_200__spec__0___redArg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3;
extern lean_object* l_Lean_diagnostics;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0;
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__6;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__8;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3;
lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__5;
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProj(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_;
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object*, size_t, size_t);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__7;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2;
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t, size_t, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0;
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2;
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__26;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_panic___at___Lean_Meta_subst_substEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4;
lean_object* l_Lean_Elab_Eqns_mkEqns(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1;
static lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__2;
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__5;
x_2 = lean_box(0);
x_3 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__4;
x_4 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__3;
x_5 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set(x_5, 4, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__6;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBMap_toArray___at___Lean_initFn____x40_Lean_ProjFns___hyg_200__spec__0___redArg(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn___closed__2____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PartialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn___closed__3____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqnInfoExt", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn___closed__4____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_initFn___closed__3____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_2 = l_Lean_Elab_PartialFixpoint_initFn___closed__2____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_3 = l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_4 = l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_initFn___lam__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____boxed), 3, 0);
x_3 = l_Lean_Elab_PartialFixpoint_initFn___closed__4____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_4 = l_Lean_mkMapDeclarationExtension___redArg(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn___lam__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Elab_PartialFixpoint_initFn___lam__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_(x_1, x_2, x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_ctor_get(x_5, 3);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_PartialFixpoint_eqnInfoExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_10 = lean_array_uget(x_5, x_6);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 4);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_10, 5);
lean_inc_ref(x_14);
lean_dec_ref(x_10);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0;
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_14);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 2, x_2);
lean_ctor_set(x_17, 3, x_3);
lean_ctor_set(x_17, 4, x_4);
x_18 = l_Lean_MapDeclarationExtension_insert___redArg(x_15, x_8, x_12, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_8 = x_18;
goto _start;
}
else
{
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*7);
lean_dec_ref(x_5);
x_7 = 1;
x_8 = l_Lean_Elab_DefKind_isTheorem(x_6);
if (x_8 == 0)
{
return x_7;
}
else
{
if (x_4 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
goto _start;
}
else
{
return x_7;
}
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_4, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_23; 
x_12 = lean_array_uget(x_3, x_4);
x_13 = lean_ctor_get(x_12, 4);
lean_inc_ref(x_13);
lean_dec_ref(x_12);
x_14 = 1;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_23 = l_Lean_Meta_isProp(x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec_ref(x_23);
x_15 = x_1;
x_16 = x_26;
goto block_22;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec_ref(x_23);
x_15 = x_2;
x_16 = x_27;
goto block_22;
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec_ref(x_23);
x_30 = lean_unbox(x_28);
lean_dec(x_28);
x_15 = x_30;
x_16 = x_29;
goto block_22;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_23;
}
}
block_22:
{
if (x_15 == 0)
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_10 = x_16;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_20 = lean_box(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
}
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_10);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_uget(x_1, x_2);
x_10 = lean_ctor_get(x_9, 3);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Meta_ensureEqnReservedNamesAvailable(x_10, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_7 = x_13;
goto _start;
}
else
{
return x_11;
}
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(uint8_t x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_3 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(x_2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__6;
x_2 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__5;
x_3 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4;
x_4 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_52; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_86; uint8_t x_99; 
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get_size(x_1);
x_99 = lean_nat_dec_lt(x_56, x_57);
if (x_99 == 0)
{
x_86 = x_9;
goto block_98;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_57, x_57);
if (x_100 == 0)
{
x_86 = x_9;
goto block_98;
}
else
{
lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; 
x_101 = lean_box(0);
x_102 = 0;
x_103 = lean_usize_of_nat(x_57);
x_104 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(x_1, x_102, x_103, x_101, x_7, x_8, x_9);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec_ref(x_104);
x_86 = x_105;
goto block_98;
}
else
{
lean_dec(x_57);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_104;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
block_51:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
x_24 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_15);
lean_ctor_set(x_24, 3, x_16);
lean_ctor_set(x_24, 4, x_17);
lean_ctor_set(x_24, 5, x_23);
lean_ctor_set(x_24, 6, x_18);
lean_ctor_set(x_24, 7, x_19);
lean_ctor_set(x_24, 8, x_20);
x_25 = lean_st_ref_set(x_8, x_24, x_21);
lean_dec(x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_st_ref_take(x_6, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_28, 1);
lean_dec(x_31);
x_32 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__7;
lean_ctor_set(x_28, 1, x_32);
x_33 = lean_st_ref_set(x_6, x_28, x_29);
lean_dec(x_6);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_33, 0, x_36);
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_28, 0);
x_41 = lean_ctor_get(x_28, 2);
x_42 = lean_ctor_get(x_28, 3);
x_43 = lean_ctor_get(x_28, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_28);
x_44 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__7;
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
x_46 = lean_st_ref_set(x_6, x_45, x_29);
lean_dec(x_6);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
block_55:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
block_85:
{
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec_ref(x_58);
x_62 = lean_st_ref_take(x_8, x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec_ref(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc_ref(x_68);
x_69 = lean_ctor_get(x_63, 4);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_63, 6);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_63, 7);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_63, 8);
lean_inc_ref(x_72);
lean_dec(x_63);
x_73 = lean_nat_dec_lt(x_56, x_57);
if (x_73 == 0)
{
lean_dec(x_57);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_64;
x_22 = x_65;
goto block_51;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_57, x_57);
if (x_74 == 0)
{
lean_dec(x_57);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_64;
x_22 = x_65;
goto block_51;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; size_t x_78; lean_object* x_79; 
x_75 = lean_array_size(x_1);
x_76 = 0;
lean_inc_ref(x_1);
x_77 = l_Array_mapMUnsafe_map___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(x_75, x_76, x_1);
x_78 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_79 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(x_77, x_2, x_3, x_4, x_1, x_76, x_78, x_65);
lean_dec_ref(x_1);
x_14 = x_66;
x_15 = x_67;
x_16 = x_68;
x_17 = x_69;
x_18 = x_70;
x_19 = x_71;
x_20 = x_72;
x_21 = x_64;
x_22 = x_79;
goto block_51;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_57);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = lean_ctor_get(x_58, 1);
lean_inc(x_80);
lean_dec_ref(x_58);
x_10 = x_80;
goto block_13;
}
}
else
{
uint8_t x_81; 
lean_dec(x_57);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_81 = !lean_is_exclusive(x_58);
if (x_81 == 0)
{
return x_58;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_58, 0);
x_83 = lean_ctor_get(x_58, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_58);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
block_98:
{
uint8_t x_87; 
x_87 = lean_nat_dec_lt(x_56, x_57);
if (x_87 == 0)
{
lean_dec(x_57);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_52 = x_86;
goto block_55;
}
else
{
if (x_87 == 0)
{
lean_dec(x_57);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_52 = x_86;
goto block_55;
}
else
{
size_t x_88; size_t x_89; uint8_t x_90; 
x_88 = 0;
x_89 = lean_usize_of_nat(x_57);
x_90 = l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(x_1, x_88, x_89);
if (x_90 == 0)
{
lean_dec(x_57);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_52 = x_86;
goto block_55;
}
else
{
uint8_t x_91; 
x_91 = 0;
if (x_87 == 0)
{
lean_object* x_92; 
x_92 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(x_90, x_91, x_91, x_5, x_6, x_7, x_8, x_86);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_58 = x_92;
goto block_85;
}
else
{
if (x_87 == 0)
{
lean_dec(x_57);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = x_86;
goto block_13;
}
else
{
lean_object* x_93; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_93 = l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(x_90, x_91, x_1, x_88, x_89, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_unbox(x_94);
lean_dec(x_94);
x_97 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(x_90, x_91, x_96, x_5, x_6, x_7, x_8, x_95);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_58 = x_97;
goto block_85;
}
else
{
lean_dec_ref(x_7);
lean_dec_ref(x_5);
x_58 = x_93;
goto block_85;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__2(x_1, x_4, x_5);
lean_dec_ref(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_anyMUnsafe_any___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__3(x_11, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__4(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_1);
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___lam__0(x_9, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
return x_4;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("deltaLHSUntilFix", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality expected", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType_x27(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1;
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_2);
x_14 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3;
x_15 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7;
x_16 = l_Lean_Meta_throwTacticEx___redArg(x_14, x_1, x_15, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Expr_appFn_x21(x_9);
x_18 = l_Lean_Expr_appArg_x21(x_17);
lean_dec_ref(x_17);
lean_inc(x_6);
lean_inc_ref(x_5);
x_19 = l_Lean_Meta_deltaExpand(x_18, x_2, x_5, x_6, x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_Expr_appArg_x21(x_9);
lean_dec(x_9);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_23 = l_Lean_Meta_mkEq(x_20, x_22, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l_Lean_MVarId_replaceTargetDefEq(x_1, x_24, x_3, x_4, x_5, x_6, x_25);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
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
lean_dec(x_9);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
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
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1), 7, 2);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_3, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Order", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__1;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__0;
x_3 = l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lfp_monotone", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__3;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__0;
x_3 = l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__9;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static size_t _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
x_2 = lean_ptr_addr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateProj!Impl", 46, 46);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj expected", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__18;
x_2 = lean_unsigned_to_nat(18u);
x_3 = lean_unsigned_to_nat(1809u);
x_4 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__17;
x_5 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__20;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
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
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__22;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__0;
x_3 = l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
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
x_1 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__25;
x_2 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__0;
x_3 = l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_rwFixUnder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__2;
x_8 = lean_unsigned_to_nat(4u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__4;
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
x_14 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__6;
x_15 = l_Lean_MessageData_ofExpr(x_1);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_18, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = l_Lean_Expr_projExpr_x21(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_20);
x_21 = lean_infer_type(x_20, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_24 = l_Lean_Elab_PartialFixpoint_rwFixUnder(x_20, x_2, x_3, x_4, x_5, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__10;
x_28 = 0;
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; uint8_t x_43; 
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_39);
x_40 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__14;
x_41 = lean_ptr_addr(x_39);
lean_dec_ref(x_39);
x_42 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__15;
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec_ref(x_1);
x_44 = l_Lean_Expr_proj___override(x_37, x_38, x_40);
x_29 = x_44;
goto block_36;
}
else
{
lean_dec(x_38);
lean_dec(x_37);
x_29 = x_1;
goto block_36;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_1);
x_45 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__19;
x_46 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_45);
x_29 = x_46;
goto block_36;
}
block_36:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = l_Lean_Expr_lam___override(x_27, x_22, x_29, x_28);
x_31 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__12;
x_32 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
x_33 = lean_array_push(x_32, x_30);
x_34 = lean_array_push(x_33, x_25);
x_35 = l_Lean_Meta_mkAppM(x_31, x_34, x_2, x_3, x_4, x_5, x_26);
return x_35;
}
}
else
{
lean_dec(x_22);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_24;
}
}
else
{
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_21;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_48 = l_Lean_Elab_PartialFixpoint_rwFixUnder(x_47, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec_ref(x_48);
x_51 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__21;
x_52 = l_Lean_Expr_appArg_x21(x_1);
lean_dec_ref(x_1);
x_53 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__13;
x_54 = lean_array_push(x_53, x_49);
x_55 = lean_array_push(x_54, x_52);
x_56 = l_Lean_Meta_mkAppM(x_51, x_55, x_2, x_3, x_4, x_5, x_50);
return x_56;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_48;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_57 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__23;
x_58 = l_Lean_Expr_getAppFn(x_1);
x_59 = l_Lean_Expr_constLevels_x21(x_58);
lean_dec_ref(x_58);
x_60 = l_Lean_Expr_const___override(x_57, x_59);
x_61 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24;
x_62 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_62);
x_63 = lean_mk_array(x_62, x_61);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_sub(x_62, x_64);
lean_dec(x_62);
x_66 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_63, x_65);
x_67 = l_Lean_mkAppN(x_60, x_66);
lean_dec_ref(x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_6);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_69 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__26;
x_70 = l_Lean_Expr_getAppFn(x_1);
x_71 = l_Lean_Expr_constLevels_x21(x_70);
lean_dec_ref(x_70);
x_72 = l_Lean_Expr_const___override(x_69, x_71);
x_73 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__24;
x_74 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_74);
x_75 = lean_mk_array(x_74, x_73);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_sub(x_74, x_76);
lean_dec(x_74);
x_78 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_75, x_77);
x_79 = l_Lean_mkAppN(x_72, x_78);
lean_dec_ref(x_78);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_6);
return x_80;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.PartialFixpoint.Eqns", 44, 44);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.PreDefinition.PartialFixpoint.Eqns.0.Lean.Elab.PartialFixpoint.rwFixEq", 89, 89);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(65u);
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1;
x_5 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2;
x_2 = lean_unsigned_to_nat(51u);
x_3 = lean_unsigned_to_nat(67u);
x_4 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1;
x_5 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType_x27(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3;
x_14 = l_panic___at___Lean_Meta_subst_substEq_spec__0(x_13, x_2, x_3, x_4, x_5, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Expr_appFn_x21(x_8);
x_16 = l_Lean_Expr_appArg_x21(x_15);
lean_dec_ref(x_15);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_17 = l_Lean_Elab_PartialFixpoint_rwFixUnder(x_16, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_18);
x_20 = lean_infer_type(x_18, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Expr_isAppOfArity(x_21, x_10, x_11);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_1);
x_24 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4;
x_25 = l_panic___at___Lean_Meta_subst_substEq_spec__0(x_24, x_2, x_3, x_4, x_5, x_22);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Lean_Expr_appArg_x21(x_8);
lean_dec(x_8);
x_27 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_28 = l_Lean_Meta_mkEq(x_27, x_26, x_2, x_3, x_4, x_5, x_22);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_box(0);
lean_inc_ref(x_2);
x_32 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_29, x_31, x_2, x_3, x_4, x_5, x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
lean_inc(x_3);
lean_inc(x_33);
x_35 = l_Lean_Meta_mkEqTrans(x_18, x_33, x_2, x_3, x_4, x_5, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_36, x_3, x_37);
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_57; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
return x_17;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_17, 0);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_17);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
x_7 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq rfl succeeded", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_smartUnfolding;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq after rwFixEq:", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq after deltaLHS:", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_219; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_219 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec_ref(x_219);
lean_inc(x_4);
x_256 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_4, x_9, x_221);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_unbox(x_257);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_ctor_get(x_256, 1);
lean_inc(x_259);
lean_dec_ref(x_256);
x_222 = x_7;
x_223 = x_8;
x_224 = x_9;
x_225 = x_10;
x_226 = x_259;
goto block_255;
}
else
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_256);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_261 = lean_ctor_get(x_256, 1);
x_262 = lean_ctor_get(x_256, 0);
lean_dec(x_262);
x_263 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__8;
lean_inc(x_220);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_220);
lean_ctor_set_tag(x_256, 7);
lean_ctor_set(x_256, 1, x_264);
lean_ctor_set(x_256, 0, x_263);
x_265 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_256);
lean_ctor_set(x_266, 1, x_265);
lean_inc(x_4);
x_267 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_4, x_266, x_7, x_8, x_9, x_10, x_261);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec_ref(x_267);
x_222 = x_7;
x_223 = x_8;
x_224 = x_9;
x_225 = x_10;
x_226 = x_268;
goto block_255;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_269 = lean_ctor_get(x_256, 1);
lean_inc(x_269);
lean_dec(x_256);
x_270 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__8;
lean_inc(x_220);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_220);
x_272 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
lean_inc(x_4);
x_275 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_4, x_274, x_7, x_8, x_9, x_10, x_269);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec_ref(x_275);
x_222 = x_7;
x_223 = x_8;
x_224 = x_9;
x_225 = x_10;
x_226 = x_276;
goto block_255;
}
}
block_255:
{
lean_object* x_227; 
lean_inc(x_225);
lean_inc_ref(x_224);
lean_inc(x_223);
lean_inc_ref(x_222);
x_227 = l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq(x_220, x_222, x_223, x_224, x_225, x_226);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec_ref(x_227);
lean_inc(x_4);
x_230 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_4, x_224, x_229);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_unbox(x_231);
lean_dec(x_231);
if (x_232 == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_230, 1);
lean_inc(x_233);
lean_dec_ref(x_230);
x_208 = x_228;
x_209 = x_222;
x_210 = x_223;
x_211 = x_224;
x_212 = x_225;
x_213 = x_233;
goto block_218;
}
else
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_230);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_235 = lean_ctor_get(x_230, 1);
x_236 = lean_ctor_get(x_230, 0);
lean_dec(x_236);
x_237 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__6;
lean_inc(x_228);
x_238 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_238, 0, x_228);
lean_ctor_set_tag(x_230, 7);
lean_ctor_set(x_230, 1, x_238);
lean_ctor_set(x_230, 0, x_237);
x_239 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_230);
lean_ctor_set(x_240, 1, x_239);
lean_inc(x_4);
x_241 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_4, x_240, x_222, x_223, x_224, x_225, x_235);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec_ref(x_241);
x_208 = x_228;
x_209 = x_222;
x_210 = x_223;
x_211 = x_224;
x_212 = x_225;
x_213 = x_242;
goto block_218;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_243 = lean_ctor_get(x_230, 1);
lean_inc(x_243);
lean_dec(x_230);
x_244 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__6;
lean_inc(x_228);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_228);
x_246 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
lean_inc(x_4);
x_249 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_4, x_248, x_222, x_223, x_224, x_225, x_243);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec_ref(x_249);
x_208 = x_228;
x_209 = x_222;
x_210 = x_223;
x_211 = x_224;
x_212 = x_225;
x_213 = x_250;
goto block_218;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_225);
lean_dec_ref(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec_ref(x_5);
lean_dec(x_4);
x_251 = !lean_is_exclusive(x_227);
if (x_251 == 0)
{
return x_227;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_227, 0);
x_253 = lean_ctor_get(x_227, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_227);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
x_277 = !lean_is_exclusive(x_219);
if (x_277 == 0)
{
return x_219;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_219, 0);
x_279 = lean_ctor_get(x_219, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_219);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
}
block_53:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0;
x_35 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_18, x_34);
x_36 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_21);
lean_ctor_set(x_36, 2, x_18);
lean_ctor_set(x_36, 3, x_22);
lean_ctor_set(x_36, 4, x_35);
lean_ctor_set(x_36, 5, x_23);
lean_ctor_set(x_36, 6, x_24);
lean_ctor_set(x_36, 7, x_25);
lean_ctor_set(x_36, 8, x_26);
lean_ctor_set(x_36, 9, x_27);
lean_ctor_set(x_36, 10, x_28);
lean_ctor_set(x_36, 11, x_29);
lean_ctor_set(x_36, 12, x_31);
lean_ctor_set_uint8(x_36, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_36, sizeof(void*)*13 + 1, x_30);
lean_inc(x_19);
x_37 = l_Lean_MVarId_refl(x_17, x_13, x_19, x_36, x_32, x_33);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_4);
x_39 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_4, x_15, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec(x_4);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec_ref(x_39);
x_43 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_5, x_19, x_42);
lean_dec(x_19);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec_ref(x_39);
x_45 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2;
x_46 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_4, x_45, x_12, x_19, x_15, x_14, x_44);
lean_dec(x_14);
lean_dec_ref(x_15);
lean_dec_ref(x_12);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_5, x_19, x_47);
lean_dec(x_19);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_19);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_12);
lean_dec_ref(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
return x_37;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_37, 0);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_37);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
block_77:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_62, 3);
lean_inc(x_67);
x_68 = lean_ctor_get(x_62, 5);
lean_inc(x_68);
x_69 = lean_ctor_get(x_62, 6);
lean_inc(x_69);
x_70 = lean_ctor_get(x_62, 7);
lean_inc(x_70);
x_71 = lean_ctor_get(x_62, 8);
lean_inc(x_71);
x_72 = lean_ctor_get(x_62, 9);
lean_inc(x_72);
x_73 = lean_ctor_get(x_62, 10);
lean_inc(x_73);
x_74 = lean_ctor_get(x_62, 11);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_62, sizeof(void*)*13 + 1);
x_76 = lean_ctor_get(x_62, 12);
lean_inc_ref(x_76);
lean_dec_ref(x_62);
x_12 = x_54;
x_13 = x_55;
x_14 = x_56;
x_15 = x_57;
x_16 = x_58;
x_17 = x_59;
x_18 = x_60;
x_19 = x_61;
x_20 = x_65;
x_21 = x_66;
x_22 = x_67;
x_23 = x_68;
x_24 = x_69;
x_25 = x_70;
x_26 = x_71;
x_27 = x_72;
x_28 = x_73;
x_29 = x_74;
x_30 = x_75;
x_31 = x_76;
x_32 = x_63;
x_33 = x_64;
goto block_53;
}
block_111:
{
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_88 = lean_st_ref_take(x_80, x_83);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec_ref(x_88);
x_91 = !lean_is_exclusive(x_89);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_89, 0);
x_93 = lean_ctor_get(x_89, 5);
lean_dec(x_93);
x_94 = l_Lean_Kernel_enableDiag(x_92, x_82);
x_95 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
lean_ctor_set(x_89, 5, x_95);
lean_ctor_set(x_89, 0, x_94);
x_96 = lean_st_ref_set(x_80, x_89, x_90);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec_ref(x_96);
lean_inc_ref(x_81);
lean_inc(x_80);
x_54 = x_78;
x_55 = x_79;
x_56 = x_80;
x_57 = x_81;
x_58 = x_82;
x_59 = x_84;
x_60 = x_85;
x_61 = x_86;
x_62 = x_81;
x_63 = x_80;
x_64 = x_97;
goto block_77;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_98 = lean_ctor_get(x_89, 0);
x_99 = lean_ctor_get(x_89, 1);
x_100 = lean_ctor_get(x_89, 2);
x_101 = lean_ctor_get(x_89, 3);
x_102 = lean_ctor_get(x_89, 4);
x_103 = lean_ctor_get(x_89, 6);
x_104 = lean_ctor_get(x_89, 7);
x_105 = lean_ctor_get(x_89, 8);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_89);
x_106 = l_Lean_Kernel_enableDiag(x_98, x_82);
x_107 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
x_108 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_99);
lean_ctor_set(x_108, 2, x_100);
lean_ctor_set(x_108, 3, x_101);
lean_ctor_set(x_108, 4, x_102);
lean_ctor_set(x_108, 5, x_107);
lean_ctor_set(x_108, 6, x_103);
lean_ctor_set(x_108, 7, x_104);
lean_ctor_set(x_108, 8, x_105);
x_109 = lean_st_ref_set(x_80, x_108, x_90);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec_ref(x_109);
lean_inc_ref(x_81);
lean_inc(x_80);
x_54 = x_78;
x_55 = x_79;
x_56 = x_80;
x_57 = x_81;
x_58 = x_82;
x_59 = x_84;
x_60 = x_85;
x_61 = x_86;
x_62 = x_81;
x_63 = x_80;
x_64 = x_110;
goto block_77;
}
}
else
{
lean_inc_ref(x_81);
lean_inc(x_80);
x_54 = x_78;
x_55 = x_79;
x_56 = x_80;
x_57 = x_81;
x_58 = x_82;
x_59 = x_84;
x_60 = x_85;
x_61 = x_86;
x_62 = x_81;
x_63 = x_80;
x_64 = x_83;
goto block_77;
}
}
block_207:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint64_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_119 = lean_st_ref_get(x_113, x_115);
x_120 = lean_ctor_get(x_112, 0);
lean_inc_ref(x_120);
x_121 = lean_ctor_get(x_119, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec_ref(x_119);
x_123 = lean_ctor_get_uint64(x_112, sizeof(void*)*7);
x_124 = lean_ctor_get_uint8(x_112, sizeof(void*)*7 + 8);
x_125 = lean_ctor_get(x_112, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_112, 2);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_112, 3);
lean_inc_ref(x_127);
x_128 = lean_ctor_get(x_112, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_112, 5);
lean_inc(x_129);
x_130 = lean_ctor_get(x_112, 6);
lean_inc(x_130);
x_131 = !lean_is_exclusive(x_120);
if (x_131 == 0)
{
uint8_t x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; uint64_t x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_159; 
x_132 = lean_ctor_get_uint8(x_112, sizeof(void*)*7 + 9);
x_133 = lean_ctor_get_uint8(x_112, sizeof(void*)*7 + 10);
x_134 = lean_ctor_get(x_114, 0);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_114, 1);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_114, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_114, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_114, 5);
lean_inc(x_138);
x_139 = lean_ctor_get(x_114, 6);
lean_inc(x_139);
x_140 = lean_ctor_get(x_114, 7);
lean_inc(x_140);
x_141 = lean_ctor_get(x_114, 8);
lean_inc(x_141);
x_142 = lean_ctor_get(x_114, 9);
lean_inc(x_142);
x_143 = lean_ctor_get(x_114, 10);
lean_inc(x_143);
x_144 = lean_ctor_get(x_114, 11);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_114, sizeof(void*)*13 + 1);
x_146 = lean_ctor_get(x_114, 12);
lean_inc_ref(x_146);
x_147 = lean_ctor_get(x_121, 0);
lean_inc_ref(x_147);
lean_dec(x_121);
lean_ctor_set_uint8(x_120, 9, x_118);
x_148 = 2;
x_149 = lean_uint64_shift_right(x_123, x_148);
x_150 = lean_uint64_shift_left(x_149, x_148);
x_151 = l_Lean_Meta_TransparencyMode_toUInt64(x_118);
x_152 = lean_uint64_lor(x_150, x_151);
x_153 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_153, 0, x_120);
lean_ctor_set(x_153, 1, x_125);
lean_ctor_set(x_153, 2, x_126);
lean_ctor_set(x_153, 3, x_127);
lean_ctor_set(x_153, 4, x_128);
lean_ctor_set(x_153, 5, x_129);
lean_ctor_set(x_153, 6, x_130);
lean_ctor_set_uint64(x_153, sizeof(void*)*7, x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 8, x_124);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 9, x_132);
lean_ctor_set_uint8(x_153, sizeof(void*)*7 + 10, x_133);
x_154 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3;
x_155 = 0;
x_156 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_136, x_154, x_155);
x_157 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4;
x_158 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_156, x_157);
x_159 = l_Lean_Kernel_isDiagnosticsEnabled(x_147);
lean_dec_ref(x_147);
if (x_159 == 0)
{
if (x_158 == 0)
{
lean_inc(x_113);
x_12 = x_112;
x_13 = x_153;
x_14 = x_113;
x_15 = x_114;
x_16 = x_158;
x_17 = x_116;
x_18 = x_156;
x_19 = x_117;
x_20 = x_134;
x_21 = x_135;
x_22 = x_137;
x_23 = x_138;
x_24 = x_139;
x_25 = x_140;
x_26 = x_141;
x_27 = x_142;
x_28 = x_143;
x_29 = x_144;
x_30 = x_145;
x_31 = x_146;
x_32 = x_113;
x_33 = x_122;
goto block_53;
}
else
{
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec_ref(x_135);
lean_dec_ref(x_134);
x_78 = x_112;
x_79 = x_153;
x_80 = x_113;
x_81 = x_114;
x_82 = x_158;
x_83 = x_122;
x_84 = x_116;
x_85 = x_156;
x_86 = x_117;
x_87 = x_159;
goto block_111;
}
}
else
{
lean_dec_ref(x_146);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec_ref(x_135);
lean_dec_ref(x_134);
x_78 = x_112;
x_79 = x_153;
x_80 = x_113;
x_81 = x_114;
x_82 = x_158;
x_83 = x_122;
x_84 = x_116;
x_85 = x_156;
x_86 = x_117;
x_87 = x_158;
goto block_111;
}
}
else
{
uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint64_t x_195; uint64_t x_196; uint64_t x_197; uint64_t x_198; uint64_t x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; uint8_t x_206; 
x_160 = lean_ctor_get_uint8(x_112, sizeof(void*)*7 + 9);
x_161 = lean_ctor_get_uint8(x_112, sizeof(void*)*7 + 10);
x_162 = lean_ctor_get_uint8(x_120, 0);
x_163 = lean_ctor_get_uint8(x_120, 1);
x_164 = lean_ctor_get_uint8(x_120, 2);
x_165 = lean_ctor_get_uint8(x_120, 3);
x_166 = lean_ctor_get_uint8(x_120, 4);
x_167 = lean_ctor_get_uint8(x_120, 5);
x_168 = lean_ctor_get_uint8(x_120, 6);
x_169 = lean_ctor_get_uint8(x_120, 7);
x_170 = lean_ctor_get_uint8(x_120, 8);
x_171 = lean_ctor_get_uint8(x_120, 10);
x_172 = lean_ctor_get_uint8(x_120, 11);
x_173 = lean_ctor_get_uint8(x_120, 12);
x_174 = lean_ctor_get_uint8(x_120, 13);
x_175 = lean_ctor_get_uint8(x_120, 14);
x_176 = lean_ctor_get_uint8(x_120, 15);
x_177 = lean_ctor_get_uint8(x_120, 16);
x_178 = lean_ctor_get_uint8(x_120, 17);
x_179 = lean_ctor_get_uint8(x_120, 18);
lean_dec(x_120);
x_180 = lean_ctor_get(x_114, 0);
lean_inc_ref(x_180);
x_181 = lean_ctor_get(x_114, 1);
lean_inc_ref(x_181);
x_182 = lean_ctor_get(x_114, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_114, 3);
lean_inc(x_183);
x_184 = lean_ctor_get(x_114, 5);
lean_inc(x_184);
x_185 = lean_ctor_get(x_114, 6);
lean_inc(x_185);
x_186 = lean_ctor_get(x_114, 7);
lean_inc(x_186);
x_187 = lean_ctor_get(x_114, 8);
lean_inc(x_187);
x_188 = lean_ctor_get(x_114, 9);
lean_inc(x_188);
x_189 = lean_ctor_get(x_114, 10);
lean_inc(x_189);
x_190 = lean_ctor_get(x_114, 11);
lean_inc(x_190);
x_191 = lean_ctor_get_uint8(x_114, sizeof(void*)*13 + 1);
x_192 = lean_ctor_get(x_114, 12);
lean_inc_ref(x_192);
x_193 = lean_ctor_get(x_121, 0);
lean_inc_ref(x_193);
lean_dec(x_121);
x_194 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_194, 0, x_162);
lean_ctor_set_uint8(x_194, 1, x_163);
lean_ctor_set_uint8(x_194, 2, x_164);
lean_ctor_set_uint8(x_194, 3, x_165);
lean_ctor_set_uint8(x_194, 4, x_166);
lean_ctor_set_uint8(x_194, 5, x_167);
lean_ctor_set_uint8(x_194, 6, x_168);
lean_ctor_set_uint8(x_194, 7, x_169);
lean_ctor_set_uint8(x_194, 8, x_170);
lean_ctor_set_uint8(x_194, 9, x_118);
lean_ctor_set_uint8(x_194, 10, x_171);
lean_ctor_set_uint8(x_194, 11, x_172);
lean_ctor_set_uint8(x_194, 12, x_173);
lean_ctor_set_uint8(x_194, 13, x_174);
lean_ctor_set_uint8(x_194, 14, x_175);
lean_ctor_set_uint8(x_194, 15, x_176);
lean_ctor_set_uint8(x_194, 16, x_177);
lean_ctor_set_uint8(x_194, 17, x_178);
lean_ctor_set_uint8(x_194, 18, x_179);
x_195 = 2;
x_196 = lean_uint64_shift_right(x_123, x_195);
x_197 = lean_uint64_shift_left(x_196, x_195);
x_198 = l_Lean_Meta_TransparencyMode_toUInt64(x_118);
x_199 = lean_uint64_lor(x_197, x_198);
x_200 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_200, 0, x_194);
lean_ctor_set(x_200, 1, x_125);
lean_ctor_set(x_200, 2, x_126);
lean_ctor_set(x_200, 3, x_127);
lean_ctor_set(x_200, 4, x_128);
lean_ctor_set(x_200, 5, x_129);
lean_ctor_set(x_200, 6, x_130);
lean_ctor_set_uint64(x_200, sizeof(void*)*7, x_199);
lean_ctor_set_uint8(x_200, sizeof(void*)*7 + 8, x_124);
lean_ctor_set_uint8(x_200, sizeof(void*)*7 + 9, x_160);
lean_ctor_set_uint8(x_200, sizeof(void*)*7 + 10, x_161);
x_201 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3;
x_202 = 0;
x_203 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_182, x_201, x_202);
x_204 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4;
x_205 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_203, x_204);
x_206 = l_Lean_Kernel_isDiagnosticsEnabled(x_193);
lean_dec_ref(x_193);
if (x_206 == 0)
{
if (x_205 == 0)
{
lean_inc(x_113);
x_12 = x_112;
x_13 = x_200;
x_14 = x_113;
x_15 = x_114;
x_16 = x_205;
x_17 = x_116;
x_18 = x_203;
x_19 = x_117;
x_20 = x_180;
x_21 = x_181;
x_22 = x_183;
x_23 = x_184;
x_24 = x_185;
x_25 = x_186;
x_26 = x_187;
x_27 = x_188;
x_28 = x_189;
x_29 = x_190;
x_30 = x_191;
x_31 = x_192;
x_32 = x_113;
x_33 = x_122;
goto block_53;
}
else
{
lean_dec_ref(x_192);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec_ref(x_181);
lean_dec_ref(x_180);
x_78 = x_112;
x_79 = x_200;
x_80 = x_113;
x_81 = x_114;
x_82 = x_205;
x_83 = x_122;
x_84 = x_116;
x_85 = x_203;
x_86 = x_117;
x_87 = x_206;
goto block_111;
}
}
else
{
lean_dec_ref(x_192);
lean_dec(x_190);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec_ref(x_181);
lean_dec_ref(x_180);
x_78 = x_112;
x_79 = x_200;
x_80 = x_113;
x_81 = x_114;
x_82 = x_205;
x_83 = x_122;
x_84 = x_116;
x_85 = x_203;
x_86 = x_117;
x_87 = x_205;
goto block_111;
}
}
}
block_218:
{
lean_object* x_214; uint8_t x_215; uint8_t x_216; uint8_t x_217; 
x_214 = lean_ctor_get(x_209, 0);
lean_inc_ref(x_214);
x_215 = lean_ctor_get_uint8(x_214, 9);
lean_dec_ref(x_214);
x_216 = 0;
x_217 = l_Lean_Meta_TransparencyMode_lt(x_215, x_216);
if (x_217 == 0)
{
x_112 = x_209;
x_113 = x_212;
x_114 = x_211;
x_115 = x_213;
x_116 = x_208;
x_117 = x_210;
x_118 = x_215;
goto block_207;
}
else
{
x_112 = x_209;
x_113 = x_212;
x_114 = x_211;
x_115 = x_213;
x_116 = x_208;
x_117 = x_210;
x_118 = x_216;
goto block_207;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to generate unfold theorem for '", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("':\n", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("partialFixpoint", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5;
x_2 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4;
x_3 = l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq start:", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_31; lean_object* x_35; uint8_t x_36; 
lean_inc_ref(x_5);
x_35 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_3, x_5, x_6, x_7, x_8, x_9);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6;
x_40 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_39, x_7, x_38);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
x_44 = l_Lean_Expr_mvarId_x21(x_37);
x_45 = lean_unbox(x_42);
lean_dec(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_free_object(x_40);
lean_free_object(x_35);
x_46 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_47 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(x_1, x_4, x_44, x_39, x_37, x_46, x_5, x_6, x_7, x_8, x_43);
x_31 = x_47;
goto block_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8;
lean_inc(x_44);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_49);
lean_ctor_set(x_40, 0, x_48);
x_50 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_50);
lean_ctor_set(x_35, 0, x_40);
x_51 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_39, x_35, x_5, x_6, x_7, x_8, x_43);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_54 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(x_1, x_4, x_44, x_39, x_37, x_53, x_5, x_6, x_7, x_8, x_52);
x_31 = x_54;
goto block_34;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_40, 0);
x_56 = lean_ctor_get(x_40, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_40);
x_57 = l_Lean_Expr_mvarId_x21(x_37);
x_58 = lean_unbox(x_55);
lean_dec(x_55);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_free_object(x_35);
x_59 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_60 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(x_1, x_4, x_57, x_39, x_37, x_59, x_5, x_6, x_7, x_8, x_56);
x_31 = x_60;
goto block_34;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8;
lean_inc(x_57);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_64);
lean_ctor_set(x_35, 0, x_63);
x_65 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_39, x_35, x_5, x_6, x_7, x_8, x_56);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_68 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(x_1, x_4, x_57, x_39, x_37, x_67, x_5, x_6, x_7, x_8, x_66);
x_31 = x_68;
goto block_34;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_69 = lean_ctor_get(x_35, 0);
x_70 = lean_ctor_get(x_35, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_35);
x_71 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6;
x_72 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_71, x_7, x_70);
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
x_76 = l_Lean_Expr_mvarId_x21(x_69);
x_77 = lean_unbox(x_73);
lean_dec(x_73);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_75);
x_78 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_79 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(x_1, x_4, x_76, x_71, x_69, x_78, x_5, x_6, x_7, x_8, x_74);
x_31 = x_79;
goto block_34;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8;
lean_inc(x_76);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
if (lean_is_scalar(x_75)) {
 x_82 = lean_alloc_ctor(7, 2, 0);
} else {
 x_82 = x_75;
 lean_ctor_set_tag(x_82, 7);
}
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_71, x_84, x_5, x_6, x_7, x_8, x_74);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_box(0);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_88 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(x_1, x_4, x_76, x_71, x_69, x_87, x_5, x_6, x_7, x_8, x_86);
x_31 = x_88;
goto block_34;
}
}
block_24:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_11);
x_14 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1;
x_15 = l_Lean_MessageData_ofName(x_1);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3;
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Exception_toMessageData(x_10);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__8;
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_22, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_23;
}
else
{
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_11;
}
}
block_30:
{
uint8_t x_28; 
x_28 = l_Lean_Exception_isInterrupt(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Exception_isRuntime(x_26);
x_10 = x_26;
x_11 = x_25;
x_12 = x_27;
x_13 = x_29;
goto block_24;
}
else
{
x_10 = x_26;
x_11 = x_25;
x_12 = x_27;
x_13 = x_28;
goto block_24;
}
}
block_34:
{
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
x_25 = x_31;
x_26 = x_32;
x_27 = x_33;
goto block_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_box(0);
lean_inc(x_1);
x_13 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_1, x_12);
lean_inc(x_2);
x_14 = l_Lean_Expr_const___override(x_2, x_13);
x_15 = l_Lean_mkAppN(x_14, x_5);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_16 = l_Lean_Meta_mkEq(x_15, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_box(0);
lean_inc(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1), 9, 4);
lean_closure_set(x_20, 0, x_2);
lean_closure_set(x_20, 1, x_17);
lean_closure_set(x_20, 2, x_19);
lean_closure_set(x_20, 3, x_3);
x_21 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_22 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_20, x_21, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = 1;
x_26 = 1;
lean_inc_ref(x_5);
x_27 = l_Lean_Meta_mkForallFVars(x_5, x_17, x_21, x_25, x_25, x_26, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_30 = l_Lean_Meta_letToHave(x_28, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Meta_mkLambdaFVars(x_5, x_23, x_21, x_25, x_21, x_25, x_26, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_8);
lean_dec_ref(x_7);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
lean_inc(x_4);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_1);
lean_ctor_set(x_36, 2, x_31);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_34);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = l_Lean_addDecl(x_40, x_9, x_10, x_35);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_31);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
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
lean_dec(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
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
lean_dec(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_27);
if (x_50 == 0)
{
return x_27;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_27, 0);
x_52 = lean_ctor_get(x_27, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_27);
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
lean_dec(x_17);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_22);
if (x_54 == 0)
{
return x_22;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_22, 0);
x_56 = lean_ctor_get(x_22, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_22);
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
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_16);
if (x_58 == 0)
{
return x_16;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_16, 0);
x_60 = lean_ctor_get(x_16, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_16);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__0() {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_56; uint8_t x_81; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec_ref(x_9);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec_ref(x_2);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 3);
lean_inc_ref(x_15);
lean_dec_ref(x_10);
x_16 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 7);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 8);
lean_inc(x_23);
x_24 = lean_ctor_get(x_6, 9);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 10);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 11);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_6, sizeof(void*)*13 + 1);
x_28 = lean_ctor_get(x_6, 12);
lean_inc_ref(x_28);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 lean_ctor_release(x_6, 2);
 lean_ctor_release(x_6, 3);
 lean_ctor_release(x_6, 4);
 lean_ctor_release(x_6, 5);
 lean_ctor_release(x_6, 6);
 lean_ctor_release(x_6, 7);
 lean_ctor_release(x_6, 8);
 lean_ctor_release(x_6, 9);
 lean_ctor_release(x_6, 10);
 lean_ctor_release(x_6, 11);
 lean_ctor_release(x_6, 12);
 x_29 = x_6;
} else {
 lean_dec_ref(x_6);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_30);
lean_dec(x_11);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__2), 11, 4);
lean_closure_set(x_31, 0, x_14);
lean_closure_set(x_31, 1, x_1);
lean_closure_set(x_31, 2, x_13);
lean_closure_set(x_31, 3, x_3);
x_32 = 0;
x_33 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__0;
x_34 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_18, x_33, x_32);
x_35 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4;
x_36 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_34, x_35);
x_81 = l_Lean_Kernel_isDiagnosticsEnabled(x_30);
lean_dec_ref(x_30);
if (x_81 == 0)
{
if (x_36 == 0)
{
x_37 = x_16;
x_38 = x_17;
x_39 = x_19;
x_40 = x_20;
x_41 = x_21;
x_42 = x_22;
x_43 = x_23;
x_44 = x_24;
x_45 = x_25;
x_46 = x_26;
x_47 = x_27;
x_48 = x_28;
x_49 = x_7;
x_50 = x_12;
goto block_55;
}
else
{
x_56 = x_81;
goto block_80;
}
}
else
{
x_56 = x_36;
goto block_80;
}
block_55:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0;
x_52 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_34, x_51);
if (lean_is_scalar(x_29)) {
 x_53 = lean_alloc_ctor(0, 13, 2);
} else {
 x_53 = x_29;
}
lean_ctor_set(x_53, 0, x_37);
lean_ctor_set(x_53, 1, x_38);
lean_ctor_set(x_53, 2, x_34);
lean_ctor_set(x_53, 3, x_39);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_40);
lean_ctor_set(x_53, 6, x_41);
lean_ctor_set(x_53, 7, x_42);
lean_ctor_set(x_53, 8, x_43);
lean_ctor_set(x_53, 9, x_44);
lean_ctor_set(x_53, 10, x_45);
lean_ctor_set(x_53, 11, x_46);
lean_ctor_set(x_53, 12, x_48);
lean_ctor_set_uint8(x_53, sizeof(void*)*13, x_36);
lean_ctor_set_uint8(x_53, sizeof(void*)*13 + 1, x_47);
x_54 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_15, x_31, x_32, x_4, x_5, x_53, x_49, x_50);
return x_54;
}
block_80:
{
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_st_ref_take(x_7, x_12);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_ctor_get(x_58, 5);
lean_dec(x_62);
x_63 = l_Lean_Kernel_enableDiag(x_61, x_36);
x_64 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
lean_ctor_set(x_58, 5, x_64);
lean_ctor_set(x_58, 0, x_63);
x_65 = lean_st_ref_set(x_7, x_58, x_59);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec_ref(x_65);
x_37 = x_16;
x_38 = x_17;
x_39 = x_19;
x_40 = x_20;
x_41 = x_21;
x_42 = x_22;
x_43 = x_23;
x_44 = x_24;
x_45 = x_25;
x_46 = x_26;
x_47 = x_27;
x_48 = x_28;
x_49 = x_7;
x_50 = x_66;
goto block_55;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_67 = lean_ctor_get(x_58, 0);
x_68 = lean_ctor_get(x_58, 1);
x_69 = lean_ctor_get(x_58, 2);
x_70 = lean_ctor_get(x_58, 3);
x_71 = lean_ctor_get(x_58, 4);
x_72 = lean_ctor_get(x_58, 6);
x_73 = lean_ctor_get(x_58, 7);
x_74 = lean_ctor_get(x_58, 8);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_58);
x_75 = l_Lean_Kernel_enableDiag(x_67, x_36);
x_76 = l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2;
x_77 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_68);
lean_ctor_set(x_77, 2, x_69);
lean_ctor_set(x_77, 3, x_70);
lean_ctor_set(x_77, 4, x_71);
lean_ctor_set(x_77, 5, x_76);
lean_ctor_set(x_77, 6, x_72);
lean_ctor_set(x_77, 7, x_73);
lean_ctor_set(x_77, 8, x_74);
x_78 = lean_st_ref_set(x_7, x_77, x_59);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec_ref(x_78);
x_37 = x_16;
x_38 = x_17;
x_39 = x_19;
x_40 = x_20;
x_41 = x_21;
x_42 = x_22;
x_43 = x_23;
x_44 = x_24;
x_45 = x_25;
x_46 = x_26;
x_47 = x_27;
x_48 = x_28;
x_49 = x_7;
x_50 = x_79;
goto block_55;
}
}
else
{
x_37 = x_16;
x_38 = x_17;
x_39 = x_19;
x_40 = x_20;
x_41 = x_21;
x_42 = x_22;
x_43 = x_23;
x_44 = x_24;
x_45 = x_25;
x_46 = x_26;
x_47 = x_27;
x_48 = x_28;
x_49 = x_7;
x_50 = x_12;
goto block_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_def", 6, 6);
return x_1;
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
lean_dec_ref(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_15);
lean_dec(x_12);
x_16 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__0;
lean_inc(x_1);
x_17 = l_Lean_Meta_mkEqLikeNameFor(x_14, x_1, x_16);
x_18 = 1;
lean_inc(x_17);
lean_inc_ref(x_15);
x_19 = l_Lean_Environment_contains(x_15, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
lean_dec(x_17);
x_20 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_21 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0;
x_22 = 0;
lean_inc(x_1);
x_23 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_20, x_21, x_15, x_1, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
lean_ctor_set(x_10, 0, x_24);
return x_10;
}
else
{
uint8_t x_25; 
lean_free_object(x_10);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq(x_1, x_26, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_27, 0);
lean_ctor_set(x_23, 0, x_29);
lean_ctor_set(x_27, 0, x_23);
return x_27;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_23, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_free_object(x_23);
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
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_23, 0);
lean_inc(x_37);
lean_dec(x_23);
x_38 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq(x_1, x_37, x_2, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
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
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_39);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_46 = x_38;
} else {
 lean_dec_ref(x_38);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
else
{
lean_object* x_48; 
lean_dec_ref(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_10, 0, x_48);
return x_10;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; 
x_49 = lean_ctor_get(x_10, 0);
x_50 = lean_ctor_get(x_10, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_10);
x_51 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_51);
lean_dec(x_8);
x_52 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_52);
lean_dec(x_49);
x_53 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__0;
lean_inc(x_1);
x_54 = l_Lean_Meta_mkEqLikeNameFor(x_51, x_1, x_53);
x_55 = 1;
lean_inc(x_54);
lean_inc_ref(x_52);
x_56 = l_Lean_Environment_contains(x_52, x_54, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
lean_dec(x_54);
x_57 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_58 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0;
x_59 = 0;
lean_inc(x_1);
x_60 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_57, x_58, x_52, x_1, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_50);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_60, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 x_64 = x_60;
} else {
 lean_dec_ref(x_60);
 x_64 = lean_box(0);
}
x_65 = l_Lean_Elab_PartialFixpoint_mkUnfoldEq(x_1, x_63, x_2, x_3, x_4, x_5, x_50);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
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
if (lean_is_scalar(x_64)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_64;
}
lean_ctor_set(x_69, 0, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_64);
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_52);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_54);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_50);
return x_76;
}
}
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
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0;
x_14 = 0;
lean_inc(x_1);
x_15 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_12, x_13, x_11, x_1, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_inc_ref(x_19);
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
lean_inc_ref(x_32);
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
lean_inc_ref(x_46);
lean_dec(x_44);
x_47 = l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo;
x_48 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0;
x_49 = 0;
lean_inc(x_1);
x_50 = l_Lean_MapDeclarationExtension_find_x3f___redArg(x_47, x_48, x_46, x_1, x_49);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
lean_inc_ref(x_55);
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
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_getEqnsFor_x3f), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_PartialFixpoint_getUnfoldFor_x3f), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_;
x_3 = l_Lean_Meta_registerGetEqnsFn(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_;
x_6 = l_Lean_Meta_registerGetUnfoldEqnFn(x_5, x_4);
return x_6;
}
else
{
return x_3;
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
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__0 = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo___closed__0);
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
l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo = _init_l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_instInhabitedEqnInfo);
l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_ = _init_l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_);
l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_ = _init_l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_);
l_Lean_Elab_PartialFixpoint_initFn___closed__2____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_ = _init_l_Lean_Elab_PartialFixpoint_initFn___closed__2____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn___closed__2____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_);
l_Lean_Elab_PartialFixpoint_initFn___closed__3____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_ = _init_l_Lean_Elab_PartialFixpoint_initFn___closed__3____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn___closed__3____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_);
l_Lean_Elab_PartialFixpoint_initFn___closed__4____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_ = _init_l_Lean_Elab_PartialFixpoint_initFn___closed__4____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn___closed__4____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_73_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_PartialFixpoint_eqnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_eqnInfoExt);
lean_dec_ref(res);
}l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0 = _init_l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at___Lean_Elab_PartialFixpoint_registerEqnsInfo_spec__1___closed__0);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__0);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__1);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__2);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__3);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__4);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__5 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__5);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__6 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__6);
l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__7 = _init_l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_registerEqnsInfo___closed__7);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__0);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__2);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__3);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__4);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__5);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__6);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_deltaLHSUntilFix___lam__1___closed__7);
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__0 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__0();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__0);
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
l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16 = _init_l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_rwFixUnder___closed__16);
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
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__0);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__1);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__2);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__3);
l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4 = _init_l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_PartialFixpoint_Eqns_0__Lean_Elab_PartialFixpoint_rwFixEq___lam__0___closed__4);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__0);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__3);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__4);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__5);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__6 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__6);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__7 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__7);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__8 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__8();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__0___closed__8);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__0);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__1);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__2);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__3);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__4);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__5);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__6);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__7);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___lam__1___closed__8);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__0 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__0();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq_doRealize___closed__0);
l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__0 = _init_l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__0();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_mkUnfoldEq___closed__0);
l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_ = _init_l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn___closed__0____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_);
l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_ = _init_l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_();
lean_mark_persistent(l_Lean_Elab_PartialFixpoint_initFn___closed__1____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_);
if (builtin) {res = l_Lean_Elab_PartialFixpoint_initFn____x40_Lean_Elab_PreDefinition_PartialFixpoint_Eqns___hyg_1694_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
