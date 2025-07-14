// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Unfold
// Imports: Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Eqns Lean.Meta.Tactic.Apply
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
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
static lean_object* l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
lean_object* l_List_lengthTR___redArg(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__35;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__19;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__17;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11;
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7;
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0;
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__32;
static lean_object* l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__15;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__18;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
extern lean_object* l_Lean_Meta_tactic_hygienic;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6;
lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__26;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___closed__1;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__30;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__20;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__14;
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__28;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3;
extern lean_object* l_Lean_instInhabitedExpr;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__36;
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4;
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3;
static lean_object* l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9;
extern lean_object* l_Lean_diagnostics;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__34;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19;
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_forM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__7;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__1;
static lean_object* l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__41;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__39;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__37;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___closed__0;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__22;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__3;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5;
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___closed__2;
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__16;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13;
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(uint8_t, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2;
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4;
lean_object* l_panic___at___Lean_Meta_subst_substEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTargetStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__38;
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__40;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__42;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3;
static lean_object* l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__24;
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_2, x_4, x_12);
x_14 = l_Lean_Expr_app___override(x_11, x_13);
x_15 = 0;
x_16 = 1;
x_17 = l_Lean_Meta_mkLambdaFVars(x_4, x_14, x_15, x_3, x_15, x_3, x_16, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rwFixEq", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected saturated fixed-point application in {lhs'}", 52, 52);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.WF.Unfold", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lean.Elab.PreDefinition.WF.Unfold.0.Lean.Elab.WF.rwFixEq", 65, 65);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10;
x_2 = lean_unsigned_to_nat(41u);
x_3 = lean_unsigned_to_nat(17u);
x_4 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9;
x_5 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rwFixEq: cannot delta-reduce ", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WellFounded", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("fix_eq", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_17 = l_Lean_MVarId_getType_x27(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7;
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Expr_isAppOfArity(x_18, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_23 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11;
x_24 = l_panic___at___Lean_Meta_subst_substEq_spec__0(x_23, x_3, x_4, x_5, x_6, x_19);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_box(x_22);
x_26 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = l_Lean_Expr_appFn_x21(x_18);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
lean_inc(x_28);
x_29 = l_Lean_Meta_delta_x3f(x_28, x_26, x_5, x_6, x_19);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13;
x_33 = l_Lean_MessageData_ofExpr(x_28);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_36, x_3, x_4, x_5, x_6, x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_30, 0);
lean_inc(x_39);
lean_dec(x_30);
lean_inc(x_39);
x_40 = l_Lean_Expr_cleanupAnnotations(x_39);
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = l_Lean_Expr_appFnCleanup___redArg(x_40);
x_44 = l_Lean_Expr_isApp(x_43);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
x_46 = l_Lean_Expr_appFnCleanup___redArg(x_43);
x_47 = l_Lean_Expr_isApp(x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = l_Lean_Expr_appFnCleanup___redArg(x_46);
x_49 = l_Lean_Expr_isApp(x_48);
if (x_49 == 0)
{
lean_dec(x_48);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = l_Lean_Expr_appFnCleanup___redArg(x_48);
x_51 = l_Lean_Expr_isApp(x_50);
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = l_Lean_Expr_appFnCleanup___redArg(x_50);
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_dec(x_52);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = l_Lean_Expr_appFnCleanup___redArg(x_52);
x_55 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18;
x_56 = l_Lean_Expr_isConstOf(x_54, x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_38;
goto block_16;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_inc(x_42);
lean_inc(x_45);
x_57 = l_Lean_Expr_app___override(x_45, x_42);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_58 = lean_infer_type(x_57, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_box(x_56);
x_62 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 10, 3);
lean_closure_set(x_62, 0, x_28);
lean_closure_set(x_62, 1, x_2);
lean_closure_set(x_62, 2, x_61);
x_63 = l_Lean_Expr_bindingDomain_x21(x_59);
lean_dec(x_59);
x_64 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19;
x_65 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_66 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_63, x_64, x_62, x_65, x_65, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_70 = l_Lean_mkAppB(x_45, x_42, x_67);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_71 = l_Lean_Meta_mkEq(x_70, x_69, x_3, x_4, x_5, x_6, x_68);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_box(0);
lean_inc(x_3);
x_75 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_72, x_74, x_3, x_4, x_5, x_6, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21;
x_79 = l_Lean_Expr_getAppFn(x_39);
x_80 = l_Lean_Expr_constLevels_x21(x_79);
lean_dec(x_79);
x_81 = l_Lean_Expr_const___override(x_78, x_80);
x_82 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__22;
x_83 = l_Lean_Expr_getAppNumArgs(x_39);
lean_inc(x_83);
x_84 = lean_mk_array(x_83, x_82);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_sub(x_83, x_85);
lean_dec(x_83);
x_87 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_39, x_84, x_86);
x_88 = l_Lean_mkAppN(x_81, x_87);
lean_dec(x_87);
lean_inc(x_4);
lean_inc(x_76);
x_89 = l_Lean_Meta_mkEqTrans(x_88, x_76, x_3, x_4, x_5, x_6, x_77);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_90, x_4, x_91);
lean_dec(x_4);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
lean_dec(x_94);
x_95 = l_Lean_Expr_mvarId_x21(x_76);
lean_dec(x_76);
lean_ctor_set(x_92, 0, x_95);
return x_92;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = l_Lean_Expr_mvarId_x21(x_76);
lean_dec(x_76);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_76);
lean_dec(x_4);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_89);
if (x_99 == 0)
{
return x_89;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_89, 0);
x_101 = lean_ctor_get(x_89, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_89);
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
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_66);
if (x_107 == 0)
{
return x_66;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_66, 0);
x_109 = lean_ctor_get(x_66, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_66);
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
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_58);
if (x_111 == 0)
{
return x_58;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_58, 0);
x_113 = lean_ctor_get(x_58, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_58);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
}
}
}
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_29);
if (x_115 == 0)
{
return x_29;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_29, 0);
x_117 = lean_ctor_get(x_29, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_29);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_17);
if (x_119 == 0)
{
return x_17;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_17, 0);
x_121 = lean_ctor_get(x_17, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_17);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1;
x_14 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5;
x_15 = l_Lean_Meta_throwTacticEx___redArg(x_13, x_1, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_instInhabitedExpr;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = 1;
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_5 = x_14;
x_10 = x_15;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("definition", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("wf", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqns", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2;
x_3 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1;
x_4 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__14;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__19() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__17;
x_4 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__18;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__19;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__16;
x_3 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__14;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__20;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to generate equational theorem for '", 43, 43);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__22;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__24;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("splitTarget into ", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__26;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" goals", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__28;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("case split into ", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__30;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp only!", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__32;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpIf!", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__34;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpMatch!", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__36;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("contradiction!", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__38;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("refl!", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__40;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("step\n", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__42;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint64_t x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_522; lean_object* x_523; uint8_t x_524; 
x_42 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4;
x_522 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_5, x_7);
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_unbox(x_523);
lean_dec(x_523);
if (x_524 == 0)
{
lean_object* x_525; 
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
lean_dec(x_522);
x_484 = x_3;
x_485 = x_4;
x_486 = x_5;
x_487 = x_6;
x_488 = x_525;
goto block_521;
}
else
{
uint8_t x_526; 
x_526 = !lean_is_exclusive(x_522);
if (x_526 == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_527 = lean_ctor_get(x_522, 1);
x_528 = lean_ctor_get(x_522, 0);
lean_dec(x_528);
x_529 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43;
lean_inc(x_2);
x_530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_530, 0, x_2);
lean_ctor_set_tag(x_522, 7);
lean_ctor_set(x_522, 1, x_530);
lean_ctor_set(x_522, 0, x_529);
x_531 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_532 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_532, 0, x_522);
lean_ctor_set(x_532, 1, x_531);
x_533 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_532, x_3, x_4, x_5, x_6, x_527);
x_534 = lean_ctor_get(x_533, 1);
lean_inc(x_534);
lean_dec(x_533);
x_484 = x_3;
x_485 = x_4;
x_486 = x_5;
x_487 = x_6;
x_488 = x_534;
goto block_521;
}
else
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_535 = lean_ctor_get(x_522, 1);
lean_inc(x_535);
lean_dec(x_522);
x_536 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43;
lean_inc(x_2);
x_537 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_537, 0, x_2);
x_538 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
x_539 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_540 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
x_541 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_540, x_3, x_4, x_5, x_6, x_535);
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
lean_dec(x_541);
x_484 = x_3;
x_485 = x_4;
x_486 = x_5;
x_487 = x_6;
x_488 = x_542;
goto block_521;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof), 7, 1);
lean_closure_set(x_22, 0, x_1);
x_23 = l_List_forM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__0(x_22, x_16, x_17, x_18, x_19, x_20, x_21);
return x_23;
}
block_41:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_array_get_size(x_26);
x_33 = lean_box(0);
x_34 = lean_nat_dec_lt(x_25, x_32);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_32, x_32);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_32);
lean_dec(x_32);
x_40 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(x_1, x_26, x_38, x_39, x_33, x_27, x_28, x_29, x_30, x_31);
lean_dec(x_26);
return x_40;
}
}
}
block_483:
{
lean_object* x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_77, 0, x_45);
lean_ctor_set_uint8(x_77, 1, x_46);
lean_ctor_set_uint8(x_77, 2, x_47);
lean_ctor_set_uint8(x_77, 3, x_48);
lean_ctor_set_uint8(x_77, 4, x_49);
lean_ctor_set_uint8(x_77, 5, x_50);
lean_ctor_set_uint8(x_77, 6, x_51);
lean_ctor_set_uint8(x_77, 7, x_52);
lean_ctor_set_uint8(x_77, 8, x_53);
lean_ctor_set_uint8(x_77, 9, x_76);
lean_ctor_set_uint8(x_77, 10, x_54);
lean_ctor_set_uint8(x_77, 11, x_55);
lean_ctor_set_uint8(x_77, 12, x_56);
lean_ctor_set_uint8(x_77, 13, x_57);
lean_ctor_set_uint8(x_77, 14, x_58);
lean_ctor_set_uint8(x_77, 15, x_59);
lean_ctor_set_uint8(x_77, 16, x_60);
lean_ctor_set_uint8(x_77, 17, x_61);
lean_ctor_set_uint8(x_77, 18, x_62);
x_78 = 2;
x_79 = lean_uint64_shift_right(x_63, x_78);
x_80 = lean_uint64_shift_left(x_79, x_78);
x_81 = l_Lean_Meta_TransparencyMode_toUInt64(x_76);
x_82 = lean_uint64_lor(x_80, x_81);
x_83 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_65);
lean_ctor_set(x_83, 2, x_66);
lean_ctor_set(x_83, 3, x_67);
lean_ctor_set(x_83, 4, x_68);
lean_ctor_set(x_83, 5, x_69);
lean_ctor_set(x_83, 6, x_70);
lean_ctor_set_uint64(x_83, sizeof(void*)*7, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*7 + 8, x_64);
lean_ctor_set_uint8(x_83, sizeof(void*)*7 + 9, x_71);
lean_ctor_set_uint8(x_83, sizeof(void*)*7 + 10, x_72);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_2);
x_84 = l_Lean_Elab_Eqns_tryURefl(x_2, x_83, x_43, x_75, x_74, x_73);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_88 = l_Lean_Elab_Eqns_tryContradiction(x_2, x_44, x_43, x_75, x_74, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_92 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_44, x_43, x_75, x_74, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_95 = l_Lean_Elab_Eqns_simpIf_x3f(x_2, x_44, x_43, x_75, x_74, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = 1;
x_99 = lean_unsigned_to_nat(100000u);
x_100 = lean_unsigned_to_nat(2u);
x_101 = 2;
x_102 = lean_alloc_ctor(0, 2, 23);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_103);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 1, x_98);
x_104 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 2, x_104);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 3, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 4, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 5, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 6, x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 7, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 8, x_98);
x_105 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 9, x_105);
x_106 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 10, x_106);
x_107 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 11, x_107);
x_108 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 12, x_108);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 13, x_98);
x_109 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 14, x_109);
x_110 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 15, x_110);
x_111 = lean_unbox(x_89);
lean_dec(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 16, x_111);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 17, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 18, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 19, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 20, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 21, x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 22, x_98);
x_112 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5;
x_113 = lean_unsigned_to_nat(0u);
x_114 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13;
x_115 = l_Lean_Meta_Simp_mkContext___redArg(x_102, x_112, x_114, x_44, x_74, x_97);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_box(0);
x_120 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21;
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_121 = l_Lean_Meta_simpTargetStar(x_2, x_117, x_112, x_119, x_120, x_44, x_43, x_75, x_74, x_118);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
x_125 = lean_ctor_get(x_122, 1);
lean_dec(x_125);
switch (lean_obj_tag(x_124)) {
case 0:
{
uint8_t x_126; 
lean_free_object(x_122);
lean_free_object(x_115);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_121);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_121, 0);
lean_dec(x_127);
x_128 = lean_box(0);
lean_ctor_set(x_121, 0, x_128);
return x_121;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_121, 1);
lean_inc(x_129);
lean_dec(x_121);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
case 1:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_121, 1);
lean_inc(x_132);
lean_dec(x_121);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_133 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_44, x_43, x_75, x_74, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_136 = l_Lean_Meta_splitTarget_x3f(x_2, x_98, x_44, x_43, x_75, x_74, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
x_140 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_122, 7);
lean_ctor_set(x_122, 1, x_140);
lean_ctor_set(x_122, 0, x_139);
x_141 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
lean_ctor_set_tag(x_115, 7);
lean_ctor_set(x_115, 1, x_141);
lean_ctor_set(x_115, 0, x_122);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_2);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_115);
lean_ctor_set(x_143, 1, x_142);
x_144 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_145, x_44, x_43, x_75, x_74, x_138);
lean_dec(x_74);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_44);
return x_146;
}
else
{
lean_object* x_147; uint8_t x_148; 
lean_free_object(x_115);
lean_dec(x_2);
x_147 = lean_ctor_get(x_136, 1);
lean_inc(x_147);
lean_dec(x_136);
x_148 = !lean_is_exclusive(x_137);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_137, 0);
x_150 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_147);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; 
lean_free_object(x_137);
lean_free_object(x_122);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_16 = x_149;
x_17 = x_44;
x_18 = x_43;
x_19 = x_75;
x_20 = x_74;
x_21 = x_153;
goto block_24;
}
else
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_150);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_155 = lean_ctor_get(x_150, 1);
x_156 = lean_ctor_get(x_150, 0);
lean_dec(x_156);
x_157 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_158 = l_List_lengthTR___redArg(x_149);
x_159 = l_Nat_reprFast(x_158);
lean_ctor_set_tag(x_137, 3);
lean_ctor_set(x_137, 0, x_159);
x_160 = l_Lean_MessageData_ofFormat(x_137);
lean_ctor_set_tag(x_150, 7);
lean_ctor_set(x_150, 1, x_160);
lean_ctor_set(x_150, 0, x_157);
x_161 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_122, 7);
lean_ctor_set(x_122, 1, x_161);
lean_ctor_set(x_122, 0, x_150);
x_162 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_122, x_44, x_43, x_75, x_74, x_155);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_16 = x_149;
x_17 = x_44;
x_18 = x_43;
x_19 = x_75;
x_20 = x_74;
x_21 = x_163;
goto block_24;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_164 = lean_ctor_get(x_150, 1);
lean_inc(x_164);
lean_dec(x_150);
x_165 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_166 = l_List_lengthTR___redArg(x_149);
x_167 = l_Nat_reprFast(x_166);
lean_ctor_set_tag(x_137, 3);
lean_ctor_set(x_137, 0, x_167);
x_168 = l_Lean_MessageData_ofFormat(x_137);
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
x_170 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_122, 7);
lean_ctor_set(x_122, 1, x_170);
lean_ctor_set(x_122, 0, x_169);
x_171 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_122, x_44, x_43, x_75, x_74, x_164);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_16 = x_149;
x_17 = x_44;
x_18 = x_43;
x_19 = x_75;
x_20 = x_74;
x_21 = x_172;
goto block_24;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_173 = lean_ctor_get(x_137, 0);
lean_inc(x_173);
lean_dec(x_137);
x_174 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_147);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; 
lean_free_object(x_122);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_16 = x_173;
x_17 = x_44;
x_18 = x_43;
x_19 = x_75;
x_20 = x_74;
x_21 = x_177;
goto block_24;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_178 = lean_ctor_get(x_174, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_179 = x_174;
} else {
 lean_dec_ref(x_174);
 x_179 = lean_box(0);
}
x_180 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_181 = l_List_lengthTR___redArg(x_173);
x_182 = l_Nat_reprFast(x_181);
x_183 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_183, 0, x_182);
x_184 = l_Lean_MessageData_ofFormat(x_183);
if (lean_is_scalar(x_179)) {
 x_185 = lean_alloc_ctor(7, 2, 0);
} else {
 x_185 = x_179;
 lean_ctor_set_tag(x_185, 7);
}
lean_ctor_set(x_185, 0, x_180);
lean_ctor_set(x_185, 1, x_184);
x_186 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_122, 7);
lean_ctor_set(x_122, 1, x_186);
lean_ctor_set(x_122, 0, x_185);
x_187 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_122, x_44, x_43, x_75, x_74, x_178);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_16 = x_173;
x_17 = x_44;
x_18 = x_43;
x_19 = x_75;
x_20 = x_74;
x_21 = x_188;
goto block_24;
}
}
}
}
else
{
uint8_t x_189; 
lean_free_object(x_122);
lean_free_object(x_115);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_136);
if (x_189 == 0)
{
return x_136;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_136, 0);
x_191 = lean_ctor_get(x_136, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_136);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
lean_object* x_193; uint8_t x_194; 
lean_free_object(x_115);
lean_dec(x_2);
x_193 = lean_ctor_get(x_133, 1);
lean_inc(x_193);
lean_dec(x_133);
x_194 = !lean_is_exclusive(x_134);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_195 = lean_ctor_get(x_134, 0);
x_196 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_193);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_unbox(x_197);
lean_dec(x_197);
if (x_198 == 0)
{
lean_object* x_199; 
lean_free_object(x_134);
lean_free_object(x_122);
x_199 = lean_ctor_get(x_196, 1);
lean_inc(x_199);
lean_dec(x_196);
x_25 = x_113;
x_26 = x_195;
x_27 = x_44;
x_28 = x_43;
x_29 = x_75;
x_30 = x_74;
x_31 = x_199;
goto block_41;
}
else
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_196);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_201 = lean_ctor_get(x_196, 1);
x_202 = lean_ctor_get(x_196, 0);
lean_dec(x_202);
x_203 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_204 = lean_array_get_size(x_195);
x_205 = l_Nat_reprFast(x_204);
lean_ctor_set_tag(x_134, 3);
lean_ctor_set(x_134, 0, x_205);
x_206 = l_Lean_MessageData_ofFormat(x_134);
lean_ctor_set_tag(x_196, 7);
lean_ctor_set(x_196, 1, x_206);
lean_ctor_set(x_196, 0, x_203);
x_207 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_122, 7);
lean_ctor_set(x_122, 1, x_207);
lean_ctor_set(x_122, 0, x_196);
x_208 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_122, x_44, x_43, x_75, x_74, x_201);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_25 = x_113;
x_26 = x_195;
x_27 = x_44;
x_28 = x_43;
x_29 = x_75;
x_30 = x_74;
x_31 = x_209;
goto block_41;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_210 = lean_ctor_get(x_196, 1);
lean_inc(x_210);
lean_dec(x_196);
x_211 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_212 = lean_array_get_size(x_195);
x_213 = l_Nat_reprFast(x_212);
lean_ctor_set_tag(x_134, 3);
lean_ctor_set(x_134, 0, x_213);
x_214 = l_Lean_MessageData_ofFormat(x_134);
x_215 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_215, 0, x_211);
lean_ctor_set(x_215, 1, x_214);
x_216 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_122, 7);
lean_ctor_set(x_122, 1, x_216);
lean_ctor_set(x_122, 0, x_215);
x_217 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_122, x_44, x_43, x_75, x_74, x_210);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_25 = x_113;
x_26 = x_195;
x_27 = x_44;
x_28 = x_43;
x_29 = x_75;
x_30 = x_74;
x_31 = x_218;
goto block_41;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_134, 0);
lean_inc(x_219);
lean_dec(x_134);
x_220 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_193);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
lean_free_object(x_122);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_25 = x_113;
x_26 = x_219;
x_27 = x_44;
x_28 = x_43;
x_29 = x_75;
x_30 = x_74;
x_31 = x_223;
goto block_41;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_224 = lean_ctor_get(x_220, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_225 = x_220;
} else {
 lean_dec_ref(x_220);
 x_225 = lean_box(0);
}
x_226 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_227 = lean_array_get_size(x_219);
x_228 = l_Nat_reprFast(x_227);
x_229 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_230 = l_Lean_MessageData_ofFormat(x_229);
if (lean_is_scalar(x_225)) {
 x_231 = lean_alloc_ctor(7, 2, 0);
} else {
 x_231 = x_225;
 lean_ctor_set_tag(x_231, 7);
}
lean_ctor_set(x_231, 0, x_226);
lean_ctor_set(x_231, 1, x_230);
x_232 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_122, 7);
lean_ctor_set(x_122, 1, x_232);
lean_ctor_set(x_122, 0, x_231);
x_233 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_122, x_44, x_43, x_75, x_74, x_224);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_25 = x_113;
x_26 = x_219;
x_27 = x_44;
x_28 = x_43;
x_29 = x_75;
x_30 = x_74;
x_31 = x_234;
goto block_41;
}
}
}
}
else
{
uint8_t x_235; 
lean_free_object(x_122);
lean_free_object(x_115);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_133);
if (x_235 == 0)
{
return x_133;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_133, 0);
x_237 = lean_ctor_get(x_133, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_133);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
default: 
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
lean_free_object(x_122);
lean_free_object(x_115);
lean_dec(x_2);
x_239 = lean_ctor_get(x_121, 1);
lean_inc(x_239);
lean_dec(x_121);
x_240 = lean_ctor_get(x_124, 0);
lean_inc(x_240);
lean_dec(x_124);
x_241 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_239);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_unbox(x_242);
lean_dec(x_242);
if (x_243 == 0)
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_244);
lean_dec(x_241);
x_2 = x_240;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_244;
goto _start;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_241, 1);
lean_inc(x_246);
lean_dec(x_241);
x_247 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
x_248 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_247, x_44, x_43, x_75, x_74, x_246);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_2 = x_240;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_249;
goto _start;
}
}
}
}
else
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_122, 0);
lean_inc(x_251);
lean_dec(x_122);
switch (lean_obj_tag(x_251)) {
case 0:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_free_object(x_115);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_252 = lean_ctor_get(x_121, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_253 = x_121;
} else {
 lean_dec_ref(x_121);
 x_253 = lean_box(0);
}
x_254 = lean_box(0);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
case 1:
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_121, 1);
lean_inc(x_256);
lean_dec(x_121);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_257 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_44, x_43, x_75, x_74, x_256);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_259);
lean_dec(x_257);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_260 = l_Lean_Meta_splitTarget_x3f(x_2, x_98, x_44, x_43, x_75, x_74, x_259);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
x_264 = l_Lean_MessageData_ofName(x_1);
x_265 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
x_266 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
lean_ctor_set_tag(x_115, 7);
lean_ctor_set(x_115, 1, x_266);
lean_ctor_set(x_115, 0, x_265);
x_267 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_267, 0, x_2);
x_268 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_268, 0, x_115);
lean_ctor_set(x_268, 1, x_267);
x_269 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_270 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
x_271 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_270, x_44, x_43, x_75, x_74, x_262);
lean_dec(x_74);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_44);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_free_object(x_115);
lean_dec(x_2);
x_272 = lean_ctor_get(x_260, 1);
lean_inc(x_272);
lean_dec(x_260);
x_273 = lean_ctor_get(x_261, 0);
lean_inc(x_273);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 x_274 = x_261;
} else {
 lean_dec_ref(x_261);
 x_274 = lean_box(0);
}
x_275 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_272);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_unbox(x_276);
lean_dec(x_276);
if (x_277 == 0)
{
lean_object* x_278; 
lean_dec(x_274);
x_278 = lean_ctor_get(x_275, 1);
lean_inc(x_278);
lean_dec(x_275);
x_16 = x_273;
x_17 = x_44;
x_18 = x_43;
x_19 = x_75;
x_20 = x_74;
x_21 = x_278;
goto block_24;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_279 = lean_ctor_get(x_275, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_280 = x_275;
} else {
 lean_dec_ref(x_275);
 x_280 = lean_box(0);
}
x_281 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_282 = l_List_lengthTR___redArg(x_273);
x_283 = l_Nat_reprFast(x_282);
if (lean_is_scalar(x_274)) {
 x_284 = lean_alloc_ctor(3, 1, 0);
} else {
 x_284 = x_274;
 lean_ctor_set_tag(x_284, 3);
}
lean_ctor_set(x_284, 0, x_283);
x_285 = l_Lean_MessageData_ofFormat(x_284);
if (lean_is_scalar(x_280)) {
 x_286 = lean_alloc_ctor(7, 2, 0);
} else {
 x_286 = x_280;
 lean_ctor_set_tag(x_286, 7);
}
lean_ctor_set(x_286, 0, x_281);
lean_ctor_set(x_286, 1, x_285);
x_287 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
x_288 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_289 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_288, x_44, x_43, x_75, x_74, x_279);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
x_16 = x_273;
x_17 = x_44;
x_18 = x_43;
x_19 = x_75;
x_20 = x_74;
x_21 = x_290;
goto block_24;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_free_object(x_115);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_291 = lean_ctor_get(x_260, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_260, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_260)) {
 lean_ctor_release(x_260, 0);
 lean_ctor_release(x_260, 1);
 x_293 = x_260;
} else {
 lean_dec_ref(x_260);
 x_293 = lean_box(0);
}
if (lean_is_scalar(x_293)) {
 x_294 = lean_alloc_ctor(1, 2, 0);
} else {
 x_294 = x_293;
}
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_292);
return x_294;
}
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
lean_free_object(x_115);
lean_dec(x_2);
x_295 = lean_ctor_get(x_257, 1);
lean_inc(x_295);
lean_dec(x_257);
x_296 = lean_ctor_get(x_258, 0);
lean_inc(x_296);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 x_297 = x_258;
} else {
 lean_dec_ref(x_258);
 x_297 = lean_box(0);
}
x_298 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_295);
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_unbox(x_299);
lean_dec(x_299);
if (x_300 == 0)
{
lean_object* x_301; 
lean_dec(x_297);
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_25 = x_113;
x_26 = x_296;
x_27 = x_44;
x_28 = x_43;
x_29 = x_75;
x_30 = x_74;
x_31 = x_301;
goto block_41;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_302 = lean_ctor_get(x_298, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_303 = x_298;
} else {
 lean_dec_ref(x_298);
 x_303 = lean_box(0);
}
x_304 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_305 = lean_array_get_size(x_296);
x_306 = l_Nat_reprFast(x_305);
if (lean_is_scalar(x_297)) {
 x_307 = lean_alloc_ctor(3, 1, 0);
} else {
 x_307 = x_297;
 lean_ctor_set_tag(x_307, 3);
}
lean_ctor_set(x_307, 0, x_306);
x_308 = l_Lean_MessageData_ofFormat(x_307);
if (lean_is_scalar(x_303)) {
 x_309 = lean_alloc_ctor(7, 2, 0);
} else {
 x_309 = x_303;
 lean_ctor_set_tag(x_309, 7);
}
lean_ctor_set(x_309, 0, x_304);
lean_ctor_set(x_309, 1, x_308);
x_310 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
x_311 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_311, x_44, x_43, x_75, x_74, x_302);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_25 = x_113;
x_26 = x_296;
x_27 = x_44;
x_28 = x_43;
x_29 = x_75;
x_30 = x_74;
x_31 = x_313;
goto block_41;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_free_object(x_115);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_314 = lean_ctor_get(x_257, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_257, 1);
lean_inc(x_315);
if (lean_is_exclusive(x_257)) {
 lean_ctor_release(x_257, 0);
 lean_ctor_release(x_257, 1);
 x_316 = x_257;
} else {
 lean_dec_ref(x_257);
 x_316 = lean_box(0);
}
if (lean_is_scalar(x_316)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_316;
}
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_315);
return x_317;
}
}
default: 
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_free_object(x_115);
lean_dec(x_2);
x_318 = lean_ctor_get(x_121, 1);
lean_inc(x_318);
lean_dec(x_121);
x_319 = lean_ctor_get(x_251, 0);
lean_inc(x_319);
lean_dec(x_251);
x_320 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_318);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_unbox(x_321);
lean_dec(x_321);
if (x_322 == 0)
{
lean_object* x_323; 
x_323 = lean_ctor_get(x_320, 1);
lean_inc(x_323);
lean_dec(x_320);
x_2 = x_319;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_323;
goto _start;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_320, 1);
lean_inc(x_325);
lean_dec(x_320);
x_326 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
x_327 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_326, x_44, x_43, x_75, x_74, x_325);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
x_2 = x_319;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_328;
goto _start;
}
}
}
}
}
else
{
uint8_t x_330; 
lean_free_object(x_115);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_330 = !lean_is_exclusive(x_121);
if (x_330 == 0)
{
return x_121;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_121, 0);
x_332 = lean_ctor_get(x_121, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_121);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_334 = lean_ctor_get(x_115, 0);
x_335 = lean_ctor_get(x_115, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_115);
x_336 = lean_box(0);
x_337 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21;
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_338 = l_Lean_Meta_simpTargetStar(x_2, x_334, x_112, x_336, x_337, x_44, x_43, x_75, x_74, x_335);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_339, 0);
lean_inc(x_340);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 x_341 = x_339;
} else {
 lean_dec_ref(x_339);
 x_341 = lean_box(0);
}
switch (lean_obj_tag(x_340)) {
case 0:
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_341);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_342 = lean_ctor_get(x_338, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_343 = x_338;
} else {
 lean_dec_ref(x_338);
 x_343 = lean_box(0);
}
x_344 = lean_box(0);
if (lean_is_scalar(x_343)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_343;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_342);
return x_345;
}
case 1:
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_338, 1);
lean_inc(x_346);
lean_dec(x_338);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_347 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_44, x_43, x_75, x_74, x_346);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; 
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
lean_dec(x_347);
lean_inc(x_74);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_44);
lean_inc(x_2);
x_350 = l_Lean_Meta_splitTarget_x3f(x_2, x_98, x_44, x_43, x_75, x_74, x_349);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
x_354 = l_Lean_MessageData_ofName(x_1);
if (lean_is_scalar(x_341)) {
 x_355 = lean_alloc_ctor(7, 2, 0);
} else {
 x_355 = x_341;
 lean_ctor_set_tag(x_355, 7);
}
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
x_356 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
x_357 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_358, 0, x_2);
x_359 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
x_360 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_361 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
x_362 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_361, x_44, x_43, x_75, x_74, x_352);
lean_dec(x_74);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_44);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; 
lean_dec(x_2);
x_363 = lean_ctor_get(x_350, 1);
lean_inc(x_363);
lean_dec(x_350);
x_364 = lean_ctor_get(x_351, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 x_365 = x_351;
} else {
 lean_dec_ref(x_351);
 x_365 = lean_box(0);
}
x_366 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_363);
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_unbox(x_367);
lean_dec(x_367);
if (x_368 == 0)
{
lean_object* x_369; 
lean_dec(x_365);
lean_dec(x_341);
x_369 = lean_ctor_get(x_366, 1);
lean_inc(x_369);
lean_dec(x_366);
x_16 = x_364;
x_17 = x_44;
x_18 = x_43;
x_19 = x_75;
x_20 = x_74;
x_21 = x_369;
goto block_24;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_370 = lean_ctor_get(x_366, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_371 = x_366;
} else {
 lean_dec_ref(x_366);
 x_371 = lean_box(0);
}
x_372 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_373 = l_List_lengthTR___redArg(x_364);
x_374 = l_Nat_reprFast(x_373);
if (lean_is_scalar(x_365)) {
 x_375 = lean_alloc_ctor(3, 1, 0);
} else {
 x_375 = x_365;
 lean_ctor_set_tag(x_375, 3);
}
lean_ctor_set(x_375, 0, x_374);
x_376 = l_Lean_MessageData_ofFormat(x_375);
if (lean_is_scalar(x_371)) {
 x_377 = lean_alloc_ctor(7, 2, 0);
} else {
 x_377 = x_371;
 lean_ctor_set_tag(x_377, 7);
}
lean_ctor_set(x_377, 0, x_372);
lean_ctor_set(x_377, 1, x_376);
x_378 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
if (lean_is_scalar(x_341)) {
 x_379 = lean_alloc_ctor(7, 2, 0);
} else {
 x_379 = x_341;
 lean_ctor_set_tag(x_379, 7);
}
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
x_380 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_379, x_44, x_43, x_75, x_74, x_370);
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_16 = x_364;
x_17 = x_44;
x_18 = x_43;
x_19 = x_75;
x_20 = x_74;
x_21 = x_381;
goto block_24;
}
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_341);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_382 = lean_ctor_get(x_350, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_350, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_384 = x_350;
} else {
 lean_dec_ref(x_350);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
lean_dec(x_2);
x_386 = lean_ctor_get(x_347, 1);
lean_inc(x_386);
lean_dec(x_347);
x_387 = lean_ctor_get(x_348, 0);
lean_inc(x_387);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 x_388 = x_348;
} else {
 lean_dec_ref(x_348);
 x_388 = lean_box(0);
}
x_389 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_386);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_unbox(x_390);
lean_dec(x_390);
if (x_391 == 0)
{
lean_object* x_392; 
lean_dec(x_388);
lean_dec(x_341);
x_392 = lean_ctor_get(x_389, 1);
lean_inc(x_392);
lean_dec(x_389);
x_25 = x_113;
x_26 = x_387;
x_27 = x_44;
x_28 = x_43;
x_29 = x_75;
x_30 = x_74;
x_31 = x_392;
goto block_41;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_393 = lean_ctor_get(x_389, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_394 = x_389;
} else {
 lean_dec_ref(x_389);
 x_394 = lean_box(0);
}
x_395 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_396 = lean_array_get_size(x_387);
x_397 = l_Nat_reprFast(x_396);
if (lean_is_scalar(x_388)) {
 x_398 = lean_alloc_ctor(3, 1, 0);
} else {
 x_398 = x_388;
 lean_ctor_set_tag(x_398, 3);
}
lean_ctor_set(x_398, 0, x_397);
x_399 = l_Lean_MessageData_ofFormat(x_398);
if (lean_is_scalar(x_394)) {
 x_400 = lean_alloc_ctor(7, 2, 0);
} else {
 x_400 = x_394;
 lean_ctor_set_tag(x_400, 7);
}
lean_ctor_set(x_400, 0, x_395);
lean_ctor_set(x_400, 1, x_399);
x_401 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
if (lean_is_scalar(x_341)) {
 x_402 = lean_alloc_ctor(7, 2, 0);
} else {
 x_402 = x_341;
 lean_ctor_set_tag(x_402, 7);
}
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
x_403 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_402, x_44, x_43, x_75, x_74, x_393);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_25 = x_113;
x_26 = x_387;
x_27 = x_44;
x_28 = x_43;
x_29 = x_75;
x_30 = x_74;
x_31 = x_404;
goto block_41;
}
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_341);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_405 = lean_ctor_get(x_347, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_347, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_407 = x_347;
} else {
 lean_dec_ref(x_347);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_406);
return x_408;
}
}
default: 
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
lean_dec(x_341);
lean_dec(x_2);
x_409 = lean_ctor_get(x_338, 1);
lean_inc(x_409);
lean_dec(x_338);
x_410 = lean_ctor_get(x_340, 0);
lean_inc(x_410);
lean_dec(x_340);
x_411 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_409);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_unbox(x_412);
lean_dec(x_412);
if (x_413 == 0)
{
lean_object* x_414; 
x_414 = lean_ctor_get(x_411, 1);
lean_inc(x_414);
lean_dec(x_411);
x_2 = x_410;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_414;
goto _start;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_416 = lean_ctor_get(x_411, 1);
lean_inc(x_416);
lean_dec(x_411);
x_417 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
x_418 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_417, x_44, x_43, x_75, x_74, x_416);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
lean_dec(x_418);
x_2 = x_410;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_419;
goto _start;
}
}
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_421 = lean_ctor_get(x_338, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_338, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_423 = x_338;
} else {
 lean_dec_ref(x_338);
 x_423 = lean_box(0);
}
if (lean_is_scalar(x_423)) {
 x_424 = lean_alloc_ctor(1, 2, 0);
} else {
 x_424 = x_423;
}
lean_ctor_set(x_424, 0, x_421);
lean_ctor_set(x_424, 1, x_422);
return x_424;
}
}
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
lean_dec(x_89);
lean_dec(x_2);
x_425 = lean_ctor_get(x_95, 1);
lean_inc(x_425);
lean_dec(x_95);
x_426 = lean_ctor_get(x_96, 0);
lean_inc(x_426);
lean_dec(x_96);
x_427 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_425);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_unbox(x_428);
lean_dec(x_428);
if (x_429 == 0)
{
lean_object* x_430; 
x_430 = lean_ctor_get(x_427, 1);
lean_inc(x_430);
lean_dec(x_427);
x_2 = x_426;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_430;
goto _start;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_432 = lean_ctor_get(x_427, 1);
lean_inc(x_432);
lean_dec(x_427);
x_433 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__35;
x_434 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_433, x_44, x_43, x_75, x_74, x_432);
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
x_2 = x_426;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_435;
goto _start;
}
}
}
else
{
uint8_t x_437; 
lean_dec(x_89);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_437 = !lean_is_exclusive(x_95);
if (x_437 == 0)
{
return x_95;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_95, 0);
x_439 = lean_ctor_get(x_95, 1);
lean_inc(x_439);
lean_inc(x_438);
lean_dec(x_95);
x_440 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
return x_440;
}
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
lean_dec(x_89);
lean_dec(x_2);
x_441 = lean_ctor_get(x_92, 1);
lean_inc(x_441);
lean_dec(x_92);
x_442 = lean_ctor_get(x_93, 0);
lean_inc(x_442);
lean_dec(x_93);
x_443 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_441);
x_444 = lean_ctor_get(x_443, 0);
lean_inc(x_444);
x_445 = lean_unbox(x_444);
lean_dec(x_444);
if (x_445 == 0)
{
lean_object* x_446; 
x_446 = lean_ctor_get(x_443, 1);
lean_inc(x_446);
lean_dec(x_443);
x_2 = x_442;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_446;
goto _start;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_ctor_get(x_443, 1);
lean_inc(x_448);
lean_dec(x_443);
x_449 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__37;
x_450 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_449, x_44, x_43, x_75, x_74, x_448);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
lean_dec(x_450);
x_2 = x_442;
x_3 = x_44;
x_4 = x_43;
x_5 = x_75;
x_6 = x_74;
x_7 = x_451;
goto _start;
}
}
}
else
{
uint8_t x_453; 
lean_dec(x_89);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_453 = !lean_is_exclusive(x_92);
if (x_453 == 0)
{
return x_92;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_92, 0);
x_455 = lean_ctor_get(x_92, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_92);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
lean_dec(x_89);
lean_dec(x_2);
lean_dec(x_1);
x_457 = lean_ctor_get(x_88, 1);
lean_inc(x_457);
lean_dec(x_88);
x_458 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_457);
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
x_460 = lean_unbox(x_459);
lean_dec(x_459);
if (x_460 == 0)
{
lean_object* x_461; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
x_461 = lean_ctor_get(x_458, 1);
lean_inc(x_461);
lean_dec(x_458);
x_8 = x_461;
goto block_11;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_462 = lean_ctor_get(x_458, 1);
lean_inc(x_462);
lean_dec(x_458);
x_463 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__39;
x_464 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_463, x_44, x_43, x_75, x_74, x_462);
lean_dec(x_74);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_44);
x_465 = lean_ctor_get(x_464, 1);
lean_inc(x_465);
lean_dec(x_464);
x_8 = x_465;
goto block_11;
}
}
}
else
{
uint8_t x_466; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_466 = !lean_is_exclusive(x_88);
if (x_466 == 0)
{
return x_88;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_467 = lean_ctor_get(x_88, 0);
x_468 = lean_ctor_get(x_88, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_88);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
return x_469;
}
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_473; 
lean_dec(x_2);
lean_dec(x_1);
x_470 = lean_ctor_get(x_84, 1);
lean_inc(x_470);
lean_dec(x_84);
x_471 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_75, x_470);
x_472 = lean_ctor_get(x_471, 0);
lean_inc(x_472);
x_473 = lean_unbox(x_472);
lean_dec(x_472);
if (x_473 == 0)
{
lean_object* x_474; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
x_474 = lean_ctor_get(x_471, 1);
lean_inc(x_474);
lean_dec(x_471);
x_12 = x_474;
goto block_15;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_475 = lean_ctor_get(x_471, 1);
lean_inc(x_475);
lean_dec(x_471);
x_476 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__41;
x_477 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_476, x_44, x_43, x_75, x_74, x_475);
lean_dec(x_74);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_44);
x_478 = lean_ctor_get(x_477, 1);
lean_inc(x_478);
lean_dec(x_477);
x_12 = x_478;
goto block_15;
}
}
}
else
{
uint8_t x_479; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_479 = !lean_is_exclusive(x_84);
if (x_479 == 0)
{
return x_84;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_84, 0);
x_481 = lean_ctor_get(x_84, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_84);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
block_521:
{
lean_object* x_489; uint64_t x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; uint8_t x_499; uint8_t x_500; uint8_t x_501; uint8_t x_502; uint8_t x_503; uint8_t x_504; uint8_t x_505; uint8_t x_506; uint8_t x_507; uint8_t x_508; uint8_t x_509; uint8_t x_510; uint8_t x_511; uint8_t x_512; uint8_t x_513; uint8_t x_514; uint8_t x_515; uint8_t x_516; uint8_t x_517; uint8_t x_518; uint8_t x_519; uint8_t x_520; 
x_489 = lean_ctor_get(x_484, 0);
lean_inc(x_489);
x_490 = lean_ctor_get_uint64(x_484, sizeof(void*)*7);
x_491 = lean_ctor_get_uint8(x_484, sizeof(void*)*7 + 8);
x_492 = lean_ctor_get(x_484, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_484, 2);
lean_inc(x_493);
x_494 = lean_ctor_get(x_484, 3);
lean_inc(x_494);
x_495 = lean_ctor_get(x_484, 4);
lean_inc(x_495);
x_496 = lean_ctor_get(x_484, 5);
lean_inc(x_496);
x_497 = lean_ctor_get(x_484, 6);
lean_inc(x_497);
x_498 = lean_ctor_get_uint8(x_484, sizeof(void*)*7 + 9);
x_499 = lean_ctor_get_uint8(x_484, sizeof(void*)*7 + 10);
x_500 = lean_ctor_get_uint8(x_489, 0);
x_501 = lean_ctor_get_uint8(x_489, 1);
x_502 = lean_ctor_get_uint8(x_489, 2);
x_503 = lean_ctor_get_uint8(x_489, 3);
x_504 = lean_ctor_get_uint8(x_489, 4);
x_505 = lean_ctor_get_uint8(x_489, 5);
x_506 = lean_ctor_get_uint8(x_489, 6);
x_507 = lean_ctor_get_uint8(x_489, 7);
x_508 = lean_ctor_get_uint8(x_489, 8);
x_509 = lean_ctor_get_uint8(x_489, 9);
x_510 = lean_ctor_get_uint8(x_489, 10);
x_511 = lean_ctor_get_uint8(x_489, 11);
x_512 = lean_ctor_get_uint8(x_489, 12);
x_513 = lean_ctor_get_uint8(x_489, 13);
x_514 = lean_ctor_get_uint8(x_489, 14);
x_515 = lean_ctor_get_uint8(x_489, 15);
x_516 = lean_ctor_get_uint8(x_489, 16);
x_517 = lean_ctor_get_uint8(x_489, 17);
x_518 = lean_ctor_get_uint8(x_489, 18);
lean_dec(x_489);
x_519 = 0;
x_520 = l_Lean_Meta_TransparencyMode_lt(x_509, x_519);
if (x_520 == 0)
{
x_43 = x_485;
x_44 = x_484;
x_45 = x_500;
x_46 = x_501;
x_47 = x_502;
x_48 = x_503;
x_49 = x_504;
x_50 = x_505;
x_51 = x_506;
x_52 = x_507;
x_53 = x_508;
x_54 = x_510;
x_55 = x_511;
x_56 = x_512;
x_57 = x_513;
x_58 = x_514;
x_59 = x_515;
x_60 = x_516;
x_61 = x_517;
x_62 = x_518;
x_63 = x_490;
x_64 = x_491;
x_65 = x_492;
x_66 = x_493;
x_67 = x_494;
x_68 = x_495;
x_69 = x_496;
x_70 = x_497;
x_71 = x_498;
x_72 = x_499;
x_73 = x_488;
x_74 = x_487;
x_75 = x_486;
x_76 = x_509;
goto block_483;
}
else
{
x_43 = x_485;
x_44 = x_484;
x_45 = x_500;
x_46 = x_501;
x_47 = x_502;
x_48 = x_503;
x_49 = x_504;
x_50 = x_505;
x_51 = x_506;
x_52 = x_507;
x_53 = x_508;
x_54 = x_510;
x_55 = x_511;
x_56 = x_512;
x_57 = x_513;
x_58 = x_514;
x_59 = x_515;
x_60 = x_516;
x_61 = x_517;
x_62 = x_518;
x_63 = x_490;
x_64 = x_491;
x_65 = x_492;
x_66 = x_493;
x_67 = x_494;
x_68 = x_495;
x_69 = x_496;
x_70 = x_497;
x_71 = x_498;
x_72 = x_499;
x_73 = x_488;
x_74 = x_487;
x_75 = x_486;
x_76 = x_519;
goto block_483;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1;
x_3 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkUnfoldEq defined ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(0);
lean_inc(x_1);
x_15 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_1, x_14);
lean_inc(x_2);
x_16 = l_Lean_Expr_const___override(x_2, x_15);
x_17 = l_Lean_mkAppN(x_16, x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Meta_mkEq(x_17, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
lean_inc(x_9);
lean_inc(x_19);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = l_Lean_Meta_Simp_Result_addExtraArgs(x_3, x_7, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_182; lean_object* x_183; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_appFn_x21(x_19);
x_29 = lean_box(0);
x_30 = 1;
x_182 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_182, 0, x_28);
lean_ctor_set(x_182, 1, x_29);
lean_ctor_set_uint8(x_182, sizeof(void*)*2, x_30);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_183 = l_Lean_Meta_Simp_mkCongr(x_182, x_26, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = l_Lean_Expr_mvarId_x21(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_187 = l_Lean_Meta_applySimpResultToTarget(x_186, x_19, x_184, x_9, x_10, x_11, x_12, x_185);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_name_eq(x_2, x_6);
if (x_190 == 0)
{
lean_object* x_191; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_191 = l_Lean_Elab_Eqns_deltaLHS(x_188, x_9, x_10, x_11, x_12, x_189);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_31 = x_192;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
x_36 = x_193;
goto block_181;
}
else
{
uint8_t x_194; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_191);
if (x_194 == 0)
{
return x_191;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_191, 0);
x_196 = lean_ctor_get(x_191, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_191);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
x_31 = x_188;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
x_36 = x_189;
goto block_181;
}
}
else
{
uint8_t x_198; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_187);
if (x_198 == 0)
{
return x_187;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_187, 0);
x_200 = lean_ctor_get(x_187, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_187);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_183);
if (x_202 == 0)
{
return x_183;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_183, 0);
x_204 = lean_ctor_get(x_183, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_183);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
block_181:
{
lean_object* x_37; 
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_37 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(x_31, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_40 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(x_2, x_38, x_32, x_33, x_34, x_35, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_23, x_33, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = 0;
x_47 = 1;
lean_inc(x_7);
x_48 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_46, x_30, x_30, x_47, x_32, x_33, x_34, x_35, x_45);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_51 = l_Lean_Meta_letToHave(x_49, x_32, x_33, x_34, x_35, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_mkLambdaFVars(x_7, x_44, x_46, x_30, x_46, x_30, x_47, x_32, x_33, x_34, x_35, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_4);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_4);
lean_ctor_set(x_57, 1, x_1);
lean_ctor_set(x_57, 2, x_52);
x_58 = lean_box(0);
lean_inc(x_4);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_58);
lean_ctor_set(x_42, 0, x_4);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_55);
lean_ctor_set(x_59, 2, x_42);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_inc(x_35);
lean_inc(x_34);
x_61 = l_Lean_addDecl(x_60, x_34, x_35, x_56);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 1);
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_4);
x_65 = l_Lean_inferDefEqAttr(x_4, x_32, x_33, x_34, x_35, x_63);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_67 = lean_ctor_get(x_65, 1);
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_70 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_69, x_34, x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
uint8_t x_73; 
lean_free_object(x_65);
lean_free_object(x_61);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_70);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_70, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_70, 0, x_75);
return x_70;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_70, 1);
lean_inc(x_76);
lean_dec(x_70);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_70, 1);
lean_inc(x_79);
lean_dec(x_70);
x_80 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_81 = l_Lean_MessageData_ofConstName(x_4, x_46);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_81);
lean_ctor_set(x_65, 0, x_80);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_5);
lean_ctor_set(x_61, 0, x_65);
x_82 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_69, x_61, x_32, x_33, x_34, x_35, x_79);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_65, 1);
lean_inc(x_83);
lean_dec(x_65);
x_84 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_85 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_84, x_34, x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_free_object(x_61);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_88 = lean_ctor_get(x_85, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_89 = x_85;
} else {
 lean_dec_ref(x_85);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_dec(x_85);
x_93 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_94 = l_Lean_MessageData_ofConstName(x_4, x_46);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set_tag(x_61, 7);
lean_ctor_set(x_61, 1, x_5);
lean_ctor_set(x_61, 0, x_95);
x_96 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_84, x_61, x_32, x_33, x_34, x_35, x_92);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_96;
}
}
}
else
{
lean_free_object(x_61);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_65;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_61, 1);
lean_inc(x_97);
lean_dec(x_61);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_4);
x_98 = l_Lean_inferDefEqAttr(x_4, x_32, x_33, x_34, x_35, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_100 = x_98;
} else {
 lean_dec_ref(x_98);
 x_100 = lean_box(0);
}
x_101 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_102 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_101, x_34, x_99);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_unbox(x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_100);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_106 = x_102;
} else {
 lean_dec_ref(x_102);
 x_106 = lean_box(0);
}
x_107 = lean_box(0);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_dec(x_102);
x_110 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_111 = l_Lean_MessageData_ofConstName(x_4, x_46);
if (lean_is_scalar(x_100)) {
 x_112 = lean_alloc_ctor(7, 2, 0);
} else {
 x_112 = x_100;
 lean_ctor_set_tag(x_112, 7);
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_5);
x_114 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_101, x_113, x_32, x_33, x_34, x_35, x_109);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_114;
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_98;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_61;
}
}
else
{
uint8_t x_115; 
lean_dec(x_52);
lean_free_object(x_42);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_54);
if (x_115 == 0)
{
return x_54;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_54, 0);
x_117 = lean_ctor_get(x_54, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_54);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_free_object(x_42);
lean_dec(x_44);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_51);
if (x_119 == 0)
{
return x_51;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_51, 0);
x_121 = lean_ctor_get(x_51, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_51);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_free_object(x_42);
lean_dec(x_44);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_48);
if (x_123 == 0)
{
return x_48;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_48, 0);
x_125 = lean_ctor_get(x_48, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_48);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; 
x_127 = lean_ctor_get(x_42, 0);
x_128 = lean_ctor_get(x_42, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_42);
x_129 = 0;
x_130 = 1;
lean_inc(x_7);
x_131 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_129, x_30, x_30, x_130, x_32, x_33, x_34, x_35, x_128);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
lean_dec(x_131);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_134 = l_Lean_Meta_letToHave(x_132, x_32, x_33, x_34, x_35, x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Meta_mkLambdaFVars(x_7, x_127, x_129, x_30, x_129, x_30, x_130, x_32, x_33, x_34, x_35, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_4);
x_140 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_140, 0, x_4);
lean_ctor_set(x_140, 1, x_1);
lean_ctor_set(x_140, 2, x_135);
x_141 = lean_box(0);
lean_inc(x_4);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_4);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_138);
lean_ctor_set(x_143, 2, x_142);
x_144 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_144, 0, x_143);
lean_inc(x_35);
lean_inc(x_34);
x_145 = l_Lean_addDecl(x_144, x_34, x_35, x_139);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
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
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_4);
x_148 = l_Lean_inferDefEqAttr(x_4, x_32, x_33, x_34, x_35, x_146);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_152 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_151, x_34, x_149);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_unbox(x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_150);
lean_dec(x_147);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_156 = x_152;
} else {
 lean_dec_ref(x_152);
 x_156 = lean_box(0);
}
x_157 = lean_box(0);
if (lean_is_scalar(x_156)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_156;
}
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_155);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_152, 1);
lean_inc(x_159);
lean_dec(x_152);
x_160 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_161 = l_Lean_MessageData_ofConstName(x_4, x_129);
if (lean_is_scalar(x_150)) {
 x_162 = lean_alloc_ctor(7, 2, 0);
} else {
 x_162 = x_150;
 lean_ctor_set_tag(x_162, 7);
}
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
if (lean_is_scalar(x_147)) {
 x_163 = lean_alloc_ctor(7, 2, 0);
} else {
 x_163 = x_147;
 lean_ctor_set_tag(x_163, 7);
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_5);
x_164 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_151, x_163, x_32, x_33, x_34, x_35, x_159);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_164;
}
}
else
{
lean_dec(x_147);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_148;
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_145;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_135);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_165 = lean_ctor_get(x_137, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_137, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_167 = x_137;
} else {
 lean_dec_ref(x_137);
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
lean_dec(x_127);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_169 = lean_ctor_get(x_134, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_134, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_171 = x_134;
} else {
 lean_dec_ref(x_134);
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
lean_dec(x_127);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_173 = lean_ctor_get(x_131, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_131, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_175 = x_131;
} else {
 lean_dec_ref(x_131);
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
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_40;
}
}
else
{
uint8_t x_177; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_37);
if (x_177 == 0)
{
return x_37;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_37, 0);
x_179 = lean_ctor_get(x_37, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_37);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
else
{
uint8_t x_206; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_206 = !lean_is_exclusive(x_25);
if (x_206 == 0)
{
return x_25;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_25, 0);
x_208 = lean_ctor_get(x_25, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_25);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_18);
if (x_210 == 0)
{
return x_18;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_18, 0);
x_212 = lean_ctor_get(x_18, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_18);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_4 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_inc(x_1);
x_5 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
x_6 = l_Lean_indentD(x_3);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_tactic_hygienic;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_50; uint8_t x_75; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 7);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 8);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 9);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 10);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 11);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*13 + 1);
x_24 = lean_ctor_get(x_6, 12);
lean_inc(x_24);
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
 x_25 = x_6;
} else {
 lean_dec_ref(x_6);
 x_25 = lean_box(0);
}
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_dec(x_10);
x_27 = l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__0;
x_28 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_14, x_27, x_1);
x_29 = l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__1;
x_30 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_28, x_29);
x_75 = l_Lean_Kernel_isDiagnosticsEnabled(x_26);
lean_dec(x_26);
if (x_75 == 0)
{
if (x_30 == 0)
{
x_31 = x_12;
x_32 = x_13;
x_33 = x_15;
x_34 = x_16;
x_35 = x_17;
x_36 = x_18;
x_37 = x_19;
x_38 = x_20;
x_39 = x_21;
x_40 = x_22;
x_41 = x_23;
x_42 = x_24;
x_43 = x_7;
x_44 = x_11;
goto block_49;
}
else
{
x_50 = x_75;
goto block_74;
}
}
else
{
x_50 = x_30;
goto block_74;
}
block_49:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__2;
x_46 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_28, x_45);
if (lean_is_scalar(x_25)) {
 x_47 = lean_alloc_ctor(0, 13, 2);
} else {
 x_47 = x_25;
}
lean_ctor_set(x_47, 0, x_31);
lean_ctor_set(x_47, 1, x_32);
lean_ctor_set(x_47, 2, x_28);
lean_ctor_set(x_47, 3, x_33);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_34);
lean_ctor_set(x_47, 6, x_35);
lean_ctor_set(x_47, 7, x_36);
lean_ctor_set(x_47, 8, x_37);
lean_ctor_set(x_47, 9, x_38);
lean_ctor_set(x_47, 10, x_39);
lean_ctor_set(x_47, 11, x_40);
lean_ctor_set(x_47, 12, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*13, x_30);
lean_ctor_set_uint8(x_47, sizeof(void*)*13 + 1, x_41);
x_48 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_2, x_3, x_1, x_4, x_5, x_47, x_43, x_44);
return x_48;
}
block_74:
{
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_st_ref_take(x_7, x_11);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 5);
lean_dec(x_56);
x_57 = l_Lean_Kernel_enableDiag(x_55, x_30);
x_58 = l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__5;
lean_ctor_set(x_52, 5, x_58);
lean_ctor_set(x_52, 0, x_57);
x_59 = lean_st_ref_set(x_7, x_52, x_53);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_31 = x_12;
x_32 = x_13;
x_33 = x_15;
x_34 = x_16;
x_35 = x_17;
x_36 = x_18;
x_37 = x_19;
x_38 = x_20;
x_39 = x_21;
x_40 = x_22;
x_41 = x_23;
x_42 = x_24;
x_43 = x_7;
x_44 = x_60;
goto block_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
x_63 = lean_ctor_get(x_52, 2);
x_64 = lean_ctor_get(x_52, 3);
x_65 = lean_ctor_get(x_52, 4);
x_66 = lean_ctor_get(x_52, 6);
x_67 = lean_ctor_get(x_52, 7);
x_68 = lean_ctor_get(x_52, 8);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_69 = l_Lean_Kernel_enableDiag(x_61, x_30);
x_70 = l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__5;
x_71 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_62);
lean_ctor_set(x_71, 2, x_63);
lean_ctor_set(x_71, 3, x_64);
lean_ctor_set(x_71, 4, x_65);
lean_ctor_set(x_71, 5, x_70);
lean_ctor_set(x_71, 6, x_66);
lean_ctor_set(x_71, 7, x_67);
lean_ctor_set(x_71, 8, x_68);
x_72 = lean_st_ref_set(x_7, x_71, x_53);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_31 = x_12;
x_32 = x_13;
x_33 = x_15;
x_34 = x_16;
x_35 = x_17;
x_36 = x_18;
x_37 = x_19;
x_38 = x_20;
x_39 = x_21;
x_40 = x_22;
x_41 = x_23;
x_42 = x_24;
x_43 = x_7;
x_44 = x_73;
goto block_49;
}
}
else
{
x_31 = x_12;
x_32 = x_13;
x_33 = x_15;
x_34 = x_16;
x_35 = x_17;
x_36 = x_18;
x_37 = x_19;
x_38 = x_20;
x_39 = x_21;
x_40 = x_22;
x_41 = x_23;
x_42 = x_24;
x_43 = x_7;
x_44 = x_11;
goto block_49;
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_def", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Cannot derive ", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkUnfoldEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_mkUnfoldEq___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 5);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lean_Elab_WF_mkUnfoldEq___closed__0;
lean_inc(x_15);
x_18 = l_Lean_Meta_mkEqLikeNameFor(x_13, x_15, x_17);
x_19 = l_Lean_Elab_WF_mkUnfoldEq___closed__2;
lean_inc(x_18);
x_20 = l_Lean_MessageData_ofName(x_18);
lean_ctor_set_tag(x_9, 7);
lean_ctor_set(x_9, 1, x_20);
lean_ctor_set(x_9, 0, x_19);
x_21 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 13, 6);
lean_closure_set(x_22, 0, x_14);
lean_closure_set(x_22, 1, x_15);
lean_closure_set(x_22, 2, x_3);
lean_closure_set(x_22, 3, x_18);
lean_closure_set(x_22, 4, x_21);
lean_closure_set(x_22, 5, x_2);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__1), 3, 2);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_23);
x_25 = 0;
x_26 = lean_box(x_25);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_16);
lean_closure_set(x_27, 2, x_22);
x_28 = l_Lean_Meta_mapErrorImp___redArg(x_27, x_24, x_4, x_5, x_6, x_7, x_12);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_37 = lean_ctor_get(x_9, 0);
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_9);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 5);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_Elab_WF_mkUnfoldEq___closed__0;
lean_inc(x_41);
x_44 = l_Lean_Meta_mkEqLikeNameFor(x_39, x_41, x_43);
x_45 = l_Lean_Elab_WF_mkUnfoldEq___closed__2;
lean_inc(x_44);
x_46 = l_Lean_MessageData_ofName(x_44);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_49 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 13, 6);
lean_closure_set(x_49, 0, x_40);
lean_closure_set(x_49, 1, x_41);
lean_closure_set(x_49, 2, x_3);
lean_closure_set(x_49, 3, x_44);
lean_closure_set(x_49, 4, x_48);
lean_closure_set(x_49, 5, x_2);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__1), 3, 2);
lean_closure_set(x_51, 0, x_48);
lean_closure_set(x_51, 1, x_50);
x_52 = 0;
x_53 = lean_box(x_52);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_42);
lean_closure_set(x_54, 2, x_49);
x_55 = l_Lean_Meta_mapErrorImp___redArg(x_54, x_51, x_4, x_5, x_6, x_7, x_38);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
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
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_55, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Elab_WF_mkUnfoldEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Elab_WF_mkUnfoldEq___lam__2(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to apply '", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' to '", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mkBinaryUnfoldEq defined ", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(0);
lean_inc(x_1);
x_15 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_1, x_14);
x_16 = l_Lean_Expr_const___override(x_2, x_15);
x_17 = l_Lean_mkAppN(x_16, x_7);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_18 = l_Lean_Meta_mkEq(x_17, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
lean_inc(x_9);
lean_inc(x_19);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_19, x_21, x_9, x_10, x_11, x_12, x_20);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_Expr_mvarId_x21(x_24);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_27 = l_Lean_Elab_Eqns_deltaLHS(x_26, x_9, x_10, x_11, x_12, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = 0;
x_32 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_28);
x_33 = l_Lean_MVarId_applyConst(x_28, x_3, x_32, x_9, x_10, x_11, x_12, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_List_isEmpty___redArg(x_34);
lean_dec(x_34);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_37 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2;
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_6);
lean_ctor_set(x_22, 0, x_37);
x_38 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4;
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_28);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_43, x_9, x_10, x_11, x_12, x_35);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_44;
}
else
{
lean_object* x_45; uint8_t x_46; 
lean_dec(x_28);
lean_free_object(x_22);
lean_dec(x_6);
x_45 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_24, x_10, x_35);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = 1;
lean_inc(x_7);
x_50 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_31, x_30, x_30, x_49, x_9, x_10, x_11, x_12, x_48);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_53 = l_Lean_Meta_letToHave(x_51, x_9, x_10, x_11, x_12, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Meta_mkLambdaFVars(x_7, x_47, x_31, x_30, x_31, x_30, x_49, x_9, x_10, x_11, x_12, x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_4);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_1);
lean_ctor_set(x_59, 2, x_54);
x_60 = lean_box(0);
lean_inc(x_4);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_60);
lean_ctor_set(x_45, 0, x_4);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_57);
lean_ctor_set(x_61, 2, x_45);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_inc(x_12);
lean_inc(x_11);
x_63 = l_Lean_addDecl(x_62, x_11, x_12, x_58);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 1);
x_66 = lean_ctor_get(x_63, 0);
lean_dec(x_66);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_67 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_65);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_69 = lean_ctor_get(x_67, 1);
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_72 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_71, x_11, x_69);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_free_object(x_67);
lean_free_object(x_63);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec(x_72);
x_82 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_83 = l_Lean_MessageData_ofConstName(x_4, x_31);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_83);
lean_ctor_set(x_67, 0, x_82);
lean_ctor_set_tag(x_63, 7);
lean_ctor_set(x_63, 1, x_5);
lean_ctor_set(x_63, 0, x_67);
x_84 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_71, x_63, x_9, x_10, x_11, x_12, x_81);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_67, 1);
lean_inc(x_85);
lean_dec(x_67);
x_86 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_87 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_86, x_11, x_85);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_63);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_91 = x_87;
} else {
 lean_dec_ref(x_87);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
if (lean_is_scalar(x_91)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_91;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_90);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_dec(x_87);
x_95 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_96 = l_Lean_MessageData_ofConstName(x_4, x_31);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set_tag(x_63, 7);
lean_ctor_set(x_63, 1, x_5);
lean_ctor_set(x_63, 0, x_97);
x_98 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_86, x_63, x_9, x_10, x_11, x_12, x_94);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_98;
}
}
}
else
{
lean_free_object(x_63);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_67;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_63, 1);
lean_inc(x_99);
lean_dec(x_63);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_100 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_104 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_103, x_11, x_101);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_102);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_108 = x_104;
} else {
 lean_dec_ref(x_104);
 x_108 = lean_box(0);
}
x_109 = lean_box(0);
if (lean_is_scalar(x_108)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_108;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_107);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_104, 1);
lean_inc(x_111);
lean_dec(x_104);
x_112 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_113 = l_Lean_MessageData_ofConstName(x_4, x_31);
if (lean_is_scalar(x_102)) {
 x_114 = lean_alloc_ctor(7, 2, 0);
} else {
 x_114 = x_102;
 lean_ctor_set_tag(x_114, 7);
}
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_5);
x_116 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_103, x_115, x_9, x_10, x_11, x_12, x_111);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_116;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_100;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_63;
}
}
else
{
uint8_t x_117; 
lean_dec(x_54);
lean_free_object(x_45);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_56);
if (x_117 == 0)
{
return x_56;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_56, 0);
x_119 = lean_ctor_get(x_56, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_56);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_free_object(x_45);
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_53);
if (x_121 == 0)
{
return x_53;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_53, 0);
x_123 = lean_ctor_get(x_53, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_53);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_free_object(x_45);
lean_dec(x_47);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_50);
if (x_125 == 0)
{
return x_50;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_50, 0);
x_127 = lean_ctor_get(x_50, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_50);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_45, 0);
x_130 = lean_ctor_get(x_45, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_45);
x_131 = 1;
lean_inc(x_7);
x_132 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_31, x_30, x_30, x_131, x_9, x_10, x_11, x_12, x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_135 = l_Lean_Meta_letToHave(x_133, x_9, x_10, x_11, x_12, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Meta_mkLambdaFVars(x_7, x_129, x_31, x_30, x_31, x_30, x_131, x_9, x_10, x_11, x_12, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_4);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_4);
lean_ctor_set(x_141, 1, x_1);
lean_ctor_set(x_141, 2, x_136);
x_142 = lean_box(0);
lean_inc(x_4);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_4);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_139);
lean_ctor_set(x_144, 2, x_143);
x_145 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_145, 0, x_144);
lean_inc(x_12);
lean_inc(x_11);
x_146 = l_Lean_addDecl(x_145, x_11, x_12, x_140);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_149 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_147);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_151 = x_149;
} else {
 lean_dec_ref(x_149);
 x_151 = lean_box(0);
}
x_152 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_153 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_152, x_11, x_150);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_unbox(x_154);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_151);
lean_dec(x_148);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_157 = x_153;
} else {
 lean_dec_ref(x_153);
 x_157 = lean_box(0);
}
x_158 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_160 = lean_ctor_get(x_153, 1);
lean_inc(x_160);
lean_dec(x_153);
x_161 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_162 = l_Lean_MessageData_ofConstName(x_4, x_31);
if (lean_is_scalar(x_151)) {
 x_163 = lean_alloc_ctor(7, 2, 0);
} else {
 x_163 = x_151;
 lean_ctor_set_tag(x_163, 7);
}
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
if (lean_is_scalar(x_148)) {
 x_164 = lean_alloc_ctor(7, 2, 0);
} else {
 x_164 = x_148;
 lean_ctor_set_tag(x_164, 7);
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_5);
x_165 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_152, x_164, x_9, x_10, x_11, x_12, x_160);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_165;
}
}
else
{
lean_dec(x_148);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_149;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_146;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_136);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_166 = lean_ctor_get(x_138, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_138, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_168 = x_138;
} else {
 lean_dec_ref(x_138);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_129);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_170 = lean_ctor_get(x_135, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_135, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_172 = x_135;
} else {
 lean_dec_ref(x_135);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_129);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_174 = lean_ctor_get(x_132, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_132, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_176 = x_132;
} else {
 lean_dec_ref(x_132);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_28);
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_33);
if (x_178 == 0)
{
return x_33;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_33, 0);
x_180 = lean_ctor_get(x_33, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_33);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_27);
if (x_182 == 0)
{
return x_27;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_27, 0);
x_184 = lean_ctor_get(x_27, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_27);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_186 = lean_ctor_get(x_22, 0);
x_187 = lean_ctor_get(x_22, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_22);
x_188 = l_Lean_Expr_mvarId_x21(x_186);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_189 = l_Lean_Elab_Eqns_deltaLHS(x_188, x_9, x_10, x_11, x_12, x_187);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = 1;
x_193 = 0;
x_194 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_190);
x_195 = l_Lean_MVarId_applyConst(x_190, x_3, x_194, x_9, x_10, x_11, x_12, x_191);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = l_List_isEmpty___redArg(x_196);
lean_dec(x_196);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec(x_186);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_199 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2;
x_200 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_6);
x_201 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4;
x_202 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_203, 0, x_190);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6;
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_206, x_9, x_10, x_11, x_12, x_197);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_207;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; 
lean_dec(x_190);
lean_dec(x_6);
x_208 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_186, x_10, x_197);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
x_212 = 1;
lean_inc(x_7);
x_213 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_193, x_192, x_192, x_212, x_9, x_10, x_11, x_12, x_210);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_216 = l_Lean_Meta_letToHave(x_214, x_9, x_10, x_11, x_12, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l_Lean_Meta_mkLambdaFVars(x_7, x_209, x_193, x_192, x_193, x_192, x_212, x_9, x_10, x_11, x_12, x_218);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
lean_inc(x_4);
x_222 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_222, 0, x_4);
lean_ctor_set(x_222, 1, x_1);
lean_ctor_set(x_222, 2, x_217);
x_223 = lean_box(0);
lean_inc(x_4);
if (lean_is_scalar(x_211)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_211;
 lean_ctor_set_tag(x_224, 1);
}
lean_ctor_set(x_224, 0, x_4);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_220);
lean_ctor_set(x_225, 2, x_224);
x_226 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_226, 0, x_225);
lean_inc(x_12);
lean_inc(x_11);
x_227 = l_Lean_addDecl(x_226, x_11, x_12, x_221);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_229 = x_227;
} else {
 lean_dec_ref(x_227);
 x_229 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_230 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_228);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_232 = x_230;
} else {
 lean_dec_ref(x_230);
 x_232 = lean_box(0);
}
x_233 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_234 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_233, x_11, x_231);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_232);
lean_dec(x_229);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_238 = x_234;
} else {
 lean_dec_ref(x_234);
 x_238 = lean_box(0);
}
x_239 = lean_box(0);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_234, 1);
lean_inc(x_241);
lean_dec(x_234);
x_242 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_243 = l_Lean_MessageData_ofConstName(x_4, x_193);
if (lean_is_scalar(x_232)) {
 x_244 = lean_alloc_ctor(7, 2, 0);
} else {
 x_244 = x_232;
 lean_ctor_set_tag(x_244, 7);
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
if (lean_is_scalar(x_229)) {
 x_245 = lean_alloc_ctor(7, 2, 0);
} else {
 x_245 = x_229;
 lean_ctor_set_tag(x_245, 7);
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_5);
x_246 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_233, x_245, x_9, x_10, x_11, x_12, x_241);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_246;
}
}
else
{
lean_dec(x_229);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_230;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_227;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_217);
lean_dec(x_211);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_247 = lean_ctor_get(x_219, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_219, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_249 = x_219;
} else {
 lean_dec_ref(x_219);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_251 = lean_ctor_get(x_216, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_216, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_253 = x_216;
} else {
 lean_dec_ref(x_216);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(1, 2, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
return x_254;
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
lean_dec(x_211);
lean_dec(x_209);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_255 = lean_ctor_get(x_213, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_213, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_257 = x_213;
} else {
 lean_dec_ref(x_213);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
}
lean_ctor_set(x_258, 0, x_255);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_190);
lean_dec(x_186);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_259 = lean_ctor_get(x_195, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_195, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_261 = x_195;
} else {
 lean_dec_ref(x_195);
 x_261 = lean_box(0);
}
if (lean_is_scalar(x_261)) {
 x_262 = lean_alloc_ctor(1, 2, 0);
} else {
 x_262 = x_261;
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_260);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_186);
lean_dec(x_19);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_263 = lean_ctor_get(x_189, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_189, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_265 = x_189;
} else {
 lean_dec_ref(x_189);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_267 = !lean_is_exclusive(x_18);
if (x_267 == 0)
{
return x_18;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_18, 0);
x_269 = lean_ctor_get(x_18, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_18);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" from ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_st_ref_get(x_6, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = l_Lean_Elab_WF_mkUnfoldEq___closed__0;
lean_inc(x_18);
x_22 = l_Lean_Meta_mkEqLikeNameFor(x_16, x_18, x_21);
x_23 = l_Lean_Meta_mkEqLikeNameFor(x_20, x_2, x_21);
x_24 = l_Lean_Elab_WF_mkUnfoldEq___closed__2;
lean_inc(x_22);
x_25 = l_Lean_MessageData_ofName(x_22);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_25);
lean_ctor_set(x_12, 0, x_24);
x_26 = l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_26);
lean_ctor_set(x_8, 0, x_12);
lean_inc(x_23);
x_27 = l_Lean_MessageData_ofName(x_23);
lean_inc(x_27);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_8);
lean_ctor_set(x_28, 1, x_27);
x_29 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0), 13, 6);
lean_closure_set(x_30, 0, x_17);
lean_closure_set(x_30, 1, x_18);
lean_closure_set(x_30, 2, x_23);
lean_closure_set(x_30, 3, x_22);
lean_closure_set(x_30, 4, x_29);
lean_closure_set(x_30, 5, x_27);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__1), 3, 2);
lean_closure_set(x_32, 0, x_29);
lean_closure_set(x_32, 1, x_31);
x_33 = 0;
x_34 = lean_box(x_33);
x_35 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_35, 0, x_34);
lean_closure_set(x_35, 1, x_19);
lean_closure_set(x_35, 2, x_30);
x_36 = l_Lean_Meta_mapErrorImp___redArg(x_35, x_32, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
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
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_36);
if (x_41 == 0)
{
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 0);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_36);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_45 = lean_ctor_get(x_12, 0);
x_46 = lean_ctor_get(x_12, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_12);
x_47 = lean_ctor_get(x_10, 0);
lean_inc(x_47);
lean_dec(x_10);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 5);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_ctor_get(x_45, 0);
lean_inc(x_51);
lean_dec(x_45);
x_52 = l_Lean_Elab_WF_mkUnfoldEq___closed__0;
lean_inc(x_49);
x_53 = l_Lean_Meta_mkEqLikeNameFor(x_47, x_49, x_52);
x_54 = l_Lean_Meta_mkEqLikeNameFor(x_51, x_2, x_52);
x_55 = l_Lean_Elab_WF_mkUnfoldEq___closed__2;
lean_inc(x_53);
x_56 = l_Lean_MessageData_ofName(x_53);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_58);
lean_ctor_set(x_8, 0, x_57);
lean_inc(x_54);
x_59 = l_Lean_MessageData_ofName(x_54);
lean_inc(x_59);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_8);
lean_ctor_set(x_60, 1, x_59);
x_61 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_62 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0), 13, 6);
lean_closure_set(x_62, 0, x_48);
lean_closure_set(x_62, 1, x_49);
lean_closure_set(x_62, 2, x_54);
lean_closure_set(x_62, 3, x_53);
lean_closure_set(x_62, 4, x_61);
lean_closure_set(x_62, 5, x_59);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__1), 3, 2);
lean_closure_set(x_64, 0, x_61);
lean_closure_set(x_64, 1, x_63);
x_65 = 0;
x_66 = lean_box(x_65);
x_67 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_67, 0, x_66);
lean_closure_set(x_67, 1, x_50);
lean_closure_set(x_67, 2, x_62);
x_68 = l_Lean_Meta_mapErrorImp___redArg(x_67, x_64, x_3, x_4, x_5, x_6, x_46);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
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
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_75 = x_68;
} else {
 lean_dec_ref(x_68);
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
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_77 = lean_ctor_get(x_8, 0);
x_78 = lean_ctor_get(x_8, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_8);
x_79 = lean_st_ref_get(x_6, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = lean_ctor_get(x_77, 0);
lean_inc(x_83);
lean_dec(x_77);
x_84 = lean_ctor_get(x_1, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_1, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_1, 5);
lean_inc(x_86);
lean_dec(x_1);
x_87 = lean_ctor_get(x_80, 0);
lean_inc(x_87);
lean_dec(x_80);
x_88 = l_Lean_Elab_WF_mkUnfoldEq___closed__0;
lean_inc(x_85);
x_89 = l_Lean_Meta_mkEqLikeNameFor(x_83, x_85, x_88);
x_90 = l_Lean_Meta_mkEqLikeNameFor(x_87, x_2, x_88);
x_91 = l_Lean_Elab_WF_mkUnfoldEq___closed__2;
lean_inc(x_89);
x_92 = l_Lean_MessageData_ofName(x_89);
if (lean_is_scalar(x_82)) {
 x_93 = lean_alloc_ctor(7, 2, 0);
} else {
 x_93 = x_82;
 lean_ctor_set_tag(x_93, 7);
}
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1;
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_90);
x_96 = l_Lean_MessageData_ofName(x_90);
lean_inc(x_96);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
x_98 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_99 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0), 13, 6);
lean_closure_set(x_99, 0, x_84);
lean_closure_set(x_99, 1, x_85);
lean_closure_set(x_99, 2, x_90);
lean_closure_set(x_99, 3, x_89);
lean_closure_set(x_99, 4, x_98);
lean_closure_set(x_99, 5, x_96);
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
x_101 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__1), 3, 2);
lean_closure_set(x_101, 0, x_98);
lean_closure_set(x_101, 1, x_100);
x_102 = 0;
x_103 = lean_box(x_102);
x_104 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_104, 0, x_103);
lean_closure_set(x_104, 1, x_86);
lean_closure_set(x_104, 2, x_99);
x_105 = l_Lean_Meta_mapErrorImp___redArg(x_104, x_101, x_3, x_4, x_5, x_6, x_81);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_112 = x_105;
} else {
 lean_dec_ref(x_105);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0;
x_2 = l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WF", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_2 = l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_2 = l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_2 = l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_2 = l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0;
x_2 = l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PreDefinition", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_2 = l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_2 = l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unfold", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_2 = l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_2 = l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2544u);
x_2 = l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4;
x_3 = 0;
x_4 = l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__8);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__10);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__11);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__12);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__13);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__14);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__16);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__17);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__18);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__22 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__22();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__22);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__1);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__2);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__6);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__7);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__8);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__9);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__11);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__14 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__14();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__14);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__15 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__15();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__15);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__16 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__16();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__16);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__17 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__17();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__17);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__18 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__18();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__18);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__19 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__19();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__19);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__20 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__20();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__20);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__22 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__22();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__22);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__24 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__24();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__24);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__26 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__26();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__26);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__28 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__28();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__28);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__30 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__30();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__30);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__32 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__32();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__32);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__34 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__34();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__34);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__35 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__35();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__35);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__36 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__36();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__36);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__37 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__37();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__37);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__38 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__38();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__38);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__39 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__39();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__39);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__40 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__40();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__40);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__41 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__41();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__41);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__42 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__42();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__42);
l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43 = _init_l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43();
lean_mark_persistent(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43);
l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0 = _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0);
l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1 = _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__1);
l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2 = _init_l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2);
l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__0 = _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__0();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__0);
l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__1 = _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__1);
l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__2 = _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__2);
l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__3 = _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__3);
l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__4 = _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__4);
l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__5 = _init_l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__5);
l_Lean_Elab_WF_mkUnfoldEq___closed__0 = _init_l_Lean_Elab_WF_mkUnfoldEq___closed__0();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___closed__0);
l_Lean_Elab_WF_mkUnfoldEq___closed__1 = _init_l_Lean_Elab_WF_mkUnfoldEq___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___closed__1);
l_Lean_Elab_WF_mkUnfoldEq___closed__2 = _init_l_Lean_Elab_WF_mkUnfoldEq___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_mkUnfoldEq___closed__2);
l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0);
l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1);
l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2);
l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__3);
l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4);
l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__5);
l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6);
l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__7 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__7();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__7);
l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8);
l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__0);
l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1 = _init_l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1();
lean_mark_persistent(l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1);
l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_ = _init_l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_);
if (builtin) {res = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
