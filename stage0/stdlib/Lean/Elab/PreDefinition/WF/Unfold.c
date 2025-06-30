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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_2, x_4, x_12);
x_14 = l_Lean_Expr_app___override(x_11, x_13);
x_15 = lean_box(0);
x_16 = lean_box(1);
x_17 = lean_unbox(x_15);
x_18 = lean_unbox(x_15);
x_19 = lean_unbox(x_16);
x_20 = l_Lean_Meta_mkLambdaFVars(x_4, x_14, x_17, x_3, x_18, x_3, x_19, x_6, x_7, x_8, x_9, x_10);
return x_20;
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; 
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
x_65 = lean_box(0);
x_66 = lean_unbox(x_65);
x_67 = lean_unbox(x_65);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_68 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_63, x_64, x_62, x_66, x_67, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_72 = l_Lean_mkAppB(x_45, x_42, x_69);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_73 = l_Lean_Meta_mkEq(x_72, x_71, x_3, x_4, x_5, x_6, x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_box(0);
lean_inc(x_3);
x_77 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_74, x_76, x_3, x_4, x_5, x_6, x_75);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21;
x_81 = l_Lean_Expr_getAppFn(x_39);
x_82 = l_Lean_Expr_constLevels_x21(x_81);
lean_dec(x_81);
x_83 = l_Lean_Expr_const___override(x_80, x_82);
x_84 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__22;
x_85 = l_Lean_Expr_getAppNumArgs(x_39);
lean_inc(x_85);
x_86 = lean_mk_array(x_85, x_84);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_nat_sub(x_85, x_87);
lean_dec(x_85);
x_89 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_39, x_86, x_88);
x_90 = l_Lean_mkAppN(x_83, x_89);
lean_dec(x_89);
lean_inc(x_4);
lean_inc(x_78);
x_91 = l_Lean_Meta_mkEqTrans(x_90, x_78, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_92, x_4, x_93);
lean_dec(x_4);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
x_97 = l_Lean_Expr_mvarId_x21(x_78);
lean_dec(x_78);
lean_ctor_set(x_94, 0, x_97);
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = l_Lean_Expr_mvarId_x21(x_78);
lean_dec(x_78);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_dec(x_78);
lean_dec(x_4);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_91);
if (x_101 == 0)
{
return x_91;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_91, 0);
x_103 = lean_ctor_get(x_91, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_91);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_73);
if (x_105 == 0)
{
return x_73;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_73, 0);
x_107 = lean_ctor_get(x_73, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_73);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_68);
if (x_109 == 0)
{
return x_68;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_68, 0);
x_111 = lean_ctor_get(x_68, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_68);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
uint8_t x_113; 
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
x_113 = !lean_is_exclusive(x_58);
if (x_113 == 0)
{
return x_58;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_58, 0);
x_115 = lean_ctor_get(x_58, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_58);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
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
uint8_t x_117; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_29);
if (x_117 == 0)
{
return x_29;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_29, 0);
x_119 = lean_ctor_get(x_29, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_29);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_17);
if (x_121 == 0)
{
return x_17;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_17, 0);
x_123 = lean_ctor_get(x_17, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_17);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12;
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__10;
x_3 = lean_box(1);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_5);
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
lean_object* x_8; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint64_t x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_541; lean_object* x_542; uint8_t x_543; 
x_42 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4;
x_541 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_5, x_7);
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_unbox(x_542);
lean_dec(x_542);
if (x_543 == 0)
{
lean_object* x_544; 
x_544 = lean_ctor_get(x_541, 1);
lean_inc(x_544);
lean_dec(x_541);
x_501 = x_3;
x_502 = x_4;
x_503 = x_5;
x_504 = x_6;
x_505 = x_544;
goto block_540;
}
else
{
uint8_t x_545; 
x_545 = !lean_is_exclusive(x_541);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_546 = lean_ctor_get(x_541, 1);
x_547 = lean_ctor_get(x_541, 0);
lean_dec(x_547);
x_548 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43;
lean_inc(x_2);
x_549 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_549, 0, x_2);
lean_ctor_set_tag(x_541, 7);
lean_ctor_set(x_541, 1, x_549);
lean_ctor_set(x_541, 0, x_548);
x_550 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_551 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_551, 0, x_541);
lean_ctor_set(x_551, 1, x_550);
x_552 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_551, x_3, x_4, x_5, x_6, x_546);
x_553 = lean_ctor_get(x_552, 1);
lean_inc(x_553);
lean_dec(x_552);
x_501 = x_3;
x_502 = x_4;
x_503 = x_5;
x_504 = x_6;
x_505 = x_553;
goto block_540;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_554 = lean_ctor_get(x_541, 1);
lean_inc(x_554);
lean_dec(x_541);
x_555 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43;
lean_inc(x_2);
x_556 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_556, 0, x_2);
x_557 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
x_558 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_559 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_558);
x_560 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_559, x_3, x_4, x_5, x_6, x_554);
x_561 = lean_ctor_get(x_560, 1);
lean_inc(x_561);
lean_dec(x_560);
x_501 = x_3;
x_502 = x_4;
x_503 = x_5;
x_504 = x_6;
x_505 = x_561;
goto block_540;
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
block_500:
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
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_2);
x_84 = l_Lean_Elab_Eqns_tryURefl(x_2, x_83, x_74, x_43, x_75, x_73);
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
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_88 = l_Lean_Elab_Eqns_tryContradiction(x_2, x_44, x_74, x_43, x_75, x_87);
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
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_92 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_44, x_74, x_43, x_75, x_91);
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
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_95 = l_Lean_Elab_Eqns_simpIf_x3f(x_2, x_44, x_74, x_43, x_75, x_94);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_box(1);
x_99 = lean_unsigned_to_nat(100000u);
x_100 = lean_unsigned_to_nat(2u);
x_101 = lean_box(2);
x_102 = lean_alloc_ctor(0, 2, 23);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
x_103 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2, x_103);
x_104 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 1, x_104);
x_105 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 2, x_105);
x_106 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 3, x_106);
x_107 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 4, x_107);
x_108 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 5, x_108);
x_109 = lean_unbox(x_101);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 6, x_109);
x_110 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 7, x_110);
x_111 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 8, x_111);
x_112 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 9, x_112);
x_113 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 10, x_113);
x_114 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 11, x_114);
x_115 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 12, x_115);
x_116 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 13, x_116);
x_117 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 14, x_117);
x_118 = lean_unbox(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 15, x_118);
x_119 = lean_unbox(x_89);
lean_dec(x_89);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 16, x_119);
x_120 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 17, x_120);
x_121 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 18, x_121);
x_122 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 19, x_122);
x_123 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 20, x_123);
x_124 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 21, x_124);
x_125 = lean_unbox(x_98);
lean_ctor_set_uint8(x_102, sizeof(void*)*2 + 22, x_125);
x_126 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5;
x_127 = lean_unsigned_to_nat(0u);
x_128 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13;
x_129 = l_Lean_Meta_Simp_mkContext___redArg(x_102, x_126, x_128, x_44, x_75, x_97);
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_129, 0);
x_132 = lean_ctor_get(x_129, 1);
x_133 = lean_box(0);
x_134 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21;
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_135 = l_Lean_Meta_simpTargetStar(x_2, x_131, x_126, x_133, x_134, x_44, x_74, x_43, x_75, x_132);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = !lean_is_exclusive(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_136, 0);
x_139 = lean_ctor_get(x_136, 1);
lean_dec(x_139);
switch (lean_obj_tag(x_138)) {
case 0:
{
uint8_t x_140; 
lean_free_object(x_136);
lean_free_object(x_129);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_135);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_135, 0);
lean_dec(x_141);
x_142 = lean_box(0);
lean_ctor_set(x_135, 0, x_142);
return x_135;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_135, 1);
lean_inc(x_143);
lean_dec(x_135);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
case 1:
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
lean_dec(x_135);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_147 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_44, x_74, x_43, x_75, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_unbox(x_98);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_151 = l_Lean_Meta_splitTarget_x3f(x_2, x_150, x_44, x_74, x_43, x_75, x_149);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
x_155 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_136, 7);
lean_ctor_set(x_136, 1, x_155);
lean_ctor_set(x_136, 0, x_154);
x_156 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
lean_ctor_set_tag(x_129, 7);
lean_ctor_set(x_129, 1, x_156);
lean_ctor_set(x_129, 0, x_136);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_2);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_129);
lean_ctor_set(x_158, 1, x_157);
x_159 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_160, x_44, x_74, x_43, x_75, x_153);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_74);
lean_dec(x_44);
return x_161;
}
else
{
lean_object* x_162; uint8_t x_163; 
lean_free_object(x_129);
lean_dec(x_2);
x_162 = lean_ctor_get(x_151, 1);
lean_inc(x_162);
lean_dec(x_151);
x_163 = !lean_is_exclusive(x_152);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_164 = lean_ctor_get(x_152, 0);
x_165 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_162);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_unbox(x_166);
lean_dec(x_166);
if (x_167 == 0)
{
lean_object* x_168; 
lean_free_object(x_152);
lean_free_object(x_136);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_dec(x_165);
x_16 = x_164;
x_17 = x_44;
x_18 = x_74;
x_19 = x_43;
x_20 = x_75;
x_21 = x_168;
goto block_24;
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_165);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_170 = lean_ctor_get(x_165, 1);
x_171 = lean_ctor_get(x_165, 0);
lean_dec(x_171);
x_172 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_173 = l_List_lengthTR___redArg(x_164);
x_174 = l_Nat_reprFast(x_173);
lean_ctor_set_tag(x_152, 3);
lean_ctor_set(x_152, 0, x_174);
x_175 = l_Lean_MessageData_ofFormat(x_152);
lean_ctor_set_tag(x_165, 7);
lean_ctor_set(x_165, 1, x_175);
lean_ctor_set(x_165, 0, x_172);
x_176 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_136, 7);
lean_ctor_set(x_136, 1, x_176);
lean_ctor_set(x_136, 0, x_165);
x_177 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_136, x_44, x_74, x_43, x_75, x_170);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_16 = x_164;
x_17 = x_44;
x_18 = x_74;
x_19 = x_43;
x_20 = x_75;
x_21 = x_178;
goto block_24;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_179 = lean_ctor_get(x_165, 1);
lean_inc(x_179);
lean_dec(x_165);
x_180 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_181 = l_List_lengthTR___redArg(x_164);
x_182 = l_Nat_reprFast(x_181);
lean_ctor_set_tag(x_152, 3);
lean_ctor_set(x_152, 0, x_182);
x_183 = l_Lean_MessageData_ofFormat(x_152);
x_184 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_184, 0, x_180);
lean_ctor_set(x_184, 1, x_183);
x_185 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_136, 7);
lean_ctor_set(x_136, 1, x_185);
lean_ctor_set(x_136, 0, x_184);
x_186 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_136, x_44, x_74, x_43, x_75, x_179);
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_16 = x_164;
x_17 = x_44;
x_18 = x_74;
x_19 = x_43;
x_20 = x_75;
x_21 = x_187;
goto block_24;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_152, 0);
lean_inc(x_188);
lean_dec(x_152);
x_189 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_162);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
lean_free_object(x_136);
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_16 = x_188;
x_17 = x_44;
x_18 = x_74;
x_19 = x_43;
x_20 = x_75;
x_21 = x_192;
goto block_24;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_194 = x_189;
} else {
 lean_dec_ref(x_189);
 x_194 = lean_box(0);
}
x_195 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_196 = l_List_lengthTR___redArg(x_188);
x_197 = l_Nat_reprFast(x_196);
x_198 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = l_Lean_MessageData_ofFormat(x_198);
if (lean_is_scalar(x_194)) {
 x_200 = lean_alloc_ctor(7, 2, 0);
} else {
 x_200 = x_194;
 lean_ctor_set_tag(x_200, 7);
}
lean_ctor_set(x_200, 0, x_195);
lean_ctor_set(x_200, 1, x_199);
x_201 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_136, 7);
lean_ctor_set(x_136, 1, x_201);
lean_ctor_set(x_136, 0, x_200);
x_202 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_136, x_44, x_74, x_43, x_75, x_193);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_16 = x_188;
x_17 = x_44;
x_18 = x_74;
x_19 = x_43;
x_20 = x_75;
x_21 = x_203;
goto block_24;
}
}
}
}
else
{
uint8_t x_204; 
lean_free_object(x_136);
lean_free_object(x_129);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_151);
if (x_204 == 0)
{
return x_151;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_151, 0);
x_206 = lean_ctor_get(x_151, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_151);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_208; uint8_t x_209; 
lean_free_object(x_129);
lean_dec(x_2);
x_208 = lean_ctor_get(x_147, 1);
lean_inc(x_208);
lean_dec(x_147);
x_209 = !lean_is_exclusive(x_148);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_210 = lean_ctor_get(x_148, 0);
x_211 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_208);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_unbox(x_212);
lean_dec(x_212);
if (x_213 == 0)
{
lean_object* x_214; 
lean_free_object(x_148);
lean_free_object(x_136);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec(x_211);
x_25 = x_127;
x_26 = x_210;
x_27 = x_44;
x_28 = x_74;
x_29 = x_43;
x_30 = x_75;
x_31 = x_214;
goto block_41;
}
else
{
uint8_t x_215; 
x_215 = !lean_is_exclusive(x_211);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_216 = lean_ctor_get(x_211, 1);
x_217 = lean_ctor_get(x_211, 0);
lean_dec(x_217);
x_218 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_219 = lean_array_get_size(x_210);
x_220 = l_Nat_reprFast(x_219);
lean_ctor_set_tag(x_148, 3);
lean_ctor_set(x_148, 0, x_220);
x_221 = l_Lean_MessageData_ofFormat(x_148);
lean_ctor_set_tag(x_211, 7);
lean_ctor_set(x_211, 1, x_221);
lean_ctor_set(x_211, 0, x_218);
x_222 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_136, 7);
lean_ctor_set(x_136, 1, x_222);
lean_ctor_set(x_136, 0, x_211);
x_223 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_136, x_44, x_74, x_43, x_75, x_216);
x_224 = lean_ctor_get(x_223, 1);
lean_inc(x_224);
lean_dec(x_223);
x_25 = x_127;
x_26 = x_210;
x_27 = x_44;
x_28 = x_74;
x_29 = x_43;
x_30 = x_75;
x_31 = x_224;
goto block_41;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_225 = lean_ctor_get(x_211, 1);
lean_inc(x_225);
lean_dec(x_211);
x_226 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_227 = lean_array_get_size(x_210);
x_228 = l_Nat_reprFast(x_227);
lean_ctor_set_tag(x_148, 3);
lean_ctor_set(x_148, 0, x_228);
x_229 = l_Lean_MessageData_ofFormat(x_148);
x_230 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_229);
x_231 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_136, 7);
lean_ctor_set(x_136, 1, x_231);
lean_ctor_set(x_136, 0, x_230);
x_232 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_136, x_44, x_74, x_43, x_75, x_225);
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_25 = x_127;
x_26 = x_210;
x_27 = x_44;
x_28 = x_74;
x_29 = x_43;
x_30 = x_75;
x_31 = x_233;
goto block_41;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_234 = lean_ctor_get(x_148, 0);
lean_inc(x_234);
lean_dec(x_148);
x_235 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_208);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_unbox(x_236);
lean_dec(x_236);
if (x_237 == 0)
{
lean_object* x_238; 
lean_free_object(x_136);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_25 = x_127;
x_26 = x_234;
x_27 = x_44;
x_28 = x_74;
x_29 = x_43;
x_30 = x_75;
x_31 = x_238;
goto block_41;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_240 = x_235;
} else {
 lean_dec_ref(x_235);
 x_240 = lean_box(0);
}
x_241 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_242 = lean_array_get_size(x_234);
x_243 = l_Nat_reprFast(x_242);
x_244 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_245 = l_Lean_MessageData_ofFormat(x_244);
if (lean_is_scalar(x_240)) {
 x_246 = lean_alloc_ctor(7, 2, 0);
} else {
 x_246 = x_240;
 lean_ctor_set_tag(x_246, 7);
}
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set(x_246, 1, x_245);
x_247 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_136, 7);
lean_ctor_set(x_136, 1, x_247);
lean_ctor_set(x_136, 0, x_246);
x_248 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_136, x_44, x_74, x_43, x_75, x_239);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_25 = x_127;
x_26 = x_234;
x_27 = x_44;
x_28 = x_74;
x_29 = x_43;
x_30 = x_75;
x_31 = x_249;
goto block_41;
}
}
}
}
else
{
uint8_t x_250; 
lean_free_object(x_136);
lean_free_object(x_129);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_147);
if (x_250 == 0)
{
return x_147;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_147, 0);
x_252 = lean_ctor_get(x_147, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_147);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
default: 
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
lean_free_object(x_136);
lean_free_object(x_129);
lean_dec(x_2);
x_254 = lean_ctor_get(x_135, 1);
lean_inc(x_254);
lean_dec(x_135);
x_255 = lean_ctor_get(x_138, 0);
lean_inc(x_255);
lean_dec(x_138);
x_256 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_254);
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
x_2 = x_255;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_259;
goto _start;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_256, 1);
lean_inc(x_261);
lean_dec(x_256);
x_262 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
x_263 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_262, x_44, x_74, x_43, x_75, x_261);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_2 = x_255;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_264;
goto _start;
}
}
}
}
else
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_136, 0);
lean_inc(x_266);
lean_dec(x_136);
switch (lean_obj_tag(x_266)) {
case 0:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_free_object(x_129);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_267 = lean_ctor_get(x_135, 1);
lean_inc(x_267);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_268 = x_135;
} else {
 lean_dec_ref(x_135);
 x_268 = lean_box(0);
}
x_269 = lean_box(0);
if (lean_is_scalar(x_268)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_268;
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_267);
return x_270;
}
case 1:
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_135, 1);
lean_inc(x_271);
lean_dec(x_135);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_272 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_44, x_74, x_43, x_75, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; uint8_t x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = lean_unbox(x_98);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_276 = l_Lean_Meta_splitTarget_x3f(x_2, x_275, x_44, x_74, x_43, x_75, x_274);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
x_280 = l_Lean_MessageData_ofName(x_1);
x_281 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_282 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
lean_ctor_set_tag(x_129, 7);
lean_ctor_set(x_129, 1, x_282);
lean_ctor_set(x_129, 0, x_281);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_2);
x_284 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_284, 0, x_129);
lean_ctor_set(x_284, 1, x_283);
x_285 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_286 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_286, x_44, x_74, x_43, x_75, x_278);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_74);
lean_dec(x_44);
return x_287;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
lean_free_object(x_129);
lean_dec(x_2);
x_288 = lean_ctor_get(x_276, 1);
lean_inc(x_288);
lean_dec(x_276);
x_289 = lean_ctor_get(x_277, 0);
lean_inc(x_289);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_290 = x_277;
} else {
 lean_dec_ref(x_277);
 x_290 = lean_box(0);
}
x_291 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_288);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_unbox(x_292);
lean_dec(x_292);
if (x_293 == 0)
{
lean_object* x_294; 
lean_dec(x_290);
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec(x_291);
x_16 = x_289;
x_17 = x_44;
x_18 = x_74;
x_19 = x_43;
x_20 = x_75;
x_21 = x_294;
goto block_24;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_295 = lean_ctor_get(x_291, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_296 = x_291;
} else {
 lean_dec_ref(x_291);
 x_296 = lean_box(0);
}
x_297 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_298 = l_List_lengthTR___redArg(x_289);
x_299 = l_Nat_reprFast(x_298);
if (lean_is_scalar(x_290)) {
 x_300 = lean_alloc_ctor(3, 1, 0);
} else {
 x_300 = x_290;
 lean_ctor_set_tag(x_300, 3);
}
lean_ctor_set(x_300, 0, x_299);
x_301 = l_Lean_MessageData_ofFormat(x_300);
if (lean_is_scalar(x_296)) {
 x_302 = lean_alloc_ctor(7, 2, 0);
} else {
 x_302 = x_296;
 lean_ctor_set_tag(x_302, 7);
}
lean_ctor_set(x_302, 0, x_297);
lean_ctor_set(x_302, 1, x_301);
x_303 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
x_304 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_305 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_304, x_44, x_74, x_43, x_75, x_295);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_16 = x_289;
x_17 = x_44;
x_18 = x_74;
x_19 = x_43;
x_20 = x_75;
x_21 = x_306;
goto block_24;
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_free_object(x_129);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_307 = lean_ctor_get(x_276, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_276, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 x_309 = x_276;
} else {
 lean_dec_ref(x_276);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; uint8_t x_316; 
lean_free_object(x_129);
lean_dec(x_2);
x_311 = lean_ctor_get(x_272, 1);
lean_inc(x_311);
lean_dec(x_272);
x_312 = lean_ctor_get(x_273, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 x_313 = x_273;
} else {
 lean_dec_ref(x_273);
 x_313 = lean_box(0);
}
x_314 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_311);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_unbox(x_315);
lean_dec(x_315);
if (x_316 == 0)
{
lean_object* x_317; 
lean_dec(x_313);
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_25 = x_127;
x_26 = x_312;
x_27 = x_44;
x_28 = x_74;
x_29 = x_43;
x_30 = x_75;
x_31 = x_317;
goto block_41;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_318 = lean_ctor_get(x_314, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_319 = x_314;
} else {
 lean_dec_ref(x_314);
 x_319 = lean_box(0);
}
x_320 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_321 = lean_array_get_size(x_312);
x_322 = l_Nat_reprFast(x_321);
if (lean_is_scalar(x_313)) {
 x_323 = lean_alloc_ctor(3, 1, 0);
} else {
 x_323 = x_313;
 lean_ctor_set_tag(x_323, 3);
}
lean_ctor_set(x_323, 0, x_322);
x_324 = l_Lean_MessageData_ofFormat(x_323);
if (lean_is_scalar(x_319)) {
 x_325 = lean_alloc_ctor(7, 2, 0);
} else {
 x_325 = x_319;
 lean_ctor_set_tag(x_325, 7);
}
lean_ctor_set(x_325, 0, x_320);
lean_ctor_set(x_325, 1, x_324);
x_326 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
x_327 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_327, x_44, x_74, x_43, x_75, x_318);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_25 = x_127;
x_26 = x_312;
x_27 = x_44;
x_28 = x_74;
x_29 = x_43;
x_30 = x_75;
x_31 = x_329;
goto block_41;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_free_object(x_129);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_330 = lean_ctor_get(x_272, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_272, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_332 = x_272;
} else {
 lean_dec_ref(x_272);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
default: 
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; 
lean_free_object(x_129);
lean_dec(x_2);
x_334 = lean_ctor_get(x_135, 1);
lean_inc(x_334);
lean_dec(x_135);
x_335 = lean_ctor_get(x_266, 0);
lean_inc(x_335);
lean_dec(x_266);
x_336 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_334);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_unbox(x_337);
lean_dec(x_337);
if (x_338 == 0)
{
lean_object* x_339; 
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
lean_dec(x_336);
x_2 = x_335;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_339;
goto _start;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_341 = lean_ctor_get(x_336, 1);
lean_inc(x_341);
lean_dec(x_336);
x_342 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
x_343 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_342, x_44, x_74, x_43, x_75, x_341);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec(x_343);
x_2 = x_335;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_344;
goto _start;
}
}
}
}
}
else
{
uint8_t x_346; 
lean_free_object(x_129);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_346 = !lean_is_exclusive(x_135);
if (x_346 == 0)
{
return x_135;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_135, 0);
x_348 = lean_ctor_get(x_135, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_135);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_350 = lean_ctor_get(x_129, 0);
x_351 = lean_ctor_get(x_129, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_129);
x_352 = lean_box(0);
x_353 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21;
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_354 = l_Lean_Meta_simpTargetStar(x_2, x_350, x_126, x_352, x_353, x_44, x_74, x_43, x_75, x_351);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_357 = x_355;
} else {
 lean_dec_ref(x_355);
 x_357 = lean_box(0);
}
switch (lean_obj_tag(x_356)) {
case 0:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_357);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_358 = lean_ctor_get(x_354, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_359 = x_354;
} else {
 lean_dec_ref(x_354);
 x_359 = lean_box(0);
}
x_360 = lean_box(0);
if (lean_is_scalar(x_359)) {
 x_361 = lean_alloc_ctor(0, 2, 0);
} else {
 x_361 = x_359;
}
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_358);
return x_361;
}
case 1:
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_354, 1);
lean_inc(x_362);
lean_dec(x_354);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_363 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_44, x_74, x_43, x_75, x_362);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; uint8_t x_366; lean_object* x_367; 
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_unbox(x_98);
lean_inc(x_75);
lean_inc(x_43);
lean_inc(x_74);
lean_inc(x_44);
lean_inc(x_2);
x_367 = l_Lean_Meta_splitTarget_x3f(x_2, x_366, x_44, x_74, x_43, x_75, x_365);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_367, 0);
lean_inc(x_368);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_369 = lean_ctor_get(x_367, 1);
lean_inc(x_369);
lean_dec(x_367);
x_370 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
x_371 = l_Lean_MessageData_ofName(x_1);
if (lean_is_scalar(x_357)) {
 x_372 = lean_alloc_ctor(7, 2, 0);
} else {
 x_372 = x_357;
 lean_ctor_set_tag(x_372, 7);
}
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
x_374 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_2);
x_376 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
x_377 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_378 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
x_379 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_378, x_44, x_74, x_43, x_75, x_369);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_74);
lean_dec(x_44);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
lean_dec(x_2);
x_380 = lean_ctor_get(x_367, 1);
lean_inc(x_380);
lean_dec(x_367);
x_381 = lean_ctor_get(x_368, 0);
lean_inc(x_381);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 x_382 = x_368;
} else {
 lean_dec_ref(x_368);
 x_382 = lean_box(0);
}
x_383 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_380);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_unbox(x_384);
lean_dec(x_384);
if (x_385 == 0)
{
lean_object* x_386; 
lean_dec(x_382);
lean_dec(x_357);
x_386 = lean_ctor_get(x_383, 1);
lean_inc(x_386);
lean_dec(x_383);
x_16 = x_381;
x_17 = x_44;
x_18 = x_74;
x_19 = x_43;
x_20 = x_75;
x_21 = x_386;
goto block_24;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_387 = lean_ctor_get(x_383, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_388 = x_383;
} else {
 lean_dec_ref(x_383);
 x_388 = lean_box(0);
}
x_389 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_390 = l_List_lengthTR___redArg(x_381);
x_391 = l_Nat_reprFast(x_390);
if (lean_is_scalar(x_382)) {
 x_392 = lean_alloc_ctor(3, 1, 0);
} else {
 x_392 = x_382;
 lean_ctor_set_tag(x_392, 3);
}
lean_ctor_set(x_392, 0, x_391);
x_393 = l_Lean_MessageData_ofFormat(x_392);
if (lean_is_scalar(x_388)) {
 x_394 = lean_alloc_ctor(7, 2, 0);
} else {
 x_394 = x_388;
 lean_ctor_set_tag(x_394, 7);
}
lean_ctor_set(x_394, 0, x_389);
lean_ctor_set(x_394, 1, x_393);
x_395 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
if (lean_is_scalar(x_357)) {
 x_396 = lean_alloc_ctor(7, 2, 0);
} else {
 x_396 = x_357;
 lean_ctor_set_tag(x_396, 7);
}
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_396, x_44, x_74, x_43, x_75, x_387);
x_398 = lean_ctor_get(x_397, 1);
lean_inc(x_398);
lean_dec(x_397);
x_16 = x_381;
x_17 = x_44;
x_18 = x_74;
x_19 = x_43;
x_20 = x_75;
x_21 = x_398;
goto block_24;
}
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_357);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_399 = lean_ctor_get(x_367, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_367, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_401 = x_367;
} else {
 lean_dec_ref(x_367);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; 
lean_dec(x_2);
x_403 = lean_ctor_get(x_363, 1);
lean_inc(x_403);
lean_dec(x_363);
x_404 = lean_ctor_get(x_364, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 x_405 = x_364;
} else {
 lean_dec_ref(x_364);
 x_405 = lean_box(0);
}
x_406 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_403);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_unbox(x_407);
lean_dec(x_407);
if (x_408 == 0)
{
lean_object* x_409; 
lean_dec(x_405);
lean_dec(x_357);
x_409 = lean_ctor_get(x_406, 1);
lean_inc(x_409);
lean_dec(x_406);
x_25 = x_127;
x_26 = x_404;
x_27 = x_44;
x_28 = x_74;
x_29 = x_43;
x_30 = x_75;
x_31 = x_409;
goto block_41;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_410 = lean_ctor_get(x_406, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 lean_ctor_release(x_406, 1);
 x_411 = x_406;
} else {
 lean_dec_ref(x_406);
 x_411 = lean_box(0);
}
x_412 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_413 = lean_array_get_size(x_404);
x_414 = l_Nat_reprFast(x_413);
if (lean_is_scalar(x_405)) {
 x_415 = lean_alloc_ctor(3, 1, 0);
} else {
 x_415 = x_405;
 lean_ctor_set_tag(x_415, 3);
}
lean_ctor_set(x_415, 0, x_414);
x_416 = l_Lean_MessageData_ofFormat(x_415);
if (lean_is_scalar(x_411)) {
 x_417 = lean_alloc_ctor(7, 2, 0);
} else {
 x_417 = x_411;
 lean_ctor_set_tag(x_417, 7);
}
lean_ctor_set(x_417, 0, x_412);
lean_ctor_set(x_417, 1, x_416);
x_418 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
if (lean_is_scalar(x_357)) {
 x_419 = lean_alloc_ctor(7, 2, 0);
} else {
 x_419 = x_357;
 lean_ctor_set_tag(x_419, 7);
}
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
x_420 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_419, x_44, x_74, x_43, x_75, x_410);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_25 = x_127;
x_26 = x_404;
x_27 = x_44;
x_28 = x_74;
x_29 = x_43;
x_30 = x_75;
x_31 = x_421;
goto block_41;
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_357);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_422 = lean_ctor_get(x_363, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_363, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_424 = x_363;
} else {
 lean_dec_ref(x_363);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
default: 
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; 
lean_dec(x_357);
lean_dec(x_2);
x_426 = lean_ctor_get(x_354, 1);
lean_inc(x_426);
lean_dec(x_354);
x_427 = lean_ctor_get(x_356, 0);
lean_inc(x_427);
lean_dec(x_356);
x_428 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_426);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_unbox(x_429);
lean_dec(x_429);
if (x_430 == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
lean_dec(x_428);
x_2 = x_427;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_431;
goto _start;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_433 = lean_ctor_get(x_428, 1);
lean_inc(x_433);
lean_dec(x_428);
x_434 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
x_435 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_434, x_44, x_74, x_43, x_75, x_433);
x_436 = lean_ctor_get(x_435, 1);
lean_inc(x_436);
lean_dec(x_435);
x_2 = x_427;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_436;
goto _start;
}
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_438 = lean_ctor_get(x_354, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_354, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_440 = x_354;
} else {
 lean_dec_ref(x_354);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
lean_dec(x_89);
lean_dec(x_2);
x_442 = lean_ctor_get(x_95, 1);
lean_inc(x_442);
lean_dec(x_95);
x_443 = lean_ctor_get(x_96, 0);
lean_inc(x_443);
lean_dec(x_96);
x_444 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_442);
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_unbox(x_445);
lean_dec(x_445);
if (x_446 == 0)
{
lean_object* x_447; 
x_447 = lean_ctor_get(x_444, 1);
lean_inc(x_447);
lean_dec(x_444);
x_2 = x_443;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_447;
goto _start;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_449 = lean_ctor_get(x_444, 1);
lean_inc(x_449);
lean_dec(x_444);
x_450 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__35;
x_451 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_450, x_44, x_74, x_43, x_75, x_449);
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_2 = x_443;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_452;
goto _start;
}
}
}
else
{
uint8_t x_454; 
lean_dec(x_89);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_454 = !lean_is_exclusive(x_95);
if (x_454 == 0)
{
return x_95;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_95, 0);
x_456 = lean_ctor_get(x_95, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_95);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
lean_dec(x_89);
lean_dec(x_2);
x_458 = lean_ctor_get(x_92, 1);
lean_inc(x_458);
lean_dec(x_92);
x_459 = lean_ctor_get(x_93, 0);
lean_inc(x_459);
lean_dec(x_93);
x_460 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_458);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_unbox(x_461);
lean_dec(x_461);
if (x_462 == 0)
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_460, 1);
lean_inc(x_463);
lean_dec(x_460);
x_2 = x_459;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_463;
goto _start;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_465 = lean_ctor_get(x_460, 1);
lean_inc(x_465);
lean_dec(x_460);
x_466 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__37;
x_467 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_466, x_44, x_74, x_43, x_75, x_465);
x_468 = lean_ctor_get(x_467, 1);
lean_inc(x_468);
lean_dec(x_467);
x_2 = x_459;
x_3 = x_44;
x_4 = x_74;
x_5 = x_43;
x_6 = x_75;
x_7 = x_468;
goto _start;
}
}
}
else
{
uint8_t x_470; 
lean_dec(x_89);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_470 = !lean_is_exclusive(x_92);
if (x_470 == 0)
{
return x_92;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_92, 0);
x_472 = lean_ctor_get(x_92, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_92);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; 
lean_dec(x_89);
lean_dec(x_2);
lean_dec(x_1);
x_474 = lean_ctor_get(x_88, 1);
lean_inc(x_474);
lean_dec(x_88);
x_475 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_474);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_unbox(x_476);
lean_dec(x_476);
if (x_477 == 0)
{
lean_object* x_478; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
x_478 = lean_ctor_get(x_475, 1);
lean_inc(x_478);
lean_dec(x_475);
x_8 = x_478;
goto block_11;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_479 = lean_ctor_get(x_475, 1);
lean_inc(x_479);
lean_dec(x_475);
x_480 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__39;
x_481 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_480, x_44, x_74, x_43, x_75, x_479);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_74);
lean_dec(x_44);
x_482 = lean_ctor_get(x_481, 1);
lean_inc(x_482);
lean_dec(x_481);
x_8 = x_482;
goto block_11;
}
}
}
else
{
uint8_t x_483; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_483 = !lean_is_exclusive(x_88);
if (x_483 == 0)
{
return x_88;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_88, 0);
x_485 = lean_ctor_get(x_88, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_88);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; 
lean_dec(x_2);
lean_dec(x_1);
x_487 = lean_ctor_get(x_84, 1);
lean_inc(x_487);
lean_dec(x_84);
x_488 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_43, x_487);
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_unbox(x_489);
lean_dec(x_489);
if (x_490 == 0)
{
lean_object* x_491; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
x_491 = lean_ctor_get(x_488, 1);
lean_inc(x_491);
lean_dec(x_488);
x_12 = x_491;
goto block_15;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_492 = lean_ctor_get(x_488, 1);
lean_inc(x_492);
lean_dec(x_488);
x_493 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__41;
x_494 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_493, x_44, x_74, x_43, x_75, x_492);
lean_dec(x_75);
lean_dec(x_43);
lean_dec(x_74);
lean_dec(x_44);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec(x_494);
x_12 = x_495;
goto block_15;
}
}
}
else
{
uint8_t x_496; 
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_496 = !lean_is_exclusive(x_84);
if (x_496 == 0)
{
return x_84;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_84, 0);
x_498 = lean_ctor_get(x_84, 1);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_84);
x_499 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
return x_499;
}
}
}
block_540:
{
lean_object* x_506; uint64_t x_507; uint8_t x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; uint8_t x_516; uint8_t x_517; uint8_t x_518; uint8_t x_519; uint8_t x_520; uint8_t x_521; uint8_t x_522; uint8_t x_523; uint8_t x_524; uint8_t x_525; uint8_t x_526; uint8_t x_527; uint8_t x_528; uint8_t x_529; uint8_t x_530; uint8_t x_531; uint8_t x_532; uint8_t x_533; uint8_t x_534; uint8_t x_535; lean_object* x_536; uint8_t x_537; uint8_t x_538; 
x_506 = lean_ctor_get(x_501, 0);
lean_inc(x_506);
x_507 = lean_ctor_get_uint64(x_501, sizeof(void*)*7);
x_508 = lean_ctor_get_uint8(x_501, sizeof(void*)*7 + 8);
x_509 = lean_ctor_get(x_501, 1);
lean_inc(x_509);
x_510 = lean_ctor_get(x_501, 2);
lean_inc(x_510);
x_511 = lean_ctor_get(x_501, 3);
lean_inc(x_511);
x_512 = lean_ctor_get(x_501, 4);
lean_inc(x_512);
x_513 = lean_ctor_get(x_501, 5);
lean_inc(x_513);
x_514 = lean_ctor_get(x_501, 6);
lean_inc(x_514);
x_515 = lean_ctor_get_uint8(x_501, sizeof(void*)*7 + 9);
x_516 = lean_ctor_get_uint8(x_501, sizeof(void*)*7 + 10);
x_517 = lean_ctor_get_uint8(x_506, 0);
x_518 = lean_ctor_get_uint8(x_506, 1);
x_519 = lean_ctor_get_uint8(x_506, 2);
x_520 = lean_ctor_get_uint8(x_506, 3);
x_521 = lean_ctor_get_uint8(x_506, 4);
x_522 = lean_ctor_get_uint8(x_506, 5);
x_523 = lean_ctor_get_uint8(x_506, 6);
x_524 = lean_ctor_get_uint8(x_506, 7);
x_525 = lean_ctor_get_uint8(x_506, 8);
x_526 = lean_ctor_get_uint8(x_506, 9);
x_527 = lean_ctor_get_uint8(x_506, 10);
x_528 = lean_ctor_get_uint8(x_506, 11);
x_529 = lean_ctor_get_uint8(x_506, 12);
x_530 = lean_ctor_get_uint8(x_506, 13);
x_531 = lean_ctor_get_uint8(x_506, 14);
x_532 = lean_ctor_get_uint8(x_506, 15);
x_533 = lean_ctor_get_uint8(x_506, 16);
x_534 = lean_ctor_get_uint8(x_506, 17);
x_535 = lean_ctor_get_uint8(x_506, 18);
lean_dec(x_506);
x_536 = lean_box(0);
x_537 = lean_unbox(x_536);
x_538 = l_Lean_Meta_TransparencyMode_lt(x_526, x_537);
if (x_538 == 0)
{
x_43 = x_503;
x_44 = x_501;
x_45 = x_517;
x_46 = x_518;
x_47 = x_519;
x_48 = x_520;
x_49 = x_521;
x_50 = x_522;
x_51 = x_523;
x_52 = x_524;
x_53 = x_525;
x_54 = x_527;
x_55 = x_528;
x_56 = x_529;
x_57 = x_530;
x_58 = x_531;
x_59 = x_532;
x_60 = x_533;
x_61 = x_534;
x_62 = x_535;
x_63 = x_507;
x_64 = x_508;
x_65 = x_509;
x_66 = x_510;
x_67 = x_511;
x_68 = x_512;
x_69 = x_513;
x_70 = x_514;
x_71 = x_515;
x_72 = x_516;
x_73 = x_505;
x_74 = x_502;
x_75 = x_504;
x_76 = x_526;
goto block_500;
}
else
{
uint8_t x_539; 
x_539 = lean_unbox(x_536);
x_43 = x_503;
x_44 = x_501;
x_45 = x_517;
x_46 = x_518;
x_47 = x_519;
x_48 = x_520;
x_49 = x_521;
x_50 = x_522;
x_51 = x_523;
x_52 = x_524;
x_53 = x_525;
x_54 = x_527;
x_55 = x_528;
x_56 = x_529;
x_57 = x_530;
x_58 = x_531;
x_59 = x_532;
x_60 = x_533;
x_61 = x_534;
x_62 = x_535;
x_63 = x_507;
x_64 = x_508;
x_65 = x_509;
x_66 = x_510;
x_67 = x_511;
x_68 = x_512;
x_69 = x_513;
x_70 = x_514;
x_71 = x_515;
x_72 = x_516;
x_73 = x_505;
x_74 = x_502;
x_75 = x_504;
x_76 = x_539;
goto block_500;
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_appFn_x21(x_19);
x_29 = lean_box(0);
x_30 = lean_box(1);
x_204 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_204, 0, x_28);
lean_ctor_set(x_204, 1, x_29);
x_205 = lean_unbox(x_30);
lean_ctor_set_uint8(x_204, sizeof(void*)*2, x_205);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_206 = l_Lean_Meta_Simp_mkCongr(x_204, x_26, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = l_Lean_Expr_mvarId_x21(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_210 = l_Lean_Meta_applySimpResultToTarget(x_209, x_19, x_207, x_9, x_10, x_11, x_12, x_208);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; uint8_t x_213; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_name_eq(x_2, x_6);
if (x_213 == 0)
{
lean_object* x_214; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_214 = l_Lean_Elab_Eqns_deltaLHS(x_211, x_9, x_10, x_11, x_12, x_212);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_31 = x_215;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
x_36 = x_216;
goto block_203;
}
else
{
uint8_t x_217; 
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
x_217 = !lean_is_exclusive(x_214);
if (x_217 == 0)
{
return x_214;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_214, 0);
x_219 = lean_ctor_get(x_214, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_214);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
x_31 = x_211;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
x_36 = x_212;
goto block_203;
}
}
else
{
uint8_t x_221; 
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
x_221 = !lean_is_exclusive(x_210);
if (x_221 == 0)
{
return x_210;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_210, 0);
x_223 = lean_ctor_get(x_210, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_210);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
else
{
uint8_t x_225; 
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
x_225 = !lean_is_exclusive(x_206);
if (x_225 == 0)
{
return x_206;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_206, 0);
x_227 = lean_ctor_get(x_206, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_206);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
block_203:
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_box(0);
x_47 = lean_box(1);
x_48 = lean_unbox(x_46);
x_49 = lean_unbox(x_30);
x_50 = lean_unbox(x_30);
x_51 = lean_unbox(x_47);
lean_inc(x_7);
x_52 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_48, x_49, x_50, x_51, x_32, x_33, x_34, x_35, x_45);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_55 = l_Lean_Meta_letToHave(x_53, x_32, x_33, x_34, x_35, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unbox(x_46);
x_59 = lean_unbox(x_30);
x_60 = lean_unbox(x_46);
x_61 = lean_unbox(x_30);
x_62 = lean_unbox(x_47);
x_63 = l_Lean_Meta_mkLambdaFVars(x_7, x_44, x_58, x_59, x_60, x_61, x_62, x_32, x_33, x_34, x_35, x_57);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_4);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_1);
lean_ctor_set(x_66, 2, x_56);
x_67 = lean_box(0);
lean_inc(x_4);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_67);
lean_ctor_set(x_42, 0, x_4);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_64);
lean_ctor_set(x_68, 2, x_42);
x_69 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_inc(x_35);
lean_inc(x_34);
x_70 = l_Lean_addDecl(x_69, x_34, x_35, x_65);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_70, 1);
x_73 = lean_ctor_get(x_70, 0);
lean_dec(x_73);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_4);
x_74 = l_Lean_inferDefEqAttr(x_4, x_32, x_33, x_34, x_35, x_72);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_76 = lean_ctor_get(x_74, 1);
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
x_78 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_79 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_78, x_34, x_76);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
lean_free_object(x_74);
lean_free_object(x_70);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_79, 0, x_84);
return x_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_dec(x_79);
x_89 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_90 = lean_unbox(x_46);
x_91 = l_Lean_MessageData_ofConstName(x_4, x_90);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_91);
lean_ctor_set(x_74, 0, x_89);
lean_ctor_set_tag(x_70, 7);
lean_ctor_set(x_70, 1, x_5);
lean_ctor_set(x_70, 0, x_74);
x_92 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_78, x_70, x_32, x_33, x_34, x_35, x_88);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_93 = lean_ctor_get(x_74, 1);
lean_inc(x_93);
lean_dec(x_74);
x_94 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_95 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_94, x_34, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_free_object(x_70);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_98 = lean_ctor_get(x_95, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_99 = x_95;
} else {
 lean_dec_ref(x_95);
 x_99 = lean_box(0);
}
x_100 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_99;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_dec(x_95);
x_103 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_104 = lean_unbox(x_46);
x_105 = l_Lean_MessageData_ofConstName(x_4, x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set_tag(x_70, 7);
lean_ctor_set(x_70, 1, x_5);
lean_ctor_set(x_70, 0, x_106);
x_107 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_94, x_70, x_32, x_33, x_34, x_35, x_102);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_107;
}
}
}
else
{
lean_free_object(x_70);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_74;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_70, 1);
lean_inc(x_108);
lean_dec(x_70);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_4);
x_109 = l_Lean_inferDefEqAttr(x_4, x_32, x_33, x_34, x_35, x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_113 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_112, x_34, x_110);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_111);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_117 = x_113;
} else {
 lean_dec_ref(x_113);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
lean_dec(x_113);
x_121 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_122 = lean_unbox(x_46);
x_123 = l_Lean_MessageData_ofConstName(x_4, x_122);
if (lean_is_scalar(x_111)) {
 x_124 = lean_alloc_ctor(7, 2, 0);
} else {
 x_124 = x_111;
 lean_ctor_set_tag(x_124, 7);
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_5);
x_126 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_112, x_125, x_32, x_33, x_34, x_35, x_120);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_126;
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
return x_109;
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
return x_70;
}
}
else
{
uint8_t x_127; 
lean_dec(x_56);
lean_free_object(x_42);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_63);
if (x_127 == 0)
{
return x_63;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_63, 0);
x_129 = lean_ctor_get(x_63, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_63);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; 
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
x_131 = !lean_is_exclusive(x_55);
if (x_131 == 0)
{
return x_55;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_55, 0);
x_133 = lean_ctor_get(x_55, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_55);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
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
x_135 = !lean_is_exclusive(x_52);
if (x_135 == 0)
{
return x_52;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_52, 0);
x_137 = lean_ctor_get(x_52, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_52);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; 
x_139 = lean_ctor_get(x_42, 0);
x_140 = lean_ctor_get(x_42, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_42);
x_141 = lean_box(0);
x_142 = lean_box(1);
x_143 = lean_unbox(x_141);
x_144 = lean_unbox(x_30);
x_145 = lean_unbox(x_30);
x_146 = lean_unbox(x_142);
lean_inc(x_7);
x_147 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_143, x_144, x_145, x_146, x_32, x_33, x_34, x_35, x_140);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_150 = l_Lean_Meta_letToHave(x_148, x_32, x_33, x_34, x_35, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; lean_object* x_158; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_unbox(x_141);
x_154 = lean_unbox(x_30);
x_155 = lean_unbox(x_141);
x_156 = lean_unbox(x_30);
x_157 = lean_unbox(x_142);
x_158 = l_Lean_Meta_mkLambdaFVars(x_7, x_139, x_153, x_154, x_155, x_156, x_157, x_32, x_33, x_34, x_35, x_152);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_4);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_4);
lean_ctor_set(x_161, 1, x_1);
lean_ctor_set(x_161, 2, x_151);
x_162 = lean_box(0);
lean_inc(x_4);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_4);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_159);
lean_ctor_set(x_164, 2, x_163);
x_165 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_165, 0, x_164);
lean_inc(x_35);
lean_inc(x_34);
x_166 = l_Lean_addDecl(x_165, x_34, x_35, x_160);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_168 = x_166;
} else {
 lean_dec_ref(x_166);
 x_168 = lean_box(0);
}
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_4);
x_169 = l_Lean_inferDefEqAttr(x_4, x_32, x_33, x_34, x_35, x_167);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_171 = x_169;
} else {
 lean_dec_ref(x_169);
 x_171 = lean_box(0);
}
x_172 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_173 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_172, x_34, x_170);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_171);
lean_dec(x_168);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_177 = x_173;
} else {
 lean_dec_ref(x_173);
 x_177 = lean_box(0);
}
x_178 = lean_box(0);
if (lean_is_scalar(x_177)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_177;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_176);
return x_179;
}
else
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_180 = lean_ctor_get(x_173, 1);
lean_inc(x_180);
lean_dec(x_173);
x_181 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_182 = lean_unbox(x_141);
x_183 = l_Lean_MessageData_ofConstName(x_4, x_182);
if (lean_is_scalar(x_171)) {
 x_184 = lean_alloc_ctor(7, 2, 0);
} else {
 x_184 = x_171;
 lean_ctor_set_tag(x_184, 7);
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_183);
if (lean_is_scalar(x_168)) {
 x_185 = lean_alloc_ctor(7, 2, 0);
} else {
 x_185 = x_168;
 lean_ctor_set_tag(x_185, 7);
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_5);
x_186 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_172, x_185, x_32, x_33, x_34, x_35, x_180);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_186;
}
}
else
{
lean_dec(x_168);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_169;
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
return x_166;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_151);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_187 = lean_ctor_get(x_158, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_158, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_189 = x_158;
} else {
 lean_dec_ref(x_158);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_139);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_191 = lean_ctor_get(x_150, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_150, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_193 = x_150;
} else {
 lean_dec_ref(x_150);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_139);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_195 = lean_ctor_get(x_147, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_147, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_197 = x_147;
} else {
 lean_dec_ref(x_147);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
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
uint8_t x_199; 
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
x_199 = !lean_is_exclusive(x_37);
if (x_199 == 0)
{
return x_37;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_37, 0);
x_201 = lean_ctor_get(x_37, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_37);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
}
else
{
uint8_t x_229; 
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
x_229 = !lean_is_exclusive(x_25);
if (x_229 == 0)
{
return x_25;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_25, 0);
x_231 = lean_ctor_get(x_25, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_25);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
else
{
uint8_t x_233; 
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
x_233 = !lean_is_exclusive(x_18);
if (x_233 == 0)
{
return x_18;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_18, 0);
x_235 = lean_ctor_get(x_18, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_18);
x_236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
return x_236;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_74; 
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
x_74 = l_Lean_Kernel_isDiagnosticsEnabled(x_26);
lean_dec(x_26);
if (x_74 == 0)
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
goto block_73;
}
}
else
{
if (x_30 == 0)
{
goto block_73;
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
block_73:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_st_ref_take(x_7, x_11);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 5);
lean_dec(x_55);
x_56 = l_Lean_Kernel_enableDiag(x_54, x_30);
x_57 = l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__5;
lean_ctor_set(x_51, 5, x_57);
lean_ctor_set(x_51, 0, x_56);
x_58 = lean_st_ref_set(x_7, x_51, x_52);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
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
x_44 = x_59;
goto block_49;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
x_62 = lean_ctor_get(x_51, 2);
x_63 = lean_ctor_get(x_51, 3);
x_64 = lean_ctor_get(x_51, 4);
x_65 = lean_ctor_get(x_51, 6);
x_66 = lean_ctor_get(x_51, 7);
x_67 = lean_ctor_get(x_51, 8);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_68 = l_Lean_Kernel_enableDiag(x_60, x_30);
x_69 = l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__5;
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_62);
lean_ctor_set(x_70, 3, x_63);
lean_ctor_set(x_70, 4, x_64);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set(x_70, 6, x_65);
lean_ctor_set(x_70, 7, x_66);
lean_ctor_set(x_70, 8, x_67);
x_71 = lean_st_ref_set(x_7, x_70, x_52);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
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
x_44 = x_72;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_25 = lean_box(0);
x_26 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_26, 0, x_25);
lean_closure_set(x_26, 1, x_16);
lean_closure_set(x_26, 2, x_22);
x_27 = l_Lean_Meta_mapErrorImp___redArg(x_26, x_24, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_9);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 3);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 5);
lean_inc(x_41);
lean_dec(x_1);
x_42 = l_Lean_Elab_WF_mkUnfoldEq___closed__0;
lean_inc(x_40);
x_43 = l_Lean_Meta_mkEqLikeNameFor(x_38, x_40, x_42);
x_44 = l_Lean_Elab_WF_mkUnfoldEq___closed__2;
lean_inc(x_43);
x_45 = l_Lean_MessageData_ofName(x_43);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_48 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 13, 6);
lean_closure_set(x_48, 0, x_39);
lean_closure_set(x_48, 1, x_40);
lean_closure_set(x_48, 2, x_3);
lean_closure_set(x_48, 3, x_43);
lean_closure_set(x_48, 4, x_47);
lean_closure_set(x_48, 5, x_2);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__1), 3, 2);
lean_closure_set(x_50, 0, x_47);
lean_closure_set(x_50, 1, x_49);
x_51 = lean_box(0);
x_52 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_52, 0, x_51);
lean_closure_set(x_52, 1, x_41);
lean_closure_set(x_52, 2, x_48);
x_53 = l_Lean_Meta_mapErrorImp___redArg(x_52, x_50, x_4, x_5, x_6, x_7, x_37);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_box(0);
x_2 = lean_box(1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 0, 4);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, 0, x_5);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, 1, x_6);
x_7 = lean_unbox(x_1);
lean_ctor_set_uint8(x_4, 2, x_7);
x_8 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, 3, x_8);
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
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(1);
x_31 = lean_box(0);
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
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_box(1);
x_50 = lean_unbox(x_31);
x_51 = lean_unbox(x_30);
x_52 = lean_unbox(x_30);
x_53 = lean_unbox(x_49);
lean_inc(x_7);
x_54 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_50, x_51, x_52, x_53, x_9, x_10, x_11, x_12, x_48);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_57 = l_Lean_Meta_letToHave(x_55, x_9, x_10, x_11, x_12, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_unbox(x_31);
x_61 = lean_unbox(x_30);
x_62 = lean_unbox(x_31);
x_63 = lean_unbox(x_30);
x_64 = lean_unbox(x_49);
x_65 = l_Lean_Meta_mkLambdaFVars(x_7, x_47, x_60, x_61, x_62, x_63, x_64, x_9, x_10, x_11, x_12, x_59);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
lean_inc(x_4);
x_68 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_1);
lean_ctor_set(x_68, 2, x_58);
x_69 = lean_box(0);
lean_inc(x_4);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_69);
lean_ctor_set(x_45, 0, x_4);
x_70 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_45);
x_71 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_71, 0, x_70);
lean_inc(x_12);
lean_inc(x_11);
x_72 = l_Lean_addDecl(x_71, x_11, x_12, x_67);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_72, 1);
x_75 = lean_ctor_get(x_72, 0);
lean_dec(x_75);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_76 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_74);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_78 = lean_ctor_get(x_76, 1);
x_79 = lean_ctor_get(x_76, 0);
lean_dec(x_79);
x_80 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_81 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_80, x_11, x_78);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
uint8_t x_84; 
lean_free_object(x_76);
lean_free_object(x_72);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_84 = !lean_is_exclusive(x_81);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_81, 0);
lean_dec(x_85);
x_86 = lean_box(0);
lean_ctor_set(x_81, 0, x_86);
return x_81;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_dec(x_81);
x_91 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_92 = lean_unbox(x_31);
x_93 = l_Lean_MessageData_ofConstName(x_4, x_92);
lean_ctor_set_tag(x_76, 7);
lean_ctor_set(x_76, 1, x_93);
lean_ctor_set(x_76, 0, x_91);
lean_ctor_set_tag(x_72, 7);
lean_ctor_set(x_72, 1, x_5);
lean_ctor_set(x_72, 0, x_76);
x_94 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_80, x_72, x_9, x_10, x_11, x_12, x_90);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_95 = lean_ctor_get(x_76, 1);
lean_inc(x_95);
lean_dec(x_76);
x_96 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_97 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_96, x_11, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_72);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_dec(x_97);
x_105 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_106 = lean_unbox(x_31);
x_107 = l_Lean_MessageData_ofConstName(x_4, x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set_tag(x_72, 7);
lean_ctor_set(x_72, 1, x_5);
lean_ctor_set(x_72, 0, x_108);
x_109 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_96, x_72, x_9, x_10, x_11, x_12, x_104);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_109;
}
}
}
else
{
lean_free_object(x_72);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_76;
}
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_72, 1);
lean_inc(x_110);
lean_dec(x_72);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_111 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_115 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_114, x_11, x_112);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_113);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_119 = x_115;
} else {
 lean_dec_ref(x_115);
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
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_115, 1);
lean_inc(x_122);
lean_dec(x_115);
x_123 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_124 = lean_unbox(x_31);
x_125 = l_Lean_MessageData_ofConstName(x_4, x_124);
if (lean_is_scalar(x_113)) {
 x_126 = lean_alloc_ctor(7, 2, 0);
} else {
 x_126 = x_113;
 lean_ctor_set_tag(x_126, 7);
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_5);
x_128 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_114, x_127, x_9, x_10, x_11, x_12, x_122);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_128;
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
return x_111;
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
return x_72;
}
}
else
{
uint8_t x_129; 
lean_dec(x_58);
lean_free_object(x_45);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_65);
if (x_129 == 0)
{
return x_65;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_65, 0);
x_131 = lean_ctor_get(x_65, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_65);
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
x_133 = !lean_is_exclusive(x_57);
if (x_133 == 0)
{
return x_57;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_57, 0);
x_135 = lean_ctor_get(x_57, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_57);
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
x_137 = !lean_is_exclusive(x_54);
if (x_137 == 0)
{
return x_54;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_54, 0);
x_139 = lean_ctor_get(x_54, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_54);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; uint8_t x_147; lean_object* x_148; 
x_141 = lean_ctor_get(x_45, 0);
x_142 = lean_ctor_get(x_45, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_45);
x_143 = lean_box(1);
x_144 = lean_unbox(x_31);
x_145 = lean_unbox(x_30);
x_146 = lean_unbox(x_30);
x_147 = lean_unbox(x_143);
lean_inc(x_7);
x_148 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_144, x_145, x_146, x_147, x_9, x_10, x_11, x_12, x_142);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_151 = l_Lean_Meta_letToHave(x_149, x_9, x_10, x_11, x_12, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; lean_object* x_159; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_unbox(x_31);
x_155 = lean_unbox(x_30);
x_156 = lean_unbox(x_31);
x_157 = lean_unbox(x_30);
x_158 = lean_unbox(x_143);
x_159 = l_Lean_Meta_mkLambdaFVars(x_7, x_141, x_154, x_155, x_156, x_157, x_158, x_9, x_10, x_11, x_12, x_153);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_4);
x_162 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_162, 0, x_4);
lean_ctor_set(x_162, 1, x_1);
lean_ctor_set(x_162, 2, x_152);
x_163 = lean_box(0);
lean_inc(x_4);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_4);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_160);
lean_ctor_set(x_165, 2, x_164);
x_166 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_166, 0, x_165);
lean_inc(x_12);
lean_inc(x_11);
x_167 = l_Lean_addDecl(x_166, x_11, x_12, x_161);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_170 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_168);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
x_173 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_174 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_173, x_11, x_171);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_172);
lean_dec(x_169);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
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
x_179 = lean_box(0);
if (lean_is_scalar(x_178)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_178;
}
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get(x_174, 1);
lean_inc(x_181);
lean_dec(x_174);
x_182 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_183 = lean_unbox(x_31);
x_184 = l_Lean_MessageData_ofConstName(x_4, x_183);
if (lean_is_scalar(x_172)) {
 x_185 = lean_alloc_ctor(7, 2, 0);
} else {
 x_185 = x_172;
 lean_ctor_set_tag(x_185, 7);
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_184);
if (lean_is_scalar(x_169)) {
 x_186 = lean_alloc_ctor(7, 2, 0);
} else {
 x_186 = x_169;
 lean_ctor_set_tag(x_186, 7);
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_5);
x_187 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_173, x_186, x_9, x_10, x_11, x_12, x_181);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_187;
}
}
else
{
lean_dec(x_169);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_170;
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
return x_167;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_152);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_188 = lean_ctor_get(x_159, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_159, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_190 = x_159;
} else {
 lean_dec_ref(x_159);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_141);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_192 = lean_ctor_get(x_151, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_151, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_194 = x_151;
} else {
 lean_dec_ref(x_151);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_141);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_196 = lean_ctor_get(x_148, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_148, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_198 = x_148;
} else {
 lean_dec_ref(x_148);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
}
}
else
{
uint8_t x_200; 
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
x_200 = !lean_is_exclusive(x_33);
if (x_200 == 0)
{
return x_33;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_33, 0);
x_202 = lean_ctor_get(x_33, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_33);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
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
x_204 = !lean_is_exclusive(x_27);
if (x_204 == 0)
{
return x_27;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_27, 0);
x_206 = lean_ctor_get(x_27, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_27);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_22, 0);
x_209 = lean_ctor_get(x_22, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_22);
x_210 = l_Lean_Expr_mvarId_x21(x_208);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_211 = l_Lean_Elab_Eqns_deltaLHS(x_210, x_9, x_10, x_11, x_12, x_209);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_box(1);
x_215 = lean_box(0);
x_216 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_212);
x_217 = l_Lean_MVarId_applyConst(x_212, x_3, x_216, x_9, x_10, x_11, x_12, x_213);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_List_isEmpty___redArg(x_218);
lean_dec(x_218);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_208);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_221 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2;
x_222 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_6);
x_223 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4;
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_212);
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6;
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_228, x_9, x_10, x_11, x_12, x_219);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; uint8_t x_236; uint8_t x_237; uint8_t x_238; lean_object* x_239; 
lean_dec(x_212);
lean_dec(x_6);
x_230 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_208, x_10, x_219);
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_233 = x_230;
} else {
 lean_dec_ref(x_230);
 x_233 = lean_box(0);
}
x_234 = lean_box(1);
x_235 = lean_unbox(x_215);
x_236 = lean_unbox(x_214);
x_237 = lean_unbox(x_214);
x_238 = lean_unbox(x_234);
lean_inc(x_7);
x_239 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_235, x_236, x_237, x_238, x_9, x_10, x_11, x_12, x_232);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec(x_239);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_242 = l_Lean_Meta_letToHave(x_240, x_9, x_10, x_11, x_12, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; uint8_t x_249; lean_object* x_250; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_245 = lean_unbox(x_215);
x_246 = lean_unbox(x_214);
x_247 = lean_unbox(x_215);
x_248 = lean_unbox(x_214);
x_249 = lean_unbox(x_234);
x_250 = l_Lean_Meta_mkLambdaFVars(x_7, x_231, x_245, x_246, x_247, x_248, x_249, x_9, x_10, x_11, x_12, x_244);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_4);
x_253 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_253, 0, x_4);
lean_ctor_set(x_253, 1, x_1);
lean_ctor_set(x_253, 2, x_243);
x_254 = lean_box(0);
lean_inc(x_4);
if (lean_is_scalar(x_233)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_233;
 lean_ctor_set_tag(x_255, 1);
}
lean_ctor_set(x_255, 0, x_4);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_251);
lean_ctor_set(x_256, 2, x_255);
x_257 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_257, 0, x_256);
lean_inc(x_12);
lean_inc(x_11);
x_258 = l_Lean_addDecl(x_257, x_11, x_12, x_252);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_260 = x_258;
} else {
 lean_dec_ref(x_258);
 x_260 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_261 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_259);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_263 = x_261;
} else {
 lean_dec_ref(x_261);
 x_263 = lean_box(0);
}
x_264 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_265 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_264, x_11, x_262);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_unbox(x_266);
lean_dec(x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_263);
lean_dec(x_260);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_268 = lean_ctor_get(x_265, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_269 = x_265;
} else {
 lean_dec_ref(x_265);
 x_269 = lean_box(0);
}
x_270 = lean_box(0);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_269;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_268);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = lean_ctor_get(x_265, 1);
lean_inc(x_272);
lean_dec(x_265);
x_273 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_274 = lean_unbox(x_215);
x_275 = l_Lean_MessageData_ofConstName(x_4, x_274);
if (lean_is_scalar(x_263)) {
 x_276 = lean_alloc_ctor(7, 2, 0);
} else {
 x_276 = x_263;
 lean_ctor_set_tag(x_276, 7);
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_275);
if (lean_is_scalar(x_260)) {
 x_277 = lean_alloc_ctor(7, 2, 0);
} else {
 x_277 = x_260;
 lean_ctor_set_tag(x_277, 7);
}
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_5);
x_278 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_264, x_277, x_9, x_10, x_11, x_12, x_272);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_278;
}
}
else
{
lean_dec(x_260);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_261;
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
return x_258;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_243);
lean_dec(x_233);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_279 = lean_ctor_get(x_250, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_250, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_281 = x_250;
} else {
 lean_dec_ref(x_250);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_283 = lean_ctor_get(x_242, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_242, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_285 = x_242;
} else {
 lean_dec_ref(x_242);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_233);
lean_dec(x_231);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_287 = lean_ctor_get(x_239, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_239, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_289 = x_239;
} else {
 lean_dec_ref(x_239);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_212);
lean_dec(x_208);
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
x_291 = lean_ctor_get(x_217, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_217, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_293 = x_217;
} else {
 lean_dec_ref(x_217);
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
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_208);
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
x_295 = lean_ctor_get(x_211, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_211, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_297 = x_211;
} else {
 lean_dec_ref(x_211);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
}
else
{
uint8_t x_299; 
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
x_299 = !lean_is_exclusive(x_18);
if (x_299 == 0)
{
return x_18;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_18, 0);
x_301 = lean_ctor_get(x_18, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_18);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_33 = lean_box(0);
x_34 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_34, 0, x_33);
lean_closure_set(x_34, 1, x_19);
lean_closure_set(x_34, 2, x_30);
x_35 = l_Lean_Meta_mapErrorImp___redArg(x_34, x_32, x_3, x_4, x_5, x_6, x_15);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_ctor_get(x_10, 0);
lean_inc(x_46);
lean_dec(x_10);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 5);
lean_inc(x_49);
lean_dec(x_1);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
lean_dec(x_44);
x_51 = l_Lean_Elab_WF_mkUnfoldEq___closed__0;
lean_inc(x_48);
x_52 = l_Lean_Meta_mkEqLikeNameFor(x_46, x_48, x_51);
x_53 = l_Lean_Meta_mkEqLikeNameFor(x_50, x_2, x_51);
x_54 = l_Lean_Elab_WF_mkUnfoldEq___closed__2;
lean_inc(x_52);
x_55 = l_Lean_MessageData_ofName(x_52);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_57);
lean_ctor_set(x_8, 0, x_56);
lean_inc(x_53);
x_58 = l_Lean_MessageData_ofName(x_53);
lean_inc(x_58);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_8);
lean_ctor_set(x_59, 1, x_58);
x_60 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_61 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0), 13, 6);
lean_closure_set(x_61, 0, x_47);
lean_closure_set(x_61, 1, x_48);
lean_closure_set(x_61, 2, x_53);
lean_closure_set(x_61, 3, x_52);
lean_closure_set(x_61, 4, x_60);
lean_closure_set(x_61, 5, x_58);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
x_63 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__1), 3, 2);
lean_closure_set(x_63, 0, x_60);
lean_closure_set(x_63, 1, x_62);
x_64 = lean_box(0);
x_65 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_65, 0, x_64);
lean_closure_set(x_65, 1, x_49);
lean_closure_set(x_65, 2, x_61);
x_66 = l_Lean_Meta_mapErrorImp___redArg(x_65, x_63, x_3, x_4, x_5, x_6, x_45);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_73 = x_66;
} else {
 lean_dec_ref(x_66);
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
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_75 = lean_ctor_get(x_8, 0);
x_76 = lean_ctor_get(x_8, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_8);
x_77 = lean_st_ref_get(x_6, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_ctor_get(x_75, 0);
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_ctor_get(x_1, 1);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 3);
lean_inc(x_83);
x_84 = lean_ctor_get(x_1, 5);
lean_inc(x_84);
lean_dec(x_1);
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
lean_dec(x_78);
x_86 = l_Lean_Elab_WF_mkUnfoldEq___closed__0;
lean_inc(x_83);
x_87 = l_Lean_Meta_mkEqLikeNameFor(x_81, x_83, x_86);
x_88 = l_Lean_Meta_mkEqLikeNameFor(x_85, x_2, x_86);
x_89 = l_Lean_Elab_WF_mkUnfoldEq___closed__2;
lean_inc(x_87);
x_90 = l_Lean_MessageData_ofName(x_87);
if (lean_is_scalar(x_80)) {
 x_91 = lean_alloc_ctor(7, 2, 0);
} else {
 x_91 = x_80;
 lean_ctor_set_tag(x_91, 7);
}
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_inc(x_88);
x_94 = l_Lean_MessageData_ofName(x_88);
lean_inc(x_94);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_97 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0), 13, 6);
lean_closure_set(x_97, 0, x_82);
lean_closure_set(x_97, 1, x_83);
lean_closure_set(x_97, 2, x_88);
lean_closure_set(x_97, 3, x_87);
lean_closure_set(x_97, 4, x_96);
lean_closure_set(x_97, 5, x_94);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
x_99 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__1), 3, 2);
lean_closure_set(x_99, 0, x_96);
lean_closure_set(x_99, 1, x_98);
x_100 = lean_box(0);
x_101 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_101, 0, x_100);
lean_closure_set(x_101, 1, x_84);
lean_closure_set(x_101, 2, x_97);
x_102 = l_Lean_Meta_mapErrorImp___redArg(x_101, x_99, x_3, x_4, x_5, x_6, x_79);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_105 = x_102;
} else {
 lean_dec_ref(x_102);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_109 = x_102;
} else {
 lean_dec_ref(x_102);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
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
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4;
x_3 = lean_box(0);
x_4 = l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2544_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
return x_6;
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
