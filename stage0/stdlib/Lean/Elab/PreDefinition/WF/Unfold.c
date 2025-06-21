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
static lean_object* l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
lean_object* l_List_lengthTR___redArg(lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
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
static lean_object* l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
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
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__15;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
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
static lean_object* l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
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
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__6;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___closed__1;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__14;
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__0;
static lean_object* l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__28;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__3;
static lean_object* l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
static lean_object* l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
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
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__9;
extern lean_object* l_Lean_diagnostics;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__34;
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__19;
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_List_forM___at_____private_Lean_Elab_PreDefinition_Eqns_0__Lean_Elab_Eqns_mkEqnProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__7;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__12;
static lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___closed__1;
static lean_object* l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__41;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__20;
static lean_object* l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__39;
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
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__1;
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_object* l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__3;
lean_object* l_Lean_MessageData_ofName(lean_object*);
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
x_20 = l_Lean_Meta_mkLambdaFVars(x_4, x_14, x_17, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10);
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
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
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
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_67 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_63, x_64, x_62, x_66, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_71 = l_Lean_mkAppB(x_45, x_42, x_68);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_72 = l_Lean_Meta_mkEq(x_71, x_70, x_3, x_4, x_5, x_6, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_box(0);
lean_inc(x_3);
x_76 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_73, x_75, x_3, x_4, x_5, x_6, x_74);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__21;
x_80 = l_Lean_Expr_getAppFn(x_39);
x_81 = l_Lean_Expr_constLevels_x21(x_80);
lean_dec(x_80);
x_82 = l_Lean_Expr_const___override(x_79, x_81);
x_83 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__22;
x_84 = l_Lean_Expr_getAppNumArgs(x_39);
lean_inc(x_84);
x_85 = lean_mk_array(x_84, x_83);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_84, x_86);
lean_dec(x_84);
x_88 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_39, x_85, x_87);
x_89 = l_Lean_mkAppN(x_82, x_88);
lean_dec(x_88);
lean_inc(x_4);
lean_inc(x_77);
x_90 = l_Lean_Meta_mkEqTrans(x_89, x_77, x_3, x_4, x_5, x_6, x_78);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_91, x_4, x_92);
lean_dec(x_4);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_dec(x_95);
x_96 = l_Lean_Expr_mvarId_x21(x_77);
lean_dec(x_77);
lean_ctor_set(x_93, 0, x_96);
return x_93;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = l_Lean_Expr_mvarId_x21(x_77);
lean_dec(x_77);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_77);
lean_dec(x_4);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_90);
if (x_100 == 0)
{
return x_90;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_90, 0);
x_102 = lean_ctor_get(x_90, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_90);
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
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_72);
if (x_104 == 0)
{
return x_72;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_72, 0);
x_106 = lean_ctor_get(x_72, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_72);
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
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_67);
if (x_108 == 0)
{
return x_67;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_67, 0);
x_110 = lean_ctor_get(x_67, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_67);
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
x_112 = !lean_is_exclusive(x_58);
if (x_112 == 0)
{
return x_58;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_58, 0);
x_114 = lean_ctor_get(x_58, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_58);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
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
uint8_t x_116; 
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_29);
if (x_116 == 0)
{
return x_29;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_29, 0);
x_118 = lean_ctor_get(x_29, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_29);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_17);
if (x_120 == 0)
{
return x_17;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_17, 0);
x_122 = lean_ctor_get(x_17, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_17);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
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
lean_object* x_8; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint64_t x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_539; lean_object* x_540; uint8_t x_541; 
x_42 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4;
x_539 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_5, x_7);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_unbox(x_540);
lean_dec(x_540);
if (x_541 == 0)
{
lean_object* x_542; 
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
lean_dec(x_539);
x_500 = x_3;
x_501 = x_4;
x_502 = x_5;
x_503 = x_6;
x_504 = x_542;
goto block_538;
}
else
{
uint8_t x_543; 
x_543 = !lean_is_exclusive(x_539);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_544 = lean_ctor_get(x_539, 1);
x_545 = lean_ctor_get(x_539, 0);
lean_dec(x_545);
x_546 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43;
lean_inc(x_2);
x_547 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_547, 0, x_2);
lean_ctor_set_tag(x_539, 7);
lean_ctor_set(x_539, 1, x_547);
lean_ctor_set(x_539, 0, x_546);
x_548 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_549 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_549, 0, x_539);
lean_ctor_set(x_549, 1, x_548);
x_550 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_549, x_3, x_4, x_5, x_6, x_544);
x_551 = lean_ctor_get(x_550, 1);
lean_inc(x_551);
lean_dec(x_550);
x_500 = x_3;
x_501 = x_4;
x_502 = x_5;
x_503 = x_6;
x_504 = x_551;
goto block_538;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_552 = lean_ctor_get(x_539, 1);
lean_inc(x_552);
lean_dec(x_539);
x_553 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__43;
lean_inc(x_2);
x_554 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_554, 0, x_2);
x_555 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
x_556 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_557 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
x_558 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_557, x_3, x_4, x_5, x_6, x_552);
x_559 = lean_ctor_get(x_558, 1);
lean_inc(x_559);
lean_dec(x_558);
x_500 = x_3;
x_501 = x_4;
x_502 = x_5;
x_503 = x_6;
x_504 = x_559;
goto block_538;
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
block_499:
{
lean_object* x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_76, 0, x_44);
lean_ctor_set_uint8(x_76, 1, x_45);
lean_ctor_set_uint8(x_76, 2, x_46);
lean_ctor_set_uint8(x_76, 3, x_47);
lean_ctor_set_uint8(x_76, 4, x_48);
lean_ctor_set_uint8(x_76, 5, x_49);
lean_ctor_set_uint8(x_76, 6, x_50);
lean_ctor_set_uint8(x_76, 7, x_51);
lean_ctor_set_uint8(x_76, 8, x_52);
lean_ctor_set_uint8(x_76, 9, x_75);
lean_ctor_set_uint8(x_76, 10, x_53);
lean_ctor_set_uint8(x_76, 11, x_54);
lean_ctor_set_uint8(x_76, 12, x_55);
lean_ctor_set_uint8(x_76, 13, x_56);
lean_ctor_set_uint8(x_76, 14, x_57);
lean_ctor_set_uint8(x_76, 15, x_58);
lean_ctor_set_uint8(x_76, 16, x_59);
lean_ctor_set_uint8(x_76, 17, x_60);
x_77 = 2;
x_78 = lean_uint64_shift_right(x_61, x_77);
x_79 = lean_uint64_shift_left(x_78, x_77);
x_80 = l_Lean_Meta_TransparencyMode_toUInt64(x_75);
x_81 = lean_uint64_lor(x_79, x_80);
x_82 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_63);
lean_ctor_set(x_82, 2, x_64);
lean_ctor_set(x_82, 3, x_65);
lean_ctor_set(x_82, 4, x_66);
lean_ctor_set(x_82, 5, x_67);
lean_ctor_set(x_82, 6, x_68);
lean_ctor_set_uint64(x_82, sizeof(void*)*7, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*7 + 8, x_62);
lean_ctor_set_uint8(x_82, sizeof(void*)*7 + 9, x_69);
lean_ctor_set_uint8(x_82, sizeof(void*)*7 + 10, x_70);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_2);
x_83 = l_Lean_Elab_Eqns_tryURefl(x_2, x_82, x_74, x_71, x_73, x_72);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_87 = l_Lean_Elab_Eqns_tryContradiction(x_2, x_43, x_74, x_71, x_73, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_91 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_43, x_74, x_71, x_73, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_94 = l_Lean_Elab_Eqns_simpIf_x3f(x_2, x_43, x_74, x_71, x_73, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_box(1);
x_98 = lean_unsigned_to_nat(100000u);
x_99 = lean_unsigned_to_nat(2u);
x_100 = lean_box(2);
x_101 = lean_alloc_ctor(0, 2, 23);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
x_102 = lean_unbox(x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_102);
x_103 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 1, x_103);
x_104 = lean_unbox(x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 2, x_104);
x_105 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 3, x_105);
x_106 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 4, x_106);
x_107 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 5, x_107);
x_108 = lean_unbox(x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 6, x_108);
x_109 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 7, x_109);
x_110 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 8, x_110);
x_111 = lean_unbox(x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 9, x_111);
x_112 = lean_unbox(x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 10, x_112);
x_113 = lean_unbox(x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 11, x_113);
x_114 = lean_unbox(x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 12, x_114);
x_115 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 13, x_115);
x_116 = lean_unbox(x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 14, x_116);
x_117 = lean_unbox(x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 15, x_117);
x_118 = lean_unbox(x_88);
lean_dec(x_88);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 16, x_118);
x_119 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 17, x_119);
x_120 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 18, x_120);
x_121 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 19, x_121);
x_122 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 20, x_122);
x_123 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 21, x_123);
x_124 = lean_unbox(x_97);
lean_ctor_set_uint8(x_101, sizeof(void*)*2 + 22, x_124);
x_125 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__5;
x_126 = lean_unsigned_to_nat(0u);
x_127 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__13;
x_128 = l_Lean_Meta_Simp_mkContext___redArg(x_101, x_125, x_127, x_43, x_73, x_96);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_ctor_get(x_128, 1);
x_132 = lean_box(0);
x_133 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21;
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_134 = l_Lean_Meta_simpTargetStar(x_2, x_130, x_125, x_132, x_133, x_43, x_74, x_71, x_73, x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
lean_dec(x_138);
switch (lean_obj_tag(x_137)) {
case 0:
{
uint8_t x_139; 
lean_free_object(x_135);
lean_free_object(x_128);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_134);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_134, 0);
lean_dec(x_140);
x_141 = lean_box(0);
lean_ctor_set(x_134, 0, x_141);
return x_134;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_134, 1);
lean_inc(x_142);
lean_dec(x_134);
x_143 = lean_box(0);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
case 1:
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_134, 1);
lean_inc(x_145);
lean_dec(x_134);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_146 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_43, x_74, x_71, x_73, x_145);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; uint8_t x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = lean_unbox(x_97);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_150 = l_Lean_Meta_splitTarget_x3f(x_2, x_149, x_43, x_74, x_71, x_73, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
x_154 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_135, 7);
lean_ctor_set(x_135, 1, x_154);
lean_ctor_set(x_135, 0, x_153);
x_155 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_155);
lean_ctor_set(x_128, 0, x_135);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_2);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_128);
lean_ctor_set(x_157, 1, x_156);
x_158 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_159, x_43, x_74, x_71, x_73, x_152);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_74);
lean_dec(x_43);
return x_160;
}
else
{
lean_object* x_161; uint8_t x_162; 
lean_free_object(x_128);
lean_dec(x_2);
x_161 = lean_ctor_get(x_150, 1);
lean_inc(x_161);
lean_dec(x_150);
x_162 = !lean_is_exclusive(x_151);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_151, 0);
x_164 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_161);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_unbox(x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; 
lean_free_object(x_151);
lean_free_object(x_135);
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
lean_dec(x_164);
x_16 = x_163;
x_17 = x_43;
x_18 = x_74;
x_19 = x_71;
x_20 = x_73;
x_21 = x_167;
goto block_24;
}
else
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_164);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_169 = lean_ctor_get(x_164, 1);
x_170 = lean_ctor_get(x_164, 0);
lean_dec(x_170);
x_171 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_172 = l_List_lengthTR___redArg(x_163);
x_173 = l_Nat_reprFast(x_172);
lean_ctor_set_tag(x_151, 3);
lean_ctor_set(x_151, 0, x_173);
x_174 = l_Lean_MessageData_ofFormat(x_151);
lean_ctor_set_tag(x_164, 7);
lean_ctor_set(x_164, 1, x_174);
lean_ctor_set(x_164, 0, x_171);
x_175 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_135, 7);
lean_ctor_set(x_135, 1, x_175);
lean_ctor_set(x_135, 0, x_164);
x_176 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_135, x_43, x_74, x_71, x_73, x_169);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_16 = x_163;
x_17 = x_43;
x_18 = x_74;
x_19 = x_71;
x_20 = x_73;
x_21 = x_177;
goto block_24;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_164, 1);
lean_inc(x_178);
lean_dec(x_164);
x_179 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_180 = l_List_lengthTR___redArg(x_163);
x_181 = l_Nat_reprFast(x_180);
lean_ctor_set_tag(x_151, 3);
lean_ctor_set(x_151, 0, x_181);
x_182 = l_Lean_MessageData_ofFormat(x_151);
x_183 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_182);
x_184 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_135, 7);
lean_ctor_set(x_135, 1, x_184);
lean_ctor_set(x_135, 0, x_183);
x_185 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_135, x_43, x_74, x_71, x_73, x_178);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_16 = x_163;
x_17 = x_43;
x_18 = x_74;
x_19 = x_71;
x_20 = x_73;
x_21 = x_186;
goto block_24;
}
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_151, 0);
lean_inc(x_187);
lean_dec(x_151);
x_188 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_161);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; 
lean_free_object(x_135);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_16 = x_187;
x_17 = x_43;
x_18 = x_74;
x_19 = x_71;
x_20 = x_73;
x_21 = x_191;
goto block_24;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_192 = lean_ctor_get(x_188, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_193 = x_188;
} else {
 lean_dec_ref(x_188);
 x_193 = lean_box(0);
}
x_194 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_195 = l_List_lengthTR___redArg(x_187);
x_196 = l_Nat_reprFast(x_195);
x_197 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_197, 0, x_196);
x_198 = l_Lean_MessageData_ofFormat(x_197);
if (lean_is_scalar(x_193)) {
 x_199 = lean_alloc_ctor(7, 2, 0);
} else {
 x_199 = x_193;
 lean_ctor_set_tag(x_199, 7);
}
lean_ctor_set(x_199, 0, x_194);
lean_ctor_set(x_199, 1, x_198);
x_200 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_135, 7);
lean_ctor_set(x_135, 1, x_200);
lean_ctor_set(x_135, 0, x_199);
x_201 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_135, x_43, x_74, x_71, x_73, x_192);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_16 = x_187;
x_17 = x_43;
x_18 = x_74;
x_19 = x_71;
x_20 = x_73;
x_21 = x_202;
goto block_24;
}
}
}
}
else
{
uint8_t x_203; 
lean_free_object(x_135);
lean_free_object(x_128);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_150);
if (x_203 == 0)
{
return x_150;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_150, 0);
x_205 = lean_ctor_get(x_150, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_150);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
lean_object* x_207; uint8_t x_208; 
lean_free_object(x_128);
lean_dec(x_2);
x_207 = lean_ctor_get(x_146, 1);
lean_inc(x_207);
lean_dec(x_146);
x_208 = !lean_is_exclusive(x_147);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_209 = lean_ctor_get(x_147, 0);
x_210 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_207);
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_unbox(x_211);
lean_dec(x_211);
if (x_212 == 0)
{
lean_object* x_213; 
lean_free_object(x_147);
lean_free_object(x_135);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_25 = x_126;
x_26 = x_209;
x_27 = x_43;
x_28 = x_74;
x_29 = x_71;
x_30 = x_73;
x_31 = x_213;
goto block_41;
}
else
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_210);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_215 = lean_ctor_get(x_210, 1);
x_216 = lean_ctor_get(x_210, 0);
lean_dec(x_216);
x_217 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_218 = lean_array_get_size(x_209);
x_219 = l_Nat_reprFast(x_218);
lean_ctor_set_tag(x_147, 3);
lean_ctor_set(x_147, 0, x_219);
x_220 = l_Lean_MessageData_ofFormat(x_147);
lean_ctor_set_tag(x_210, 7);
lean_ctor_set(x_210, 1, x_220);
lean_ctor_set(x_210, 0, x_217);
x_221 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_135, 7);
lean_ctor_set(x_135, 1, x_221);
lean_ctor_set(x_135, 0, x_210);
x_222 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_135, x_43, x_74, x_71, x_73, x_215);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_25 = x_126;
x_26 = x_209;
x_27 = x_43;
x_28 = x_74;
x_29 = x_71;
x_30 = x_73;
x_31 = x_223;
goto block_41;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_224 = lean_ctor_get(x_210, 1);
lean_inc(x_224);
lean_dec(x_210);
x_225 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_226 = lean_array_get_size(x_209);
x_227 = l_Nat_reprFast(x_226);
lean_ctor_set_tag(x_147, 3);
lean_ctor_set(x_147, 0, x_227);
x_228 = l_Lean_MessageData_ofFormat(x_147);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_225);
lean_ctor_set(x_229, 1, x_228);
x_230 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_135, 7);
lean_ctor_set(x_135, 1, x_230);
lean_ctor_set(x_135, 0, x_229);
x_231 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_135, x_43, x_74, x_71, x_73, x_224);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
x_25 = x_126;
x_26 = x_209;
x_27 = x_43;
x_28 = x_74;
x_29 = x_71;
x_30 = x_73;
x_31 = x_232;
goto block_41;
}
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_233 = lean_ctor_get(x_147, 0);
lean_inc(x_233);
lean_dec(x_147);
x_234 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_207);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_unbox(x_235);
lean_dec(x_235);
if (x_236 == 0)
{
lean_object* x_237; 
lean_free_object(x_135);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_25 = x_126;
x_26 = x_233;
x_27 = x_43;
x_28 = x_74;
x_29 = x_71;
x_30 = x_73;
x_31 = x_237;
goto block_41;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_239 = x_234;
} else {
 lean_dec_ref(x_234);
 x_239 = lean_box(0);
}
x_240 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_241 = lean_array_get_size(x_233);
x_242 = l_Nat_reprFast(x_241);
x_243 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_243, 0, x_242);
x_244 = l_Lean_MessageData_ofFormat(x_243);
if (lean_is_scalar(x_239)) {
 x_245 = lean_alloc_ctor(7, 2, 0);
} else {
 x_245 = x_239;
 lean_ctor_set_tag(x_245, 7);
}
lean_ctor_set(x_245, 0, x_240);
lean_ctor_set(x_245, 1, x_244);
x_246 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
lean_ctor_set_tag(x_135, 7);
lean_ctor_set(x_135, 1, x_246);
lean_ctor_set(x_135, 0, x_245);
x_247 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_135, x_43, x_74, x_71, x_73, x_238);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_25 = x_126;
x_26 = x_233;
x_27 = x_43;
x_28 = x_74;
x_29 = x_71;
x_30 = x_73;
x_31 = x_248;
goto block_41;
}
}
}
}
else
{
uint8_t x_249; 
lean_free_object(x_135);
lean_free_object(x_128);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_146);
if (x_249 == 0)
{
return x_146;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_146, 0);
x_251 = lean_ctor_get(x_146, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_146);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
default: 
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
lean_free_object(x_135);
lean_free_object(x_128);
lean_dec(x_2);
x_253 = lean_ctor_get(x_134, 1);
lean_inc(x_253);
lean_dec(x_134);
x_254 = lean_ctor_get(x_137, 0);
lean_inc(x_254);
lean_dec(x_137);
x_255 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_253);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_unbox(x_256);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_255, 1);
lean_inc(x_258);
lean_dec(x_255);
x_2 = x_254;
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_258;
goto _start;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_260 = lean_ctor_get(x_255, 1);
lean_inc(x_260);
lean_dec(x_255);
x_261 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
x_262 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_261, x_43, x_74, x_71, x_73, x_260);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_2 = x_254;
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_263;
goto _start;
}
}
}
}
else
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_135, 0);
lean_inc(x_265);
lean_dec(x_135);
switch (lean_obj_tag(x_265)) {
case 0:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_free_object(x_128);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_266 = lean_ctor_get(x_134, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_267 = x_134;
} else {
 lean_dec_ref(x_134);
 x_267 = lean_box(0);
}
x_268 = lean_box(0);
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_266);
return x_269;
}
case 1:
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_134, 1);
lean_inc(x_270);
lean_dec(x_134);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_271 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_43, x_74, x_71, x_73, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; uint8_t x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = lean_unbox(x_97);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_275 = l_Lean_Meta_splitTarget_x3f(x_2, x_274, x_43, x_74, x_71, x_73, x_273);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
x_279 = l_Lean_MessageData_ofName(x_1);
x_280 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
lean_ctor_set_tag(x_128, 7);
lean_ctor_set(x_128, 1, x_281);
lean_ctor_set(x_128, 0, x_280);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_2);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_128);
lean_ctor_set(x_283, 1, x_282);
x_284 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_285 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
x_286 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_285, x_43, x_74, x_71, x_73, x_277);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_74);
lean_dec(x_43);
return x_286;
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
lean_free_object(x_128);
lean_dec(x_2);
x_287 = lean_ctor_get(x_275, 1);
lean_inc(x_287);
lean_dec(x_275);
x_288 = lean_ctor_get(x_276, 0);
lean_inc(x_288);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 x_289 = x_276;
} else {
 lean_dec_ref(x_276);
 x_289 = lean_box(0);
}
x_290 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_287);
x_291 = lean_ctor_get(x_290, 0);
lean_inc(x_291);
x_292 = lean_unbox(x_291);
lean_dec(x_291);
if (x_292 == 0)
{
lean_object* x_293; 
lean_dec(x_289);
x_293 = lean_ctor_get(x_290, 1);
lean_inc(x_293);
lean_dec(x_290);
x_16 = x_288;
x_17 = x_43;
x_18 = x_74;
x_19 = x_71;
x_20 = x_73;
x_21 = x_293;
goto block_24;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_294 = lean_ctor_get(x_290, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_295 = x_290;
} else {
 lean_dec_ref(x_290);
 x_295 = lean_box(0);
}
x_296 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_297 = l_List_lengthTR___redArg(x_288);
x_298 = l_Nat_reprFast(x_297);
if (lean_is_scalar(x_289)) {
 x_299 = lean_alloc_ctor(3, 1, 0);
} else {
 x_299 = x_289;
 lean_ctor_set_tag(x_299, 3);
}
lean_ctor_set(x_299, 0, x_298);
x_300 = l_Lean_MessageData_ofFormat(x_299);
if (lean_is_scalar(x_295)) {
 x_301 = lean_alloc_ctor(7, 2, 0);
} else {
 x_301 = x_295;
 lean_ctor_set_tag(x_301, 7);
}
lean_ctor_set(x_301, 0, x_296);
lean_ctor_set(x_301, 1, x_300);
x_302 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
x_303 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
x_304 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_303, x_43, x_74, x_71, x_73, x_294);
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
x_16 = x_288;
x_17 = x_43;
x_18 = x_74;
x_19 = x_71;
x_20 = x_73;
x_21 = x_305;
goto block_24;
}
}
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_free_object(x_128);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_306 = lean_ctor_get(x_275, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_275, 1);
lean_inc(x_307);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_308 = x_275;
} else {
 lean_dec_ref(x_275);
 x_308 = lean_box(0);
}
if (lean_is_scalar(x_308)) {
 x_309 = lean_alloc_ctor(1, 2, 0);
} else {
 x_309 = x_308;
}
lean_ctor_set(x_309, 0, x_306);
lean_ctor_set(x_309, 1, x_307);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
lean_free_object(x_128);
lean_dec(x_2);
x_310 = lean_ctor_get(x_271, 1);
lean_inc(x_310);
lean_dec(x_271);
x_311 = lean_ctor_get(x_272, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 x_312 = x_272;
} else {
 lean_dec_ref(x_272);
 x_312 = lean_box(0);
}
x_313 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_310);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_unbox(x_314);
lean_dec(x_314);
if (x_315 == 0)
{
lean_object* x_316; 
lean_dec(x_312);
x_316 = lean_ctor_get(x_313, 1);
lean_inc(x_316);
lean_dec(x_313);
x_25 = x_126;
x_26 = x_311;
x_27 = x_43;
x_28 = x_74;
x_29 = x_71;
x_30 = x_73;
x_31 = x_316;
goto block_41;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_317 = lean_ctor_get(x_313, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_318 = x_313;
} else {
 lean_dec_ref(x_313);
 x_318 = lean_box(0);
}
x_319 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_320 = lean_array_get_size(x_311);
x_321 = l_Nat_reprFast(x_320);
if (lean_is_scalar(x_312)) {
 x_322 = lean_alloc_ctor(3, 1, 0);
} else {
 x_322 = x_312;
 lean_ctor_set_tag(x_322, 3);
}
lean_ctor_set(x_322, 0, x_321);
x_323 = l_Lean_MessageData_ofFormat(x_322);
if (lean_is_scalar(x_318)) {
 x_324 = lean_alloc_ctor(7, 2, 0);
} else {
 x_324 = x_318;
 lean_ctor_set_tag(x_324, 7);
}
lean_ctor_set(x_324, 0, x_319);
lean_ctor_set(x_324, 1, x_323);
x_325 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
x_326 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
x_327 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_326, x_43, x_74, x_71, x_73, x_317);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
x_25 = x_126;
x_26 = x_311;
x_27 = x_43;
x_28 = x_74;
x_29 = x_71;
x_30 = x_73;
x_31 = x_328;
goto block_41;
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_free_object(x_128);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_329 = lean_ctor_get(x_271, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_271, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_331 = x_271;
} else {
 lean_dec_ref(x_271);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 2, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_329);
lean_ctor_set(x_332, 1, x_330);
return x_332;
}
}
default: 
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
lean_free_object(x_128);
lean_dec(x_2);
x_333 = lean_ctor_get(x_134, 1);
lean_inc(x_333);
lean_dec(x_134);
x_334 = lean_ctor_get(x_265, 0);
lean_inc(x_334);
lean_dec(x_265);
x_335 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_333);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_unbox(x_336);
lean_dec(x_336);
if (x_337 == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_335, 1);
lean_inc(x_338);
lean_dec(x_335);
x_2 = x_334;
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_338;
goto _start;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = lean_ctor_get(x_335, 1);
lean_inc(x_340);
lean_dec(x_335);
x_341 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
x_342 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_341, x_43, x_74, x_71, x_73, x_340);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
lean_dec(x_342);
x_2 = x_334;
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_343;
goto _start;
}
}
}
}
}
else
{
uint8_t x_345; 
lean_free_object(x_128);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_345 = !lean_is_exclusive(x_134);
if (x_345 == 0)
{
return x_134;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_134, 0);
x_347 = lean_ctor_get(x_134, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_134);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_128, 0);
x_350 = lean_ctor_get(x_128, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_128);
x_351 = lean_box(0);
x_352 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__21;
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_353 = l_Lean_Meta_simpTargetStar(x_2, x_349, x_125, x_351, x_352, x_43, x_74, x_71, x_73, x_350);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_356 = x_354;
} else {
 lean_dec_ref(x_354);
 x_356 = lean_box(0);
}
switch (lean_obj_tag(x_355)) {
case 0:
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_356);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_357 = lean_ctor_get(x_353, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_358 = x_353;
} else {
 lean_dec_ref(x_353);
 x_358 = lean_box(0);
}
x_359 = lean_box(0);
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(0, 2, 0);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_357);
return x_360;
}
case 1:
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_353, 1);
lean_inc(x_361);
lean_dec(x_353);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_362 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_43, x_74, x_71, x_73, x_361);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; uint8_t x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = lean_unbox(x_97);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_74);
lean_inc(x_43);
lean_inc(x_2);
x_366 = l_Lean_Meta_splitTarget_x3f(x_2, x_365, x_43, x_74, x_71, x_73, x_364);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__23;
x_370 = l_Lean_MessageData_ofName(x_1);
if (lean_is_scalar(x_356)) {
 x_371 = lean_alloc_ctor(7, 2, 0);
} else {
 x_371 = x_356;
 lean_ctor_set_tag(x_371, 7);
}
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_372 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__25;
x_373 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
x_374 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_374, 0, x_2);
x_375 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set(x_375, 1, x_374);
x_376 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2___closed__15;
x_377 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
x_378 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_377, x_43, x_74, x_71, x_73, x_368);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_74);
lean_dec(x_43);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
lean_dec(x_2);
x_379 = lean_ctor_get(x_366, 1);
lean_inc(x_379);
lean_dec(x_366);
x_380 = lean_ctor_get(x_367, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 x_381 = x_367;
} else {
 lean_dec_ref(x_367);
 x_381 = lean_box(0);
}
x_382 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_379);
x_383 = lean_ctor_get(x_382, 0);
lean_inc(x_383);
x_384 = lean_unbox(x_383);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; 
lean_dec(x_381);
lean_dec(x_356);
x_385 = lean_ctor_get(x_382, 1);
lean_inc(x_385);
lean_dec(x_382);
x_16 = x_380;
x_17 = x_43;
x_18 = x_74;
x_19 = x_71;
x_20 = x_73;
x_21 = x_385;
goto block_24;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_386 = lean_ctor_get(x_382, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_382)) {
 lean_ctor_release(x_382, 0);
 lean_ctor_release(x_382, 1);
 x_387 = x_382;
} else {
 lean_dec_ref(x_382);
 x_387 = lean_box(0);
}
x_388 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__27;
x_389 = l_List_lengthTR___redArg(x_380);
x_390 = l_Nat_reprFast(x_389);
if (lean_is_scalar(x_381)) {
 x_391 = lean_alloc_ctor(3, 1, 0);
} else {
 x_391 = x_381;
 lean_ctor_set_tag(x_391, 3);
}
lean_ctor_set(x_391, 0, x_390);
x_392 = l_Lean_MessageData_ofFormat(x_391);
if (lean_is_scalar(x_387)) {
 x_393 = lean_alloc_ctor(7, 2, 0);
} else {
 x_393 = x_387;
 lean_ctor_set_tag(x_393, 7);
}
lean_ctor_set(x_393, 0, x_388);
lean_ctor_set(x_393, 1, x_392);
x_394 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
if (lean_is_scalar(x_356)) {
 x_395 = lean_alloc_ctor(7, 2, 0);
} else {
 x_395 = x_356;
 lean_ctor_set_tag(x_395, 7);
}
lean_ctor_set(x_395, 0, x_393);
lean_ctor_set(x_395, 1, x_394);
x_396 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_395, x_43, x_74, x_71, x_73, x_386);
x_397 = lean_ctor_get(x_396, 1);
lean_inc(x_397);
lean_dec(x_396);
x_16 = x_380;
x_17 = x_43;
x_18 = x_74;
x_19 = x_71;
x_20 = x_73;
x_21 = x_397;
goto block_24;
}
}
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
lean_dec(x_356);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_398 = lean_ctor_get(x_366, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_366, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_400 = x_366;
} else {
 lean_dec_ref(x_366);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_398);
lean_ctor_set(x_401, 1, x_399);
return x_401;
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; 
lean_dec(x_2);
x_402 = lean_ctor_get(x_362, 1);
lean_inc(x_402);
lean_dec(x_362);
x_403 = lean_ctor_get(x_363, 0);
lean_inc(x_403);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_404 = x_363;
} else {
 lean_dec_ref(x_363);
 x_404 = lean_box(0);
}
x_405 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_402);
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_unbox(x_406);
lean_dec(x_406);
if (x_407 == 0)
{
lean_object* x_408; 
lean_dec(x_404);
lean_dec(x_356);
x_408 = lean_ctor_get(x_405, 1);
lean_inc(x_408);
lean_dec(x_405);
x_25 = x_126;
x_26 = x_403;
x_27 = x_43;
x_28 = x_74;
x_29 = x_71;
x_30 = x_73;
x_31 = x_408;
goto block_41;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_409 = lean_ctor_get(x_405, 1);
lean_inc(x_409);
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 lean_ctor_release(x_405, 1);
 x_410 = x_405;
} else {
 lean_dec_ref(x_405);
 x_410 = lean_box(0);
}
x_411 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__31;
x_412 = lean_array_get_size(x_403);
x_413 = l_Nat_reprFast(x_412);
if (lean_is_scalar(x_404)) {
 x_414 = lean_alloc_ctor(3, 1, 0);
} else {
 x_414 = x_404;
 lean_ctor_set_tag(x_414, 3);
}
lean_ctor_set(x_414, 0, x_413);
x_415 = l_Lean_MessageData_ofFormat(x_414);
if (lean_is_scalar(x_410)) {
 x_416 = lean_alloc_ctor(7, 2, 0);
} else {
 x_416 = x_410;
 lean_ctor_set_tag(x_416, 7);
}
lean_ctor_set(x_416, 0, x_411);
lean_ctor_set(x_416, 1, x_415);
x_417 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__29;
if (lean_is_scalar(x_356)) {
 x_418 = lean_alloc_ctor(7, 2, 0);
} else {
 x_418 = x_356;
 lean_ctor_set_tag(x_418, 7);
}
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
x_419 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_418, x_43, x_74, x_71, x_73, x_409);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_25 = x_126;
x_26 = x_403;
x_27 = x_43;
x_28 = x_74;
x_29 = x_71;
x_30 = x_73;
x_31 = x_420;
goto block_41;
}
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
lean_dec(x_356);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_421 = lean_ctor_get(x_362, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_362, 1);
lean_inc(x_422);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_423 = x_362;
} else {
 lean_dec_ref(x_362);
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
default: 
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
lean_dec(x_356);
lean_dec(x_2);
x_425 = lean_ctor_get(x_353, 1);
lean_inc(x_425);
lean_dec(x_353);
x_426 = lean_ctor_get(x_355, 0);
lean_inc(x_426);
lean_dec(x_355);
x_427 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_425);
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
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_430;
goto _start;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_432 = lean_ctor_get(x_427, 1);
lean_inc(x_432);
lean_dec(x_427);
x_433 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__33;
x_434 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_433, x_43, x_74, x_71, x_73, x_432);
x_435 = lean_ctor_get(x_434, 1);
lean_inc(x_435);
lean_dec(x_434);
x_2 = x_426;
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_435;
goto _start;
}
}
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_437 = lean_ctor_get(x_353, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_353, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_439 = x_353;
} else {
 lean_dec_ref(x_353);
 x_439 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_440 = lean_alloc_ctor(1, 2, 0);
} else {
 x_440 = x_439;
}
lean_ctor_set(x_440, 0, x_437);
lean_ctor_set(x_440, 1, x_438);
return x_440;
}
}
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; 
lean_dec(x_88);
lean_dec(x_2);
x_441 = lean_ctor_get(x_94, 1);
lean_inc(x_441);
lean_dec(x_94);
x_442 = lean_ctor_get(x_95, 0);
lean_inc(x_442);
lean_dec(x_95);
x_443 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_441);
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
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_446;
goto _start;
}
else
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_ctor_get(x_443, 1);
lean_inc(x_448);
lean_dec(x_443);
x_449 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__35;
x_450 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_449, x_43, x_74, x_71, x_73, x_448);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
lean_dec(x_450);
x_2 = x_442;
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_451;
goto _start;
}
}
}
else
{
uint8_t x_453; 
lean_dec(x_88);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_453 = !lean_is_exclusive(x_94);
if (x_453 == 0)
{
return x_94;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_94, 0);
x_455 = lean_ctor_get(x_94, 1);
lean_inc(x_455);
lean_inc(x_454);
lean_dec(x_94);
x_456 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
return x_456;
}
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; 
lean_dec(x_88);
lean_dec(x_2);
x_457 = lean_ctor_get(x_91, 1);
lean_inc(x_457);
lean_dec(x_91);
x_458 = lean_ctor_get(x_92, 0);
lean_inc(x_458);
lean_dec(x_92);
x_459 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_457);
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_unbox(x_460);
lean_dec(x_460);
if (x_461 == 0)
{
lean_object* x_462; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
lean_dec(x_459);
x_2 = x_458;
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_462;
goto _start;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_464 = lean_ctor_get(x_459, 1);
lean_inc(x_464);
lean_dec(x_459);
x_465 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__37;
x_466 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_465, x_43, x_74, x_71, x_73, x_464);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
lean_dec(x_466);
x_2 = x_458;
x_3 = x_43;
x_4 = x_74;
x_5 = x_71;
x_6 = x_73;
x_7 = x_467;
goto _start;
}
}
}
else
{
uint8_t x_469; 
lean_dec(x_88);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_469 = !lean_is_exclusive(x_91);
if (x_469 == 0)
{
return x_91;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_91, 0);
x_471 = lean_ctor_get(x_91, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_91);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
return x_472;
}
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
lean_dec(x_88);
lean_dec(x_2);
lean_dec(x_1);
x_473 = lean_ctor_get(x_87, 1);
lean_inc(x_473);
lean_dec(x_87);
x_474 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_473);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_unbox(x_475);
lean_dec(x_475);
if (x_476 == 0)
{
lean_object* x_477; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
x_477 = lean_ctor_get(x_474, 1);
lean_inc(x_477);
lean_dec(x_474);
x_8 = x_477;
goto block_11;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_478 = lean_ctor_get(x_474, 1);
lean_inc(x_478);
lean_dec(x_474);
x_479 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__39;
x_480 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_479, x_43, x_74, x_71, x_73, x_478);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_74);
lean_dec(x_43);
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
lean_dec(x_480);
x_8 = x_481;
goto block_11;
}
}
}
else
{
uint8_t x_482; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_482 = !lean_is_exclusive(x_87);
if (x_482 == 0)
{
return x_87;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_87, 0);
x_484 = lean_ctor_get(x_87, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_87);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; uint8_t x_489; 
lean_dec(x_2);
lean_dec(x_1);
x_486 = lean_ctor_get(x_83, 1);
lean_inc(x_486);
lean_dec(x_83);
x_487 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_42, x_71, x_486);
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
x_489 = lean_unbox(x_488);
lean_dec(x_488);
if (x_489 == 0)
{
lean_object* x_490; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
lean_dec(x_487);
x_12 = x_490;
goto block_15;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_491 = lean_ctor_get(x_487, 1);
lean_inc(x_491);
lean_dec(x_487);
x_492 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__41;
x_493 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_42, x_492, x_43, x_74, x_71, x_73, x_491);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_74);
lean_dec(x_43);
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec(x_493);
x_12 = x_494;
goto block_15;
}
}
}
else
{
uint8_t x_495; 
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_2);
lean_dec(x_1);
x_495 = !lean_is_exclusive(x_83);
if (x_495 == 0)
{
return x_83;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_83, 0);
x_497 = lean_ctor_get(x_83, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_83);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
}
block_538:
{
lean_object* x_505; uint64_t x_506; uint8_t x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; uint8_t x_514; uint8_t x_515; uint8_t x_516; uint8_t x_517; uint8_t x_518; uint8_t x_519; uint8_t x_520; uint8_t x_521; uint8_t x_522; uint8_t x_523; uint8_t x_524; uint8_t x_525; uint8_t x_526; uint8_t x_527; uint8_t x_528; uint8_t x_529; uint8_t x_530; uint8_t x_531; uint8_t x_532; uint8_t x_533; lean_object* x_534; uint8_t x_535; uint8_t x_536; 
x_505 = lean_ctor_get(x_500, 0);
lean_inc(x_505);
x_506 = lean_ctor_get_uint64(x_500, sizeof(void*)*7);
x_507 = lean_ctor_get_uint8(x_500, sizeof(void*)*7 + 8);
x_508 = lean_ctor_get(x_500, 1);
lean_inc(x_508);
x_509 = lean_ctor_get(x_500, 2);
lean_inc(x_509);
x_510 = lean_ctor_get(x_500, 3);
lean_inc(x_510);
x_511 = lean_ctor_get(x_500, 4);
lean_inc(x_511);
x_512 = lean_ctor_get(x_500, 5);
lean_inc(x_512);
x_513 = lean_ctor_get(x_500, 6);
lean_inc(x_513);
x_514 = lean_ctor_get_uint8(x_500, sizeof(void*)*7 + 9);
x_515 = lean_ctor_get_uint8(x_500, sizeof(void*)*7 + 10);
x_516 = lean_ctor_get_uint8(x_505, 0);
x_517 = lean_ctor_get_uint8(x_505, 1);
x_518 = lean_ctor_get_uint8(x_505, 2);
x_519 = lean_ctor_get_uint8(x_505, 3);
x_520 = lean_ctor_get_uint8(x_505, 4);
x_521 = lean_ctor_get_uint8(x_505, 5);
x_522 = lean_ctor_get_uint8(x_505, 6);
x_523 = lean_ctor_get_uint8(x_505, 7);
x_524 = lean_ctor_get_uint8(x_505, 8);
x_525 = lean_ctor_get_uint8(x_505, 9);
x_526 = lean_ctor_get_uint8(x_505, 10);
x_527 = lean_ctor_get_uint8(x_505, 11);
x_528 = lean_ctor_get_uint8(x_505, 12);
x_529 = lean_ctor_get_uint8(x_505, 13);
x_530 = lean_ctor_get_uint8(x_505, 14);
x_531 = lean_ctor_get_uint8(x_505, 15);
x_532 = lean_ctor_get_uint8(x_505, 16);
x_533 = lean_ctor_get_uint8(x_505, 17);
lean_dec(x_505);
x_534 = lean_box(0);
x_535 = lean_unbox(x_534);
x_536 = l_Lean_Meta_TransparencyMode_lt(x_525, x_535);
if (x_536 == 0)
{
x_43 = x_500;
x_44 = x_516;
x_45 = x_517;
x_46 = x_518;
x_47 = x_519;
x_48 = x_520;
x_49 = x_521;
x_50 = x_522;
x_51 = x_523;
x_52 = x_524;
x_53 = x_526;
x_54 = x_527;
x_55 = x_528;
x_56 = x_529;
x_57 = x_530;
x_58 = x_531;
x_59 = x_532;
x_60 = x_533;
x_61 = x_506;
x_62 = x_507;
x_63 = x_508;
x_64 = x_509;
x_65 = x_510;
x_66 = x_511;
x_67 = x_512;
x_68 = x_513;
x_69 = x_514;
x_70 = x_515;
x_71 = x_502;
x_72 = x_504;
x_73 = x_503;
x_74 = x_501;
x_75 = x_525;
goto block_499;
}
else
{
uint8_t x_537; 
x_537 = lean_unbox(x_534);
x_43 = x_500;
x_44 = x_516;
x_45 = x_517;
x_46 = x_518;
x_47 = x_519;
x_48 = x_520;
x_49 = x_521;
x_50 = x_522;
x_51 = x_523;
x_52 = x_524;
x_53 = x_526;
x_54 = x_527;
x_55 = x_528;
x_56 = x_529;
x_57 = x_530;
x_58 = x_531;
x_59 = x_532;
x_60 = x_533;
x_61 = x_506;
x_62 = x_507;
x_63 = x_508;
x_64 = x_509;
x_65 = x_510;
x_66 = x_511;
x_67 = x_512;
x_68 = x_513;
x_69 = x_514;
x_70 = x_515;
x_71 = x_502;
x_72 = x_504;
x_73 = x_503;
x_74 = x_501;
x_75 = x_537;
goto block_499;
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_186; uint8_t x_187; lean_object* x_188; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_appFn_x21(x_19);
x_29 = lean_box(0);
x_30 = lean_box(1);
x_186 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_186, 0, x_28);
lean_ctor_set(x_186, 1, x_29);
x_187 = lean_unbox(x_30);
lean_ctor_set_uint8(x_186, sizeof(void*)*2, x_187);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_188 = l_Lean_Meta_Simp_mkCongr(x_186, x_26, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Expr_mvarId_x21(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_192 = l_Lean_Meta_applySimpResultToTarget(x_191, x_19, x_189, x_9, x_10, x_11, x_12, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_name_eq(x_2, x_6);
if (x_195 == 0)
{
lean_object* x_196; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_196 = l_Lean_Elab_Eqns_deltaLHS(x_193, x_9, x_10, x_11, x_12, x_194);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_31 = x_197;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
x_36 = x_198;
goto block_185;
}
else
{
uint8_t x_199; 
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
x_199 = !lean_is_exclusive(x_196);
if (x_199 == 0)
{
return x_196;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_196, 0);
x_201 = lean_ctor_get(x_196, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_196);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
x_31 = x_193;
x_32 = x_9;
x_33 = x_10;
x_34 = x_11;
x_35 = x_12;
x_36 = x_194;
goto block_185;
}
}
else
{
uint8_t x_203; 
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
x_203 = !lean_is_exclusive(x_192);
if (x_203 == 0)
{
return x_192;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_192, 0);
x_205 = lean_ctor_get(x_192, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_192);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
else
{
uint8_t x_207; 
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
x_207 = !lean_is_exclusive(x_188);
if (x_207 == 0)
{
return x_188;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_188, 0);
x_209 = lean_ctor_get(x_188, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_188);
x_210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
block_185:
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
x_42 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_23, x_33, x_41);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_box(0);
x_47 = lean_box(1);
x_48 = lean_unbox(x_46);
x_49 = lean_unbox(x_30);
x_50 = lean_unbox(x_47);
lean_inc(x_7);
x_51 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_48, x_49, x_50, x_32, x_33, x_34, x_35, x_45);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unbox(x_46);
x_55 = lean_unbox(x_30);
x_56 = lean_unbox(x_46);
x_57 = lean_unbox(x_47);
x_58 = l_Lean_Meta_mkLambdaFVars(x_7, x_44, x_54, x_55, x_56, x_57, x_32, x_33, x_34, x_35, x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_4);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_4);
lean_ctor_set(x_61, 1, x_1);
lean_ctor_set(x_61, 2, x_52);
x_62 = lean_box(0);
lean_inc(x_4);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_62);
lean_ctor_set(x_42, 0, x_4);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_42);
x_64 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_64, 0, x_63);
lean_inc(x_35);
lean_inc(x_34);
x_65 = l_Lean_addDecl(x_64, x_34, x_35, x_60);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_65, 1);
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_4);
x_69 = l_Lean_inferDefEqAttr(x_4, x_32, x_33, x_34, x_35, x_67);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_71 = lean_ctor_get(x_69, 1);
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_74 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_73, x_34, x_71);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
uint8_t x_77; 
lean_free_object(x_69);
lean_free_object(x_65);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_74, 0);
lean_dec(x_78);
x_79 = lean_box(0);
lean_ctor_set(x_74, 0, x_79);
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_dec(x_74);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_dec(x_74);
x_84 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_85 = lean_unbox(x_46);
x_86 = l_Lean_MessageData_ofConstName(x_4, x_85);
lean_ctor_set_tag(x_69, 7);
lean_ctor_set(x_69, 1, x_86);
lean_ctor_set(x_69, 0, x_84);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_5);
lean_ctor_set(x_65, 0, x_69);
x_87 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_73, x_65, x_32, x_33, x_34, x_35, x_83);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_69, 1);
lean_inc(x_88);
lean_dec(x_69);
x_89 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_90 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_89, x_34, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_unbox(x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_65);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
x_95 = lean_box(0);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
lean_dec(x_90);
x_98 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_99 = lean_unbox(x_46);
x_100 = l_Lean_MessageData_ofConstName(x_4, x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set_tag(x_65, 7);
lean_ctor_set(x_65, 1, x_5);
lean_ctor_set(x_65, 0, x_101);
x_102 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_89, x_65, x_32, x_33, x_34, x_35, x_97);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_102;
}
}
}
else
{
lean_free_object(x_65);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_69;
}
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_65, 1);
lean_inc(x_103);
lean_dec(x_65);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_4);
x_104 = l_Lean_inferDefEqAttr(x_4, x_32, x_33, x_34, x_35, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
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
x_107 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_108 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_107, x_34, x_105);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_106);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_112 = x_108;
} else {
 lean_dec_ref(x_108);
 x_112 = lean_box(0);
}
x_113 = lean_box(0);
if (lean_is_scalar(x_112)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_112;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_111);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = lean_ctor_get(x_108, 1);
lean_inc(x_115);
lean_dec(x_108);
x_116 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_117 = lean_unbox(x_46);
x_118 = l_Lean_MessageData_ofConstName(x_4, x_117);
if (lean_is_scalar(x_106)) {
 x_119 = lean_alloc_ctor(7, 2, 0);
} else {
 x_119 = x_106;
 lean_ctor_set_tag(x_119, 7);
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_5);
x_121 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_107, x_120, x_32, x_33, x_34, x_35, x_115);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_121;
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
return x_104;
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
return x_65;
}
}
else
{
uint8_t x_122; 
lean_dec(x_52);
lean_free_object(x_42);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_58);
if (x_122 == 0)
{
return x_58;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_58, 0);
x_124 = lean_ctor_get(x_58, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_58);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
uint8_t x_126; 
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
x_126 = !lean_is_exclusive(x_51);
if (x_126 == 0)
{
return x_51;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_51, 0);
x_128 = lean_ctor_get(x_51, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_51);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; lean_object* x_137; 
x_130 = lean_ctor_get(x_42, 0);
x_131 = lean_ctor_get(x_42, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_42);
x_132 = lean_box(0);
x_133 = lean_box(1);
x_134 = lean_unbox(x_132);
x_135 = lean_unbox(x_30);
x_136 = lean_unbox(x_133);
lean_inc(x_7);
x_137 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_134, x_135, x_136, x_32, x_33, x_34, x_35, x_131);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; lean_object* x_144; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_unbox(x_132);
x_141 = lean_unbox(x_30);
x_142 = lean_unbox(x_132);
x_143 = lean_unbox(x_133);
x_144 = l_Lean_Meta_mkLambdaFVars(x_7, x_130, x_140, x_141, x_142, x_143, x_32, x_33, x_34, x_35, x_139);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
lean_inc(x_4);
x_147 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_147, 0, x_4);
lean_ctor_set(x_147, 1, x_1);
lean_ctor_set(x_147, 2, x_138);
x_148 = lean_box(0);
lean_inc(x_4);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_4);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_145);
lean_ctor_set(x_150, 2, x_149);
x_151 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_151, 0, x_150);
lean_inc(x_35);
lean_inc(x_34);
x_152 = l_Lean_addDecl(x_151, x_34, x_35, x_146);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_154 = x_152;
} else {
 lean_dec_ref(x_152);
 x_154 = lean_box(0);
}
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_4);
x_155 = l_Lean_inferDefEqAttr(x_4, x_32, x_33, x_34, x_35, x_153);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_159 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_158, x_34, x_156);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_unbox(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
x_162 = lean_ctor_get(x_159, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_163 = x_159;
} else {
 lean_dec_ref(x_159);
 x_163 = lean_box(0);
}
x_164 = lean_box(0);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(0, 2, 0);
} else {
 x_165 = x_163;
}
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_162);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_dec(x_159);
x_167 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__2;
x_168 = lean_unbox(x_132);
x_169 = l_Lean_MessageData_ofConstName(x_4, x_168);
if (lean_is_scalar(x_157)) {
 x_170 = lean_alloc_ctor(7, 2, 0);
} else {
 x_170 = x_157;
 lean_ctor_set_tag(x_170, 7);
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_169);
if (lean_is_scalar(x_154)) {
 x_171 = lean_alloc_ctor(7, 2, 0);
} else {
 x_171 = x_154;
 lean_ctor_set_tag(x_171, 7);
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_5);
x_172 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_158, x_171, x_32, x_33, x_34, x_35, x_166);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_172;
}
}
else
{
lean_dec(x_154);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
return x_155;
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
return x_152;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_138);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_173 = lean_ctor_get(x_144, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_144, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_175 = x_144;
} else {
 lean_dec_ref(x_144);
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
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_130);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_177 = lean_ctor_get(x_137, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_137, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_179 = x_137;
} else {
 lean_dec_ref(x_137);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
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
uint8_t x_181; 
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
x_181 = !lean_is_exclusive(x_37);
if (x_181 == 0)
{
return x_37;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_37, 0);
x_183 = lean_ctor_get(x_37, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_37);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
else
{
uint8_t x_211; 
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
x_211 = !lean_is_exclusive(x_25);
if (x_211 == 0)
{
return x_25;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_25, 0);
x_213 = lean_ctor_get(x_25, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_25);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
uint8_t x_215; 
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
x_215 = !lean_is_exclusive(x_18);
if (x_215 == 0)
{
return x_18;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_18, 0);
x_217 = lean_ctor_get(x_18, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_18);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
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
x_45 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_24, x_10, x_35);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
x_49 = lean_box(1);
x_50 = lean_unbox(x_31);
x_51 = lean_unbox(x_30);
x_52 = lean_unbox(x_49);
lean_inc(x_7);
x_53 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_50, x_51, x_52, x_9, x_10, x_11, x_12, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_31);
x_57 = lean_unbox(x_30);
x_58 = lean_unbox(x_31);
x_59 = lean_unbox(x_49);
x_60 = l_Lean_Meta_mkLambdaFVars(x_7, x_47, x_56, x_57, x_58, x_59, x_9, x_10, x_11, x_12, x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_4);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_1);
lean_ctor_set(x_63, 2, x_54);
x_64 = lean_box(0);
lean_inc(x_4);
lean_ctor_set_tag(x_45, 1);
lean_ctor_set(x_45, 1, x_64);
lean_ctor_set(x_45, 0, x_4);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_45);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_inc(x_12);
lean_inc(x_11);
x_67 = l_Lean_addDecl(x_66, x_11, x_12, x_62);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 1);
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_71 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_69);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_71, 1);
x_74 = lean_ctor_get(x_71, 0);
lean_dec(x_74);
x_75 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_76 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_75, x_11, x_73);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
uint8_t x_79; 
lean_free_object(x_71);
lean_free_object(x_67);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_79 = !lean_is_exclusive(x_76);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_76, 0);
lean_dec(x_80);
x_81 = lean_box(0);
lean_ctor_set(x_76, 0, x_81);
return x_76;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_dec(x_76);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_76, 1);
lean_inc(x_85);
lean_dec(x_76);
x_86 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_87 = lean_unbox(x_31);
x_88 = l_Lean_MessageData_ofConstName(x_4, x_87);
lean_ctor_set_tag(x_71, 7);
lean_ctor_set(x_71, 1, x_88);
lean_ctor_set(x_71, 0, x_86);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_5);
lean_ctor_set(x_67, 0, x_71);
x_89 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_75, x_67, x_9, x_10, x_11, x_12, x_85);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_71, 1);
lean_inc(x_90);
lean_dec(x_71);
x_91 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_92 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_91, x_11, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_free_object(x_67);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_96 = x_92;
} else {
 lean_dec_ref(x_92);
 x_96 = lean_box(0);
}
x_97 = lean_box(0);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_dec(x_92);
x_100 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_101 = lean_unbox(x_31);
x_102 = l_Lean_MessageData_ofConstName(x_4, x_101);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_5);
lean_ctor_set(x_67, 0, x_103);
x_104 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_91, x_67, x_9, x_10, x_11, x_12, x_99);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_104;
}
}
}
else
{
lean_free_object(x_67);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_71;
}
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_67, 1);
lean_inc(x_105);
lean_dec(x_67);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_106 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
x_109 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_110 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_109, x_11, x_107);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_108);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_114 = x_110;
} else {
 lean_dec_ref(x_110);
 x_114 = lean_box(0);
}
x_115 = lean_box(0);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
x_118 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_119 = lean_unbox(x_31);
x_120 = l_Lean_MessageData_ofConstName(x_4, x_119);
if (lean_is_scalar(x_108)) {
 x_121 = lean_alloc_ctor(7, 2, 0);
} else {
 x_121 = x_108;
 lean_ctor_set_tag(x_121, 7);
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_5);
x_123 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_109, x_122, x_9, x_10, x_11, x_12, x_117);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_123;
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
return x_106;
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
return x_67;
}
}
else
{
uint8_t x_124; 
lean_dec(x_54);
lean_free_object(x_45);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_60);
if (x_124 == 0)
{
return x_60;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_60, 0);
x_126 = lean_ctor_get(x_60, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_60);
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
x_128 = !lean_is_exclusive(x_53);
if (x_128 == 0)
{
return x_53;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_53, 0);
x_130 = lean_ctor_get(x_53, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_53);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; 
x_132 = lean_ctor_get(x_45, 0);
x_133 = lean_ctor_get(x_45, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_45);
x_134 = lean_box(1);
x_135 = lean_unbox(x_31);
x_136 = lean_unbox(x_30);
x_137 = lean_unbox(x_134);
lean_inc(x_7);
x_138 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_135, x_136, x_137, x_9, x_10, x_11, x_12, x_133);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; uint8_t x_142; uint8_t x_143; uint8_t x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_unbox(x_31);
x_142 = lean_unbox(x_30);
x_143 = lean_unbox(x_31);
x_144 = lean_unbox(x_134);
x_145 = l_Lean_Meta_mkLambdaFVars(x_7, x_132, x_141, x_142, x_143, x_144, x_9, x_10, x_11, x_12, x_140);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
lean_inc(x_4);
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_4);
lean_ctor_set(x_148, 1, x_1);
lean_ctor_set(x_148, 2, x_139);
x_149 = lean_box(0);
lean_inc(x_4);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_4);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_150);
x_152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_152, 0, x_151);
lean_inc(x_12);
lean_inc(x_11);
x_153 = l_Lean_addDecl(x_152, x_11, x_12, x_147);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_156 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_154);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_160 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_159, x_11, x_157);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_158);
lean_dec(x_155);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_164 = x_160;
} else {
 lean_dec_ref(x_160);
 x_164 = lean_box(0);
}
x_165 = lean_box(0);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_160, 1);
lean_inc(x_167);
lean_dec(x_160);
x_168 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_169 = lean_unbox(x_31);
x_170 = l_Lean_MessageData_ofConstName(x_4, x_169);
if (lean_is_scalar(x_158)) {
 x_171 = lean_alloc_ctor(7, 2, 0);
} else {
 x_171 = x_158;
 lean_ctor_set_tag(x_171, 7);
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_170);
if (lean_is_scalar(x_155)) {
 x_172 = lean_alloc_ctor(7, 2, 0);
} else {
 x_172 = x_155;
 lean_ctor_set_tag(x_172, 7);
}
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_5);
x_173 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_159, x_172, x_9, x_10, x_11, x_12, x_167);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_173;
}
}
else
{
lean_dec(x_155);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_156;
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
return x_153;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_139);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_174 = lean_ctor_get(x_145, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_145, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_176 = x_145;
} else {
 lean_dec_ref(x_145);
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
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_132);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_178 = lean_ctor_get(x_138, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_138, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_180 = x_138;
} else {
 lean_dec_ref(x_138);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
}
else
{
uint8_t x_182; 
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
x_182 = !lean_is_exclusive(x_33);
if (x_182 == 0)
{
return x_33;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_33, 0);
x_184 = lean_ctor_get(x_33, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_33);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
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
x_186 = !lean_is_exclusive(x_27);
if (x_186 == 0)
{
return x_27;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_27, 0);
x_188 = lean_ctor_get(x_27, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_27);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_22, 0);
x_191 = lean_ctor_get(x_22, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_22);
x_192 = l_Lean_Expr_mvarId_x21(x_190);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_193 = l_Lean_Elab_Eqns_deltaLHS(x_192, x_9, x_10, x_11, x_12, x_191);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_box(1);
x_197 = lean_box(0);
x_198 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_194);
x_199 = l_Lean_MVarId_applyConst(x_194, x_3, x_198, x_9, x_10, x_11, x_12, x_195);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l_List_isEmpty___redArg(x_200);
lean_dec(x_200);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_190);
lean_dec(x_19);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_203 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__2;
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_6);
x_205 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__4;
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_194);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__6;
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_210, x_9, x_10, x_11, x_12, x_201);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; uint8_t x_218; uint8_t x_219; lean_object* x_220; 
lean_dec(x_194);
lean_dec(x_6);
x_212 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_190, x_10, x_201);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
x_216 = lean_box(1);
x_217 = lean_unbox(x_197);
x_218 = lean_unbox(x_196);
x_219 = lean_unbox(x_216);
lean_inc(x_7);
x_220 = l_Lean_Meta_mkForallFVars(x_7, x_19, x_217, x_218, x_219, x_9, x_10, x_11, x_12, x_214);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; lean_object* x_227; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_unbox(x_197);
x_224 = lean_unbox(x_196);
x_225 = lean_unbox(x_197);
x_226 = lean_unbox(x_216);
x_227 = l_Lean_Meta_mkLambdaFVars(x_7, x_213, x_223, x_224, x_225, x_226, x_9, x_10, x_11, x_12, x_222);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
lean_inc(x_4);
x_230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_230, 0, x_4);
lean_ctor_set(x_230, 1, x_1);
lean_ctor_set(x_230, 2, x_221);
x_231 = lean_box(0);
lean_inc(x_4);
if (lean_is_scalar(x_215)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_215;
 lean_ctor_set_tag(x_232, 1);
}
lean_ctor_set(x_232, 0, x_4);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_228);
lean_ctor_set(x_233, 2, x_232);
x_234 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_234, 0, x_233);
lean_inc(x_12);
lean_inc(x_11);
x_235 = l_Lean_addDecl(x_234, x_11, x_12, x_229);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_237 = x_235;
} else {
 lean_dec_ref(x_235);
 x_237 = lean_box(0);
}
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_238 = l_Lean_inferDefEqAttr(x_4, x_9, x_10, x_11, x_12, x_236);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; 
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_240 = x_238;
} else {
 lean_dec_ref(x_238);
 x_240 = lean_box(0);
}
x_241 = l_Lean_Elab_WF_mkUnfoldEq___lam__0___closed__0;
x_242 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_241, x_11, x_239);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_unbox(x_243);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_246 = x_242;
} else {
 lean_dec_ref(x_242);
 x_246 = lean_box(0);
}
x_247 = lean_box(0);
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(0, 2, 0);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_245);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_249 = lean_ctor_get(x_242, 1);
lean_inc(x_249);
lean_dec(x_242);
x_250 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___closed__8;
x_251 = lean_unbox(x_197);
x_252 = l_Lean_MessageData_ofConstName(x_4, x_251);
if (lean_is_scalar(x_240)) {
 x_253 = lean_alloc_ctor(7, 2, 0);
} else {
 x_253 = x_240;
 lean_ctor_set_tag(x_253, 7);
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_252);
if (lean_is_scalar(x_237)) {
 x_254 = lean_alloc_ctor(7, 2, 0);
} else {
 x_254 = x_237;
 lean_ctor_set_tag(x_254, 7);
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_5);
x_255 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_241, x_254, x_9, x_10, x_11, x_12, x_249);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_255;
}
}
else
{
lean_dec(x_237);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_238;
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
return x_235;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_221);
lean_dec(x_215);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_256 = lean_ctor_get(x_227, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_227, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_258 = x_227;
} else {
 lean_dec_ref(x_227);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_215);
lean_dec(x_213);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_260 = lean_ctor_get(x_220, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_220, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_262 = x_220;
} else {
 lean_dec_ref(x_220);
 x_262 = lean_box(0);
}
if (lean_is_scalar(x_262)) {
 x_263 = lean_alloc_ctor(1, 2, 0);
} else {
 x_263 = x_262;
}
lean_ctor_set(x_263, 0, x_260);
lean_ctor_set(x_263, 1, x_261);
return x_263;
}
}
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_194);
lean_dec(x_190);
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
x_264 = lean_ctor_get(x_199, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_199, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_266 = x_199;
} else {
 lean_dec_ref(x_199);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_190);
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
x_268 = lean_ctor_get(x_193, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_193, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_270 = x_193;
} else {
 lean_dec_ref(x_193);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
}
else
{
uint8_t x_272; 
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
x_272 = !lean_is_exclusive(x_18);
if (x_272 == 0)
{
return x_18;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_18, 0);
x_274 = lean_ctor_get(x_18, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_18);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
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
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0;
x_2 = l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("WF", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_2 = l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_2 = l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_2 = l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_2 = l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__0;
x_2 = l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("PreDefinition", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_2 = l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_2 = l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unfold", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_2 = l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_2 = l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2514u);
x_2 = l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof___closed__4;
x_3 = lean_box(0);
x_4 = l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_;
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
l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__0____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__1____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__2____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__3____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__4____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__5____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__6____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__7____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__8____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__9____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__10____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__11____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__12____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__13____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__14____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__15____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__16____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__17____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_ = _init_l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_();
lean_mark_persistent(l_Lean_Elab_WF_initFn___closed__18____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_);
if (builtin) {res = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2514_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
