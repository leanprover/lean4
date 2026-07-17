// Lean compiler output
// Module: Lean.Meta.Tactic.Unfold
// Imports: public import Lean.Meta.Tactic.Delta public import Lean.Meta.Tactic.Simp.Main import Lean.Meta.WHNF
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
extern lean_object* l_Lean_Meta_Simp_neutralConfig;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isBackwardRflTheorem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_zetaDeltaFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceLocalDeclDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_unfold___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_unfold___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_unfold___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_unfold___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__4___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_unfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_unfold___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_unfold___closed__0 = (const lean_object*)&l_Lean_Meta_unfold___closed__0_value;
static const lean_closure_object l_Lean_Meta_unfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_unfold___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_unfold___closed__1 = (const lean_object*)&l_Lean_Meta_unfold___closed__1_value;
static const lean_closure_object l_Lean_Meta_unfold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_unfold___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_unfold___closed__2 = (const lean_object*)&l_Lean_Meta_unfold___closed__2_value;
static const lean_closure_object l_Lean_Meta_unfold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_unfold___lam__3___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_unfold___closed__3 = (const lean_object*)&l_Lean_Meta_unfold___closed__3_value;
static lean_once_cell_t l_Lean_Meta_unfold___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfold___closed__4;
static lean_once_cell_t l_Lean_Meta_unfold___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfold___closed__5;
static lean_once_cell_t l_Lean_Meta_unfold___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfold___closed__6;
static lean_once_cell_t l_Lean_Meta_unfold___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfold___closed__7;
static lean_once_cell_t l_Lean_Meta_unfold___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfold___closed__8;
static lean_once_cell_t l_Lean_Meta_unfold___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfold___closed__9;
static lean_once_cell_t l_Lean_Meta_unfold___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfold___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_unfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_unfoldTarget___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Tactic `unfold` failed to unfold `"};
static const lean_object* l_Lean_Meta_unfoldTarget___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_unfoldTarget___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_unfoldTarget___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfoldTarget___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_unfoldTarget___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "` in"};
static const lean_object* l_Lean_Meta_unfoldTarget___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_unfoldTarget___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_unfoldTarget___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfoldTarget___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Meta.Tactic.Unfold"};
static const lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.unfoldLocalDecl"};
static const lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_9_; lean_object* v_maxSteps_10_; lean_object* v_maxDischargeDepth_11_; uint8_t v_contextual_12_; uint8_t v_memoize_13_; uint8_t v_singlePass_14_; uint8_t v_zeta_15_; uint8_t v_beta_16_; uint8_t v_eta_17_; uint8_t v_etaStruct_18_; uint8_t v_iota_19_; uint8_t v_proj_20_; uint8_t v_decide_21_; uint8_t v_arith_22_; uint8_t v_autoUnfold_23_; uint8_t v_dsimp_24_; uint8_t v_failIfUnchanged_25_; uint8_t v_ground_26_; uint8_t v_unfoldPartialApp_27_; uint8_t v_zetaDelta_28_; uint8_t v_index_29_; uint8_t v_implicitDefEqProofs_30_; uint8_t v_zetaUnused_31_; uint8_t v_catchRuntime_32_; uint8_t v_zetaHave_33_; uint8_t v_congrConsts_34_; uint8_t v_bitVecOfNat_35_; uint8_t v_warnExponents_36_; uint8_t v_suggestions_37_; lean_object* v_maxSuggestions_38_; uint8_t v_locals_39_; uint8_t v_instances_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_a_8_);
lean_dec_ref_known(v___x_7_, 1);
v___x_9_ = l_Lean_Meta_Simp_neutralConfig;
v_maxSteps_10_ = lean_ctor_get(v___x_9_, 0);
v_maxDischargeDepth_11_ = lean_ctor_get(v___x_9_, 1);
v_contextual_12_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3);
v_memoize_13_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 1);
v_singlePass_14_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 2);
v_zeta_15_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 3);
v_beta_16_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 4);
v_eta_17_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 5);
v_etaStruct_18_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 6);
v_iota_19_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 7);
v_proj_20_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 8);
v_decide_21_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 9);
v_arith_22_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 10);
v_autoUnfold_23_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 11);
v_dsimp_24_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 12);
v_failIfUnchanged_25_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 13);
v_ground_26_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 14);
v_unfoldPartialApp_27_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 15);
v_zetaDelta_28_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 16);
v_index_29_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 17);
v_implicitDefEqProofs_30_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 18);
v_zetaUnused_31_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 19);
v_catchRuntime_32_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 20);
v_zetaHave_33_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 21);
v_congrConsts_34_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 23);
v_bitVecOfNat_35_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 24);
v_warnExponents_36_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 25);
v_suggestions_37_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 26);
v_maxSuggestions_38_ = lean_ctor_get(v___x_9_, 2);
v_locals_39_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 27);
v_instances_40_ = lean_ctor_get_uint8(v___x_9_, sizeof(void*)*3 + 28);
v___x_41_ = 1;
lean_inc(v_maxSuggestions_38_);
lean_inc(v_maxDischargeDepth_11_);
lean_inc(v_maxSteps_10_);
v___x_42_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_42_, 0, v_maxSteps_10_);
lean_ctor_set(v___x_42_, 1, v_maxDischargeDepth_11_);
lean_ctor_set(v___x_42_, 2, v_maxSuggestions_38_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3, v_contextual_12_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 1, v_memoize_13_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 2, v_singlePass_14_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 3, v_zeta_15_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 4, v_beta_16_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 5, v_eta_17_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 6, v_etaStruct_18_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 7, v_iota_19_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 8, v_proj_20_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 9, v_decide_21_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 10, v_arith_22_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 11, v_autoUnfold_23_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 12, v_dsimp_24_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 13, v_failIfUnchanged_25_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 14, v_ground_26_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 15, v_unfoldPartialApp_27_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 16, v_zetaDelta_28_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 17, v_index_29_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_30_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 19, v_zetaUnused_31_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 20, v_catchRuntime_32_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 21, v_zetaHave_33_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 22, v___x_41_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 23, v_congrConsts_34_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 24, v_bitVecOfNat_35_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 25, v_warnExponents_36_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 26, v_suggestions_37_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 27, v_locals_39_);
lean_ctor_set_uint8(v___x_42_, sizeof(void*)*3 + 28, v_instances_40_);
v___x_43_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0));
v___x_44_ = l_Lean_Options_empty;
v___x_45_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_42_, v___x_43_, v_a_8_, v___x_44_, v_a_3_, v_a_4_, v_a_5_);
return v___x_45_;
}
else
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_53_; 
v_a_46_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_53_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_53_ == 0)
{
v___x_48_ = v___x_7_;
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_7_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_53_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_51_; 
if (v_isShared_49_ == 0)
{
v___x_51_ = v___x_48_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_a_46_);
v___x_51_ = v_reuseFailAlloc_52_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
return v___x_51_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___boxed(lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_54_, v_a_55_, v_a_56_);
lean_dec(v_a_56_);
lean_dec_ref(v_a_55_);
lean_dec_ref(v_a_54_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_59_, v_a_61_, v_a_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___boxed(lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(v_a_65_, v_a_66_, v_a_67_, v_a_68_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
lean_dec(v_a_66_);
lean_dec_ref(v_a_65_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(lean_object* v_unfoldThm_73_, lean_object* v_e_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_a_84_; lean_object* v___x_135_; 
lean_inc(v_unfoldThm_73_);
v___x_135_ = l_Lean_Meta_isRflTheorem(v_unfoldThm_73_, v_a_80_, v_a_81_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
lean_inc(v_unfoldThm_73_);
v___x_137_ = l_Lean_Meta_isBackwardRflTheorem(v_unfoldThm_73_, v_a_80_, v_a_81_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v_keyedConfig_141_; uint8_t v_trackZetaDelta_142_; lean_object* v_zetaDeltaSet_143_; lean_object* v_lctx_144_; lean_object* v_localInstances_145_; lean_object* v_defEqCtx_x3f_146_; lean_object* v_synthPendingDepth_147_; lean_object* v_customCanUnfoldPredicate_x3f_148_; uint8_t v_univApprox_149_; uint8_t v_inTypeClassResolution_150_; uint8_t v_cacheInferType_151_; uint8_t v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; uint8_t v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
v___x_139_ = lean_box(0);
lean_inc(v_unfoldThm_73_);
v___x_140_ = l_Lean_mkConst(v_unfoldThm_73_, v___x_139_);
v_keyedConfig_141_ = lean_ctor_get(v_a_78_, 0);
v_trackZetaDelta_142_ = lean_ctor_get_uint8(v_a_78_, sizeof(void*)*7);
v_zetaDeltaSet_143_ = lean_ctor_get(v_a_78_, 1);
v_lctx_144_ = lean_ctor_get(v_a_78_, 2);
v_localInstances_145_ = lean_ctor_get(v_a_78_, 3);
v_defEqCtx_x3f_146_ = lean_ctor_get(v_a_78_, 4);
v_synthPendingDepth_147_ = lean_ctor_get(v_a_78_, 5);
v_customCanUnfoldPredicate_x3f_148_ = lean_ctor_get(v_a_78_, 6);
v_univApprox_149_ = lean_ctor_get_uint8(v_a_78_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_150_ = lean_ctor_get_uint8(v_a_78_, sizeof(void*)*7 + 2);
v_cacheInferType_151_ = lean_ctor_get_uint8(v_a_78_, sizeof(void*)*7 + 3);
v___x_152_ = 1;
v___x_153_ = 0;
v___x_154_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_154_, 0, v_unfoldThm_73_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_152_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1 + 1, v___x_153_);
v___x_155_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0));
v___x_156_ = lean_unsigned_to_nat(1000u);
v___x_157_ = lean_alloc_ctor(0, 5, 4);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_155_);
lean_ctor_set(v___x_157_, 2, v___x_140_);
lean_ctor_set(v___x_157_, 3, v___x_156_);
lean_ctor_set(v___x_157_, 4, v___x_154_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*5, v___x_152_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*5 + 1, v___x_153_);
v___x_158_ = lean_unbox(v_a_136_);
lean_dec(v_a_136_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*5 + 2, v___x_158_);
v___x_159_ = lean_unbox(v_a_138_);
lean_dec(v_a_138_);
lean_ctor_set_uint8(v___x_157_, sizeof(void*)*5 + 3, v___x_159_);
v___x_160_ = 2;
lean_inc_ref(v_keyedConfig_141_);
v___x_161_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_160_, v_keyedConfig_141_);
lean_inc(v_customCanUnfoldPredicate_x3f_148_);
lean_inc(v_synthPendingDepth_147_);
lean_inc(v_defEqCtx_x3f_146_);
lean_inc_ref(v_localInstances_145_);
lean_inc_ref(v_lctx_144_);
lean_inc(v_zetaDeltaSet_143_);
v___x_162_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_zetaDeltaSet_143_);
lean_ctor_set(v___x_162_, 2, v_lctx_144_);
lean_ctor_set(v___x_162_, 3, v_localInstances_145_);
lean_ctor_set(v___x_162_, 4, v_defEqCtx_x3f_146_);
lean_ctor_set(v___x_162_, 5, v_synthPendingDepth_147_);
lean_ctor_set(v___x_162_, 6, v_customCanUnfoldPredicate_x3f_148_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*7, v_trackZetaDelta_142_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*7 + 1, v_univApprox_149_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*7 + 2, v_inTypeClassResolution_150_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*7 + 3, v_cacheInferType_151_);
v___x_163_ = l_Lean_Meta_Simp_tryTheorem_x3f(v_e_74_, v___x_157_, v_a_75_, v_a_76_, v_a_77_, v___x_162_, v_a_79_, v_a_80_, v_a_81_);
lean_dec_ref_known(v___x_162_, 7);
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_164_; 
v_a_164_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v___x_163_, 1);
v_a_84_ = v_a_164_;
goto v___jp_83_;
}
else
{
if (lean_obj_tag(v___x_163_) == 0)
{
lean_object* v_a_165_; 
v_a_165_ = lean_ctor_get(v___x_163_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_163_, 1);
v_a_84_ = v_a_165_;
goto v___jp_83_;
}
else
{
lean_object* v_a_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_173_; 
v_a_166_ = lean_ctor_get(v___x_163_, 0);
v_isSharedCheck_173_ = !lean_is_exclusive(v___x_163_);
if (v_isSharedCheck_173_ == 0)
{
v___x_168_ = v___x_163_;
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_a_166_);
lean_dec(v___x_163_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_173_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_171_; 
if (v_isShared_169_ == 0)
{
v___x_171_ = v___x_168_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_a_166_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
else
{
lean_object* v_a_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_181_; 
lean_dec(v_a_136_);
lean_dec_ref(v_e_74_);
lean_dec(v_unfoldThm_73_);
v_a_174_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_181_ == 0)
{
v___x_176_ = v___x_137_;
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_a_174_);
lean_dec(v___x_137_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_181_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v___x_179_; 
if (v_isShared_177_ == 0)
{
v___x_179_ = v___x_176_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v_e_74_);
lean_dec(v_unfoldThm_73_);
v_a_182_ = lean_ctor_get(v___x_135_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_135_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_135_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_135_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
v___jp_83_:
{
if (lean_obj_tag(v_a_84_) == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_85_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_85_, 0, v_a_84_);
v___x_86_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
return v___x_86_;
}
else
{
lean_object* v_val_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_134_; 
v_val_87_ = lean_ctor_get(v_a_84_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v_a_84_);
if (v_isSharedCheck_134_ == 0)
{
v___x_89_ = v_a_84_;
v_isShared_90_ = v_isSharedCheck_134_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_val_87_);
lean_dec(v_a_84_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_134_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v_expr_91_; lean_object* v_proof_x3f_92_; uint8_t v_cache_93_; lean_object* v___x_94_; 
v_expr_91_ = lean_ctor_get(v_val_87_, 0);
v_proof_x3f_92_ = lean_ctor_get(v_val_87_, 1);
v_cache_93_ = lean_ctor_get_uint8(v_val_87_, sizeof(void*)*2);
v___x_94_ = l_Lean_Meta_reduceMatcher_x3f(v_expr_91_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_125_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_125_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_125_ == 0)
{
v___x_97_ = v___x_94_;
v_isShared_98_ = v_isSharedCheck_125_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_a_95_);
lean_dec(v___x_94_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_125_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
if (lean_obj_tag(v_a_95_) == 0)
{
lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_116_; 
lean_inc(v_proof_x3f_92_);
lean_del_object(v___x_89_);
v_isSharedCheck_116_ = !lean_is_exclusive(v_val_87_);
if (v_isSharedCheck_116_ == 0)
{
lean_object* v_unused_117_; lean_object* v_unused_118_; 
v_unused_117_ = lean_ctor_get(v_val_87_, 1);
lean_dec(v_unused_117_);
v_unused_118_ = lean_ctor_get(v_val_87_, 0);
lean_dec(v_unused_118_);
v___x_100_ = v_val_87_;
v_isShared_101_ = v_isSharedCheck_116_;
goto v_resetjp_99_;
}
else
{
lean_dec(v_val_87_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_116_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v_val_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_115_; 
v_val_102_ = lean_ctor_get(v_a_95_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v_a_95_);
if (v_isSharedCheck_115_ == 0)
{
v___x_104_ = v_a_95_;
v_isShared_105_ = v_isSharedCheck_115_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_val_102_);
lean_dec(v_a_95_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_115_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v_val_102_);
v___x_107_ = v___x_100_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_val_102_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_proof_x3f_92_);
lean_ctor_set_uint8(v_reuseFailAlloc_114_, sizeof(void*)*2, v_cache_93_);
v___x_107_ = v_reuseFailAlloc_114_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
lean_object* v___x_109_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_107_);
v___x_109_ = v___x_104_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_113_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_109_);
v___x_111_ = v___x_97_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
else
{
lean_object* v___x_120_; 
lean_dec(v_a_95_);
if (v_isShared_90_ == 0)
{
lean_ctor_set_tag(v___x_89_, 0);
v___x_120_ = v___x_89_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v_val_87_);
v___x_120_ = v_reuseFailAlloc_124_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_object* v___x_122_; 
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_120_);
v___x_122_ = v___x_97_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
else
{
lean_object* v_a_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_133_; 
lean_del_object(v___x_89_);
lean_dec(v_val_87_);
v_a_126_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_133_ == 0)
{
v___x_128_ = v___x_94_;
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_a_126_);
lean_dec(v___x_94_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_133_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_a_126_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed(lean_object* v_unfoldThm_190_, lean_object* v_e_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(v_unfoldThm_190_, v_e_191_, v_a_192_, v_a_193_, v_a_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_a_194_);
lean_dec_ref(v_a_193_);
lean_dec(v_a_192_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0(lean_object* v_e_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v___x_210_; uint8_t v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_210_ = lean_box(0);
v___x_211_ = 1;
v___x_212_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_212_, 0, v_e_201_);
lean_ctor_set(v___x_212_, 1, v___x_210_);
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*2, v___x_211_);
v___x_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___x_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0___boxed(lean_object* v_e_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Lean_Meta_unfold___lam__0(v_e_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___y_216_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1(lean_object* v_x_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_Meta_unfold___lam__1___closed__0));
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1___boxed(lean_object* v_x_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Meta_unfold___lam__1(v_x_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v_x_238_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2(lean_object* v_e_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v_e_248_);
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2___boxed(lean_object* v_e_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_unfold___lam__2(v_e_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3(lean_object* v_x_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_box(0);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3___boxed(lean_object* v_x_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_unfold___lam__3(v_x_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
lean_dec_ref(v_x_280_);
return v_res_289_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_unfold___lam__4(lean_object* v_declName_290_, lean_object* v_x_291_){
_start:
{
uint8_t v___x_292_; 
v___x_292_ = lean_name_eq(v_x_291_, v_declName_290_);
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__4___boxed(lean_object* v_declName_293_, lean_object* v_x_294_){
_start:
{
uint8_t v_res_295_; lean_object* v_r_296_; 
v_res_295_ = l_Lean_Meta_unfold___lam__4(v_declName_293_, v_x_294_);
lean_dec(v_x_294_);
lean_dec(v_declName_293_);
v_r_296_ = lean_box(v_res_295_);
return v_r_296_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__4(void){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_301_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__5(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_obj_once(&l_Lean_Meta_unfold___closed__4, &l_Lean_Meta_unfold___closed__4_once, _init_l_Lean_Meta_unfold___closed__4);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__6(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__7(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_unsigned_to_nat(32u);
v___x_308_ = lean_mk_empty_array_with_capacity(v___x_307_);
v___x_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__8(void){
_start:
{
size_t v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_310_ = ((size_t)5ULL);
v___x_311_ = lean_unsigned_to_nat(0u);
v___x_312_ = lean_unsigned_to_nat(32u);
v___x_313_ = lean_mk_empty_array_with_capacity(v___x_312_);
v___x_314_ = lean_obj_once(&l_Lean_Meta_unfold___closed__7, &l_Lean_Meta_unfold___closed__7_once, _init_l_Lean_Meta_unfold___closed__7);
v___x_315_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
lean_ctor_set(v___x_315_, 2, v___x_311_);
lean_ctor_set(v___x_315_, 3, v___x_311_);
lean_ctor_set_usize(v___x_315_, 4, v___x_310_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__9(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_Meta_unfold___closed__8, &l_Lean_Meta_unfold___closed__8_once, _init_l_Lean_Meta_unfold___closed__8);
v___x_317_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_317_);
lean_ctor_set(v___x_318_, 2, v___x_317_);
lean_ctor_set(v___x_318_, 3, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__10(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_obj_once(&l_Lean_Meta_unfold___closed__9, &l_Lean_Meta_unfold___closed__9_once, _init_l_Lean_Meta_unfold___closed__9);
v___x_320_ = lean_obj_once(&l_Lean_Meta_unfold___closed__6, &l_Lean_Meta_unfold___closed__6_once, _init_l_Lean_Meta_unfold___closed__6);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold(lean_object* v_e_322_, lean_object* v_declName_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
uint8_t v___x_329_; lean_object* v___x_330_; 
v___x_329_ = 0;
lean_inc(v_declName_323_);
v___x_330_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_323_, v___x_329_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
if (lean_obj_tag(v_a_331_) == 1)
{
lean_object* v_val_332_; lean_object* v___x_333_; 
lean_dec(v_declName_323_);
v_val_332_ = lean_ctor_get(v_a_331_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v_a_331_, 1);
v___x_333_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_324_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___f_335_; lean_object* v___f_336_; lean_object* v___f_337_; lean_object* v___f_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___f_335_ = ((lean_object*)(l_Lean_Meta_unfold___closed__0));
v___f_336_ = ((lean_object*)(l_Lean_Meta_unfold___closed__1));
v___f_337_ = ((lean_object*)(l_Lean_Meta_unfold___closed__2));
v___f_338_ = ((lean_object*)(l_Lean_Meta_unfold___closed__3));
v___x_339_ = lean_obj_once(&l_Lean_Meta_unfold___closed__10, &l_Lean_Meta_unfold___closed__10_once, _init_l_Lean_Meta_unfold___closed__10);
v___x_340_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed), 10, 1);
lean_closure_set(v___x_340_, 0, v_val_332_);
v___x_341_ = 1;
v___x_342_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_342_, 0, v___x_340_);
lean_ctor_set(v___x_342_, 1, v___f_335_);
lean_ctor_set(v___x_342_, 2, v___f_336_);
lean_ctor_set(v___x_342_, 3, v___f_337_);
lean_ctor_set(v___x_342_, 4, v___f_338_);
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*5, v___x_341_);
v___x_343_ = l_Lean_Meta_Simp_main(v_e_322_, v_a_334_, v___x_339_, v___x_342_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_343_) == 0)
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_352_; 
v_a_344_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_352_ == 0)
{
v___x_346_ = v___x_343_;
v_isShared_347_ = v_isSharedCheck_352_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_343_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_352_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_fst_348_; lean_object* v___x_350_; 
v_fst_348_ = lean_ctor_get(v_a_344_, 0);
lean_inc(v_fst_348_);
lean_dec(v_a_344_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 0, v_fst_348_);
v___x_350_ = v___x_346_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_fst_348_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
v_a_353_ = lean_ctor_get(v___x_343_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_343_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_343_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_343_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec(v_val_332_);
lean_dec_ref(v_e_322_);
v_a_361_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_333_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_333_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
else
{
lean_object* v___f_369_; lean_object* v___x_370_; 
lean_dec(v_a_331_);
v___f_369_ = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__4___boxed), 2, 1);
lean_closure_set(v___f_369_, 0, v_declName_323_);
v___x_370_ = l_Lean_Meta_deltaExpand(v_e_322_, v___f_369_, v___x_329_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_381_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_381_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_381_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_381_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; uint8_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v___x_375_ = lean_box(0);
v___x_376_ = 1;
v___x_377_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_377_, 0, v_a_371_);
lean_ctor_set(v___x_377_, 1, v___x_375_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*2, v___x_376_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_377_);
v___x_379_ = v___x_373_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_370_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_370_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
lean_dec(v_declName_323_);
lean_dec_ref(v_e_322_);
v_a_390_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_330_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_330_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___boxed(lean_object* v_e_398_, lean_object* v_declName_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Meta_unfold(v_e_398_, v_declName_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(lean_object* v_e_406_, lean_object* v___y_407_){
_start:
{
uint8_t v___x_409_; 
v___x_409_ = l_Lean_Expr_hasMVar(v_e_406_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_e_406_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v_mctx_412_; lean_object* v___x_413_; lean_object* v_fst_414_; lean_object* v_snd_415_; lean_object* v___x_416_; lean_object* v_cache_417_; lean_object* v_zetaDeltaFVarIds_418_; lean_object* v_postponed_419_; lean_object* v_diag_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_429_; 
v___x_411_ = lean_st_ref_get(v___y_407_);
v_mctx_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc_ref(v_mctx_412_);
lean_dec(v___x_411_);
v___x_413_ = l_Lean_instantiateMVarsCore(v_mctx_412_, v_e_406_);
v_fst_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_fst_414_);
v_snd_415_ = lean_ctor_get(v___x_413_, 1);
lean_inc(v_snd_415_);
lean_dec_ref(v___x_413_);
v___x_416_ = lean_st_ref_take(v___y_407_);
v_cache_417_ = lean_ctor_get(v___x_416_, 1);
v_zetaDeltaFVarIds_418_ = lean_ctor_get(v___x_416_, 2);
v_postponed_419_ = lean_ctor_get(v___x_416_, 3);
v_diag_420_ = lean_ctor_get(v___x_416_, 4);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v___x_416_, 0);
lean_dec(v_unused_430_);
v___x_422_ = v___x_416_;
v_isShared_423_ = v_isSharedCheck_429_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_diag_420_);
lean_inc(v_postponed_419_);
lean_inc(v_zetaDeltaFVarIds_418_);
lean_inc(v_cache_417_);
lean_dec(v___x_416_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_429_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_425_; 
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v_snd_415_);
v___x_425_ = v___x_422_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v_snd_415_);
lean_ctor_set(v_reuseFailAlloc_428_, 1, v_cache_417_);
lean_ctor_set(v_reuseFailAlloc_428_, 2, v_zetaDeltaFVarIds_418_);
lean_ctor_set(v_reuseFailAlloc_428_, 3, v_postponed_419_);
lean_ctor_set(v_reuseFailAlloc_428_, 4, v_diag_420_);
v___x_425_ = v_reuseFailAlloc_428_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_426_ = lean_st_ref_set(v___y_407_, v___x_425_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v_fst_414_);
return v___x_427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg___boxed(lean_object* v_e_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_431_, v___y_432_);
lean_dec(v___y_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(lean_object* v_e_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_435_, v___y_437_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___boxed(lean_object* v_e_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(v_e_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(lean_object* v_mvarId_449_, lean_object* v_x_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_449_, v_x_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_a_465_; lean_object* v___x_467_; uint8_t v_isShared_468_; uint8_t v_isSharedCheck_472_; 
v_a_465_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_472_ == 0)
{
v___x_467_ = v___x_456_;
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
else
{
lean_inc(v_a_465_);
lean_dec(v___x_456_);
v___x_467_ = lean_box(0);
v_isShared_468_ = v_isSharedCheck_472_;
goto v_resetjp_466_;
}
v_resetjp_466_:
{
lean_object* v___x_470_; 
if (v_isShared_468_ == 0)
{
v___x_470_ = v___x_467_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_a_465_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg___boxed(lean_object* v_mvarId_473_, lean_object* v_x_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_473_, v_x_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(lean_object* v_00_u03b1_481_, lean_object* v_mvarId_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_482_, v_x_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___boxed(lean_object* v_00_u03b1_490_, lean_object* v_mvarId_491_, lean_object* v_x_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(v_00_u03b1_490_, v_mvarId_491_, v_x_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
lean_dec(v___y_494_);
lean_dec_ref(v___y_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(lean_object* v_msgData_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; lean_object* v_env_506_; lean_object* v___x_507_; lean_object* v_mctx_508_; lean_object* v_lctx_509_; lean_object* v_options_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_505_ = lean_st_ref_get(v___y_503_);
v_env_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc_ref(v_env_506_);
lean_dec(v___x_505_);
v___x_507_ = lean_st_ref_get(v___y_501_);
v_mctx_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc_ref(v_mctx_508_);
lean_dec(v___x_507_);
v_lctx_509_ = lean_ctor_get(v___y_500_, 2);
v_options_510_ = lean_ctor_get(v___y_502_, 2);
lean_inc_ref(v_options_510_);
lean_inc_ref(v_lctx_509_);
v___x_511_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_511_, 0, v_env_506_);
lean_ctor_set(v___x_511_, 1, v_mctx_508_);
lean_ctor_set(v___x_511_, 2, v_lctx_509_);
lean_ctor_set(v___x_511_, 3, v_options_510_);
v___x_512_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_msgData_499_);
v___x_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1___boxed(lean_object* v_msgData_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msgData_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(lean_object* v_msg_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_ref_527_; lean_object* v___x_528_; lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_537_; 
v_ref_527_ = lean_ctor_get(v___y_524_, 5);
v___x_528_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msg_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
v_a_529_ = lean_ctor_get(v___x_528_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_528_);
if (v_isSharedCheck_537_ == 0)
{
v___x_531_ = v___x_528_;
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_528_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_537_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_533_; lean_object* v___x_535_; 
lean_inc(v_ref_527_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_ref_527_);
lean_ctor_set(v___x_533_, 1, v_a_529_);
if (v_isShared_532_ == 0)
{
lean_ctor_set_tag(v___x_531_, 1);
lean_ctor_set(v___x_531_, 0, v___x_533_);
v___x_535_ = v___x_531_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg___boxed(lean_object* v_msg_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
return v_res_544_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = ((lean_object*)(l_Lean_Meta_unfoldTarget___lam__0___closed__0));
v___x_547_ = l_Lean_stringToMessageData(v___x_546_);
return v___x_547_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_Meta_unfoldTarget___lam__0___closed__2));
v___x_550_ = l_Lean_stringToMessageData(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0(lean_object* v_mvarId_551_, lean_object* v_declName_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; 
lean_inc(v_mvarId_551_);
v___x_558_ = l_Lean_MVarId_getType(v_mvarId_551_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; lean_object* v_a_561_; lean_object* v___x_562_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_559_, v___y_554_);
v_a_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc_n(v_a_561_, 2);
lean_dec_ref(v___x_560_);
lean_inc(v_declName_552_);
v___x_562_ = l_Lean_Meta_unfold(v_a_561_, v_declName_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v_expr_564_; uint8_t v___x_565_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_a_563_);
lean_dec_ref_known(v___x_562_, 1);
v_expr_564_ = lean_ctor_get(v_a_563_, 0);
v___x_565_ = lean_expr_eqv(v_expr_564_, v_a_561_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; 
lean_dec(v_declName_552_);
v___x_566_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_551_, v_a_561_, v_a_563_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
lean_dec(v_a_561_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; uint8_t v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_dec(v_a_563_);
lean_dec(v_mvarId_551_);
v___x_567_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_568_ = 0;
v___x_569_ = l_Lean_MessageData_ofConstName(v_declName_552_, v___x_568_);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_567_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_570_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_indentExpr(v_a_561_);
v___x_574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_572_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
v___x_575_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_574_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
v_a_576_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_575_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_575_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
else
{
lean_object* v_a_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_591_; 
lean_dec(v_a_561_);
lean_dec(v_declName_552_);
lean_dec(v_mvarId_551_);
v_a_584_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_591_ == 0)
{
v___x_586_ = v___x_562_;
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_a_584_);
lean_dec(v___x_562_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_591_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_589_; 
if (v_isShared_587_ == 0)
{
v___x_589_ = v___x_586_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_a_584_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
}
}
else
{
lean_object* v_a_592_; lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_599_; 
lean_dec(v_declName_552_);
lean_dec(v_mvarId_551_);
v_a_592_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_599_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_599_ == 0)
{
v___x_594_ = v___x_558_;
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
else
{
lean_inc(v_a_592_);
lean_dec(v___x_558_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_599_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v___x_597_; 
if (v_isShared_595_ == 0)
{
v___x_597_ = v___x_594_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_a_592_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0___boxed(lean_object* v_mvarId_600_, lean_object* v_declName_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_res_607_; 
v_res_607_ = l_Lean_Meta_unfoldTarget___lam__0(v_mvarId_600_, v_declName_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_);
lean_dec(v___y_605_);
lean_dec_ref(v___y_604_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget(lean_object* v_mvarId_608_, lean_object* v_declName_609_, lean_object* v_a_610_, lean_object* v_a_611_, lean_object* v_a_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___f_615_; lean_object* v___x_616_; 
lean_inc(v_mvarId_608_);
v___f_615_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_615_, 0, v_mvarId_608_);
lean_closure_set(v___f_615_, 1, v_declName_609_);
v___x_616_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_608_, v___f_615_, v_a_610_, v_a_611_, v_a_612_, v_a_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___boxed(lean_object* v_mvarId_617_, lean_object* v_declName_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_Meta_unfoldTarget(v_mvarId_617_, v_declName_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
lean_dec(v_a_622_);
lean_dec_ref(v_a_621_);
lean_dec(v_a_620_);
lean_dec_ref(v_a_619_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(lean_object* v_00_u03b1_625_, lean_object* v_msg_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___boxed(lean_object* v_00_u03b1_633_, lean_object* v_msg_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(v_00_u03b1_633_, v_msg_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(lean_object* v_msg_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___f_648_; lean_object* v___x_976__overap_649_; lean_object* v___x_650_; 
v___f_648_ = ((lean_object*)(l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0));
v___x_976__overap_649_ = lean_panic_fn_borrowed(v___f_648_, v_msg_642_);
lean_inc(v___y_646_);
lean_inc_ref(v___y_645_);
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
v___x_650_ = lean_apply_5(v___x_976__overap_649_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, lean_box(0));
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___boxed(lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_657_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_661_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2));
v___x_662_ = lean_unsigned_to_nat(94u);
v___x_663_ = lean_unsigned_to_nat(43u);
v___x_664_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1));
v___x_665_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0));
v___x_666_ = l_mkPanicMessageWithDecl(v___x_665_, v___x_664_, v___x_663_, v___x_662_, v___x_661_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0(lean_object* v_fvarId_667_, lean_object* v_declName_668_, lean_object* v_mvarId_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___x_675_; 
lean_inc(v_fvarId_667_);
v___x_675_ = l_Lean_FVarId_getType___redArg(v_fvarId_667_, v___y_670_, v___y_672_, v___y_673_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v___x_677_; lean_object* v_a_678_; lean_object* v___x_679_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc_n(v_a_676_, 2);
lean_dec_ref_known(v___x_675_, 1);
v___x_677_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_676_, v___y_671_);
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref(v___x_677_);
lean_inc(v_declName_668_);
v___x_679_ = l_Lean_Meta_unfold(v_a_678_, v_declName_668_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v_expr_708_; uint8_t v___x_709_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v_expr_708_ = lean_ctor_get(v_a_680_, 0);
v___x_709_ = lean_expr_eqv(v_expr_708_, v_a_676_);
if (v___x_709_ == 0)
{
lean_dec(v_a_676_);
lean_dec(v_declName_668_);
v___y_682_ = v___y_670_;
v___y_683_ = v___y_671_;
v___y_684_ = v___y_672_;
v___y_685_ = v___y_673_;
goto v___jp_681_;
}
else
{
lean_object* v___x_710_; uint8_t v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_dec(v_a_680_);
lean_dec(v_mvarId_669_);
lean_dec(v_fvarId_667_);
v___x_710_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_711_ = 0;
v___x_712_ = l_Lean_MessageData_ofConstName(v_declName_668_, v___x_711_);
v___x_713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_713_, 0, v___x_710_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
v___x_714_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_713_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
v___x_716_ = l_Lean_indentExpr(v_a_676_);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_715_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v___x_718_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_717_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
v___jp_681_:
{
uint8_t v___x_686_; lean_object* v___x_687_; 
v___x_686_ = 0;
v___x_687_ = l_Lean_Meta_applySimpResultToLocalDecl(v_mvarId_669_, v_fvarId_667_, v_a_680_, v___x_686_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_699_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_699_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_699_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_a_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_699_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
if (lean_obj_tag(v_a_688_) == 1)
{
lean_object* v_val_692_; lean_object* v_snd_693_; lean_object* v___x_695_; 
v_val_692_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_val_692_);
lean_dec_ref_known(v_a_688_, 1);
v_snd_693_ = lean_ctor_get(v_val_692_, 1);
lean_inc(v_snd_693_);
lean_dec(v_val_692_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v_snd_693_);
v___x_695_ = v___x_690_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_snd_693_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
else
{
lean_object* v___x_697_; lean_object* v___x_698_; 
lean_del_object(v___x_690_);
lean_dec(v_a_688_);
v___x_697_ = lean_obj_once(&l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3, &l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3);
v___x_698_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v___x_697_, v___y_682_, v___y_683_, v___y_684_, v___y_685_);
return v___x_698_;
}
}
}
else
{
lean_object* v_a_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_707_; 
v_a_700_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_707_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_707_ == 0)
{
v___x_702_ = v___x_687_;
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_a_700_);
lean_dec(v___x_687_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_707_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_705_; 
if (v_isShared_703_ == 0)
{
v___x_705_ = v___x_702_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_a_700_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec(v_a_676_);
lean_dec(v_mvarId_669_);
lean_dec(v_declName_668_);
lean_dec(v_fvarId_667_);
v_a_727_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_679_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_679_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_a_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v_mvarId_669_);
lean_dec(v_declName_668_);
lean_dec(v_fvarId_667_);
v_a_735_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_675_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_675_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___boxed(lean_object* v_fvarId_743_, lean_object* v_declName_744_, lean_object* v_mvarId_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Meta_unfoldLocalDecl___lam__0(v_fvarId_743_, v_declName_744_, v_mvarId_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl(lean_object* v_mvarId_752_, lean_object* v_fvarId_753_, lean_object* v_declName_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___f_760_; lean_object* v___x_761_; 
lean_inc(v_mvarId_752_);
v___f_760_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_760_, 0, v_fvarId_753_);
lean_closure_set(v___f_760_, 1, v_declName_754_);
lean_closure_set(v___f_760_, 2, v_mvarId_752_);
v___x_761_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_752_, v___f_760_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___boxed(lean_object* v_mvarId_762_, lean_object* v_fvarId_763_, lean_object* v_declName_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Meta_unfoldLocalDecl(v_mvarId_762_, v_fvarId_763_, v_declName_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0(lean_object* v_mvarId_771_, lean_object* v_declFVarId_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; 
lean_inc(v_mvarId_771_);
v___x_778_ = l_Lean_MVarId_getType(v_mvarId_771_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_780_; lean_object* v_a_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v___x_780_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_779_, v___y_774_);
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc_n(v_a_781_, 2);
lean_dec_ref(v___x_780_);
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_mk_empty_array_with_capacity(v___x_782_);
lean_inc(v_declFVarId_772_);
v___x_784_ = lean_array_push(v___x_783_, v_declFVarId_772_);
v___x_785_ = l_Lean_Meta_zetaDeltaFVars(v_a_781_, v___x_784_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; uint8_t v___x_787_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___x_787_ = lean_expr_eqv(v_a_786_, v_a_781_);
if (v___x_787_ == 0)
{
lean_object* v___x_788_; 
lean_dec(v_a_781_);
lean_dec(v_declFVarId_772_);
v___x_788_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_771_, v_a_786_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v_a_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_805_; 
lean_dec(v_a_786_);
lean_dec(v_mvarId_771_);
v___x_789_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_790_ = l_Lean_Expr_fvar___override(v_declFVarId_772_);
v___x_791_ = l_Lean_MessageData_ofExpr(v___x_790_);
v___x_792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_789_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_794_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_792_);
lean_ctor_set(v___x_794_, 1, v___x_793_);
v___x_795_ = l_Lean_indentExpr(v_a_781_);
v___x_796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_794_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_796_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
v_a_798_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_805_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_805_ == 0)
{
v___x_800_ = v___x_797_;
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_a_798_);
lean_dec(v___x_797_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_805_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_a_798_);
v___x_803_ = v_reuseFailAlloc_804_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
return v___x_803_;
}
}
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_a_781_);
lean_dec(v_declFVarId_772_);
lean_dec(v_mvarId_771_);
v_a_806_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_785_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_785_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec(v_declFVarId_772_);
lean_dec(v_mvarId_771_);
v_a_814_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_778_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_778_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0___boxed(lean_object* v_mvarId_822_, lean_object* v_declFVarId_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Meta_zetaDeltaTarget___lam__0(v_mvarId_822_, v_declFVarId_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec_ref(v___y_824_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget(lean_object* v_mvarId_830_, lean_object* v_declFVarId_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v___f_837_; lean_object* v___x_838_; 
lean_inc(v_mvarId_830_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_837_, 0, v_mvarId_830_);
lean_closure_set(v___f_837_, 1, v_declFVarId_831_);
v___x_838_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_830_, v___f_837_, v_a_832_, v_a_833_, v_a_834_, v_a_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___boxed(lean_object* v_mvarId_839_, lean_object* v_declFVarId_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_zetaDeltaTarget(v_mvarId_839_, v_declFVarId_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
lean_dec(v_a_842_);
lean_dec_ref(v_a_841_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0(lean_object* v_fvarId_847_, lean_object* v_declFVarId_848_, lean_object* v_mvarId_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; 
lean_inc(v_fvarId_847_);
v___x_855_ = l_Lean_FVarId_getType___redArg(v_fvarId_847_, v___y_850_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v_a_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc_n(v_a_856_, 2);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_856_, v___y_851_);
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref(v___x_857_);
v___x_859_ = lean_unsigned_to_nat(1u);
v___x_860_ = lean_mk_empty_array_with_capacity(v___x_859_);
v___x_861_ = lean_array_push(v___x_860_, v_declFVarId_848_);
v___x_862_ = l_Lean_Meta_zetaDeltaFVars(v_a_858_, v___x_861_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; uint8_t v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = lean_expr_eqv(v_a_863_, v_a_856_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; 
lean_dec(v_a_856_);
v___x_865_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_849_, v_fvarId_847_, v_a_863_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec(v_a_863_);
lean_dec(v_mvarId_849_);
v___x_866_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_867_ = l_Lean_Expr_fvar___override(v_fvarId_847_);
v___x_868_ = l_Lean_MessageData_ofExpr(v___x_867_);
v___x_869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_866_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
v___x_870_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
v___x_872_ = l_Lean_indentExpr(v_a_856_);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_873_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec(v_a_856_);
lean_dec(v_mvarId_849_);
lean_dec(v_fvarId_847_);
v_a_883_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_862_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_862_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec(v_mvarId_849_);
lean_dec(v_declFVarId_848_);
lean_dec(v_fvarId_847_);
v_a_891_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_855_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_855_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed(lean_object* v_fvarId_899_, lean_object* v_declFVarId_900_, lean_object* v_mvarId_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_Meta_zetaDeltaLocalDecl___lam__0(v_fvarId_899_, v_declFVarId_900_, v_mvarId_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl(lean_object* v_mvarId_908_, lean_object* v_fvarId_909_, lean_object* v_declFVarId_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___f_916_; lean_object* v___x_917_; 
lean_inc(v_mvarId_908_);
v___f_916_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_916_, 0, v_fvarId_909_);
lean_closure_set(v___f_916_, 1, v_declFVarId_910_);
lean_closure_set(v___f_916_, 2, v_mvarId_908_);
v___x_917_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_908_, v___f_916_, v_a_911_, v_a_912_, v_a_913_, v_a_914_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___boxed(lean_object* v_mvarId_918_, lean_object* v_fvarId_919_, lean_object* v_declFVarId_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Meta_zetaDeltaLocalDecl(v_mvarId_918_, v_fvarId_919_, v_declFVarId_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec_ref(v_a_921_);
return v_res_926_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Unfold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Unfold(builtin);
}
#ifdef __cplusplus
}
#endif
