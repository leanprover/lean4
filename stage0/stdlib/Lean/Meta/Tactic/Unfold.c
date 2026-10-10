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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Simp_tryTheorem_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_deltaExpand(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
static const lean_closure_object l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3_ = stack[0].m_obj;
lean_object* v_a_4_ = stack[1].m_obj;
lean_object* v_a_5_ = stack[2].m_obj;
lean_object* v_res_54_;
v_res_54_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_54_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___boxed(lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_55_, v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec_ref(v_a_55_);
return v_res_59_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_60_, v_a_62_, v_a_63_);
return v___x_65_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_60_ = stack[0].m_obj;
lean_object* v_a_61_ = stack[1].m_obj;
lean_object* v_a_62_ = stack[2].m_obj;
lean_object* v_a_63_ = stack[3].m_obj;
lean_object* v_res_66_;
v_res_66_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(v_a_60_, v_a_61_, v_a_62_, v_a_63_);
stack->m_obj
 = v_res_66_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___boxed(lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(v_a_67_, v_a_68_, v_a_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_a_69_);
lean_dec(v_a_68_);
lean_dec_ref(v_a_67_);
return v_res_72_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(lean_object* v_unfoldThm_75_, lean_object* v_e_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___y_86_; lean_object* v___x_152_; 
lean_inc(v_unfoldThm_75_);
v___x_152_ = l_Lean_Meta_isRflTheorem(v_unfoldThm_75_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_a_153_; lean_object* v___x_154_; 
v_a_153_ = lean_ctor_get(v___x_152_, 0);
lean_inc(v_a_153_);
lean_dec_ref_known(v___x_152_, 1);
lean_inc(v_unfoldThm_75_);
v___x_154_ = l_Lean_Meta_isBackwardRflTheorem(v_unfoldThm_75_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v_transparency_159_; uint8_t v___x_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; uint8_t v___x_167_; uint8_t v___x_168_; uint8_t v___x_169_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref_known(v___x_154_, 1);
v___x_156_ = lean_box(0);
lean_inc(v_unfoldThm_75_);
v___x_157_ = l_Lean_mkConst(v_unfoldThm_75_, v___x_156_);
v___x_158_ = l_Lean_Meta_Context_config(v_a_80_);
v_transparency_159_ = lean_ctor_get_uint8(v___x_158_, 9);
lean_dec_ref(v___x_158_);
v___x_160_ = 1;
v___x_161_ = 0;
v___x_162_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_162_, 0, v_unfoldThm_75_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1, v___x_160_);
lean_ctor_set_uint8(v___x_162_, sizeof(void*)*1 + 1, v___x_161_);
v___x_163_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0));
v___x_164_ = lean_unsigned_to_nat(1000u);
v___x_165_ = lean_alloc_ctor(0, 5, 4);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_163_);
lean_ctor_set(v___x_165_, 2, v___x_157_);
lean_ctor_set(v___x_165_, 3, v___x_164_);
lean_ctor_set(v___x_165_, 4, v___x_162_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5, v___x_160_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5 + 1, v___x_161_);
v___x_166_ = lean_unbox(v_a_153_);
lean_dec(v_a_153_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5 + 2, v___x_166_);
v___x_167_ = lean_unbox(v_a_155_);
lean_dec(v_a_155_);
lean_ctor_set_uint8(v___x_165_, sizeof(void*)*5 + 3, v___x_167_);
v___x_168_ = 2;
v___x_169_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_159_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v_keyedConfig_170_; uint8_t v_trackZetaDelta_171_; lean_object* v_zetaDeltaSet_172_; lean_object* v_lctx_173_; lean_object* v_localInstances_174_; lean_object* v_defEqCtx_x3f_175_; lean_object* v_synthPendingDepth_176_; lean_object* v_customCanUnfoldPredicate_x3f_177_; uint8_t v_univApprox_178_; uint8_t v_inTypeClassResolution_179_; uint8_t v_cacheInferType_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v_keyedConfig_170_ = lean_ctor_get(v_a_80_, 0);
v_trackZetaDelta_171_ = lean_ctor_get_uint8(v_a_80_, sizeof(void*)*7);
v_zetaDeltaSet_172_ = lean_ctor_get(v_a_80_, 1);
v_lctx_173_ = lean_ctor_get(v_a_80_, 2);
v_localInstances_174_ = lean_ctor_get(v_a_80_, 3);
v_defEqCtx_x3f_175_ = lean_ctor_get(v_a_80_, 4);
v_synthPendingDepth_176_ = lean_ctor_get(v_a_80_, 5);
v_customCanUnfoldPredicate_x3f_177_ = lean_ctor_get(v_a_80_, 6);
v_univApprox_178_ = lean_ctor_get_uint8(v_a_80_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_179_ = lean_ctor_get_uint8(v_a_80_, sizeof(void*)*7 + 2);
v_cacheInferType_180_ = lean_ctor_get_uint8(v_a_80_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_170_);
v___x_181_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_168_, v_keyedConfig_170_);
lean_inc(v_customCanUnfoldPredicate_x3f_177_);
lean_inc(v_synthPendingDepth_176_);
lean_inc(v_defEqCtx_x3f_175_);
lean_inc_ref(v_localInstances_174_);
lean_inc_ref(v_lctx_173_);
lean_inc(v_zetaDeltaSet_172_);
v___x_182_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_zetaDeltaSet_172_);
lean_ctor_set(v___x_182_, 2, v_lctx_173_);
lean_ctor_set(v___x_182_, 3, v_localInstances_174_);
lean_ctor_set(v___x_182_, 4, v_defEqCtx_x3f_175_);
lean_ctor_set(v___x_182_, 5, v_synthPendingDepth_176_);
lean_ctor_set(v___x_182_, 6, v_customCanUnfoldPredicate_x3f_177_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*7, v_trackZetaDelta_171_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*7 + 1, v_univApprox_178_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*7 + 2, v_inTypeClassResolution_179_);
lean_ctor_set_uint8(v___x_182_, sizeof(void*)*7 + 3, v_cacheInferType_180_);
v___x_183_ = l_Lean_Meta_Simp_tryTheorem_x3f(v_e_76_, v___x_165_, v_a_77_, v_a_78_, v_a_79_, v___x_182_, v_a_81_, v_a_82_, v_a_83_);
lean_dec_ref_known(v___x_182_, 7);
v___y_86_ = v___x_183_;
goto v___jp_85_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Simp_tryTheorem_x3f(v_e_76_, v___x_165_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
v___y_86_ = v___x_184_;
goto v___jp_85_;
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec(v_a_153_);
lean_dec_ref(v_e_76_);
lean_dec(v_unfoldThm_75_);
v_a_185_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_154_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_154_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_e_76_);
lean_dec(v_unfoldThm_75_);
v_a_193_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_152_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_152_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
v___jp_85_:
{
if (lean_obj_tag(v___y_86_) == 0)
{
lean_object* v_a_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_143_; 
v_a_87_ = lean_ctor_get(v___y_86_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___y_86_);
if (v_isSharedCheck_143_ == 0)
{
v___x_89_ = v___y_86_;
v_isShared_90_ = v_isSharedCheck_143_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_a_87_);
lean_dec(v___y_86_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_143_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
if (lean_obj_tag(v_a_87_) == 0)
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_91_, 0, v_a_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
else
{
lean_object* v_val_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_142_; 
lean_del_object(v___x_89_);
v_val_95_ = lean_ctor_get(v_a_87_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v_a_87_);
if (v_isSharedCheck_142_ == 0)
{
v___x_97_ = v_a_87_;
v_isShared_98_ = v_isSharedCheck_142_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_val_95_);
lean_dec(v_a_87_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_142_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v_expr_99_; lean_object* v_proof_x3f_100_; uint8_t v_cache_101_; lean_object* v___x_102_; 
v_expr_99_ = lean_ctor_get(v_val_95_, 0);
v_proof_x3f_100_ = lean_ctor_get(v_val_95_, 1);
v_cache_101_ = lean_ctor_get_uint8(v_val_95_, sizeof(void*)*2);
v___x_102_ = l_Lean_Meta_reduceMatcher_x3f(v_expr_99_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_133_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_133_ == 0)
{
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_133_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_a_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_133_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
if (lean_obj_tag(v_a_103_) == 0)
{
lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_124_; 
lean_inc(v_proof_x3f_100_);
lean_del_object(v___x_97_);
v_isSharedCheck_124_ = !lean_is_exclusive(v_val_95_);
if (v_isSharedCheck_124_ == 0)
{
lean_object* v_unused_125_; lean_object* v_unused_126_; 
v_unused_125_ = lean_ctor_get(v_val_95_, 1);
lean_dec(v_unused_125_);
v_unused_126_ = lean_ctor_get(v_val_95_, 0);
lean_dec(v_unused_126_);
v___x_108_ = v_val_95_;
v_isShared_109_ = v_isSharedCheck_124_;
goto v_resetjp_107_;
}
else
{
lean_dec(v_val_95_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_124_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v_val_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_123_; 
v_val_110_ = lean_ctor_get(v_a_103_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v_a_103_);
if (v_isSharedCheck_123_ == 0)
{
v___x_112_ = v_a_103_;
v_isShared_113_ = v_isSharedCheck_123_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_val_110_);
lean_dec(v_a_103_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_123_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v_val_110_);
v___x_115_ = v___x_108_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_val_110_);
lean_ctor_set(v_reuseFailAlloc_122_, 1, v_proof_x3f_100_);
lean_ctor_set_uint8(v_reuseFailAlloc_122_, sizeof(void*)*2, v_cache_101_);
v___x_115_ = v_reuseFailAlloc_122_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_117_; 
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_115_);
v___x_117_ = v___x_112_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_115_);
v___x_117_ = v_reuseFailAlloc_121_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_119_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_117_);
v___x_119_ = v___x_105_;
goto v_reusejp_118_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_117_);
v___x_119_ = v_reuseFailAlloc_120_;
goto v_reusejp_118_;
}
v_reusejp_118_:
{
return v___x_119_;
}
}
}
}
}
}
else
{
lean_object* v___x_128_; 
lean_dec(v_a_103_);
if (v_isShared_98_ == 0)
{
lean_ctor_set_tag(v___x_97_, 0);
v___x_128_ = v___x_97_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_val_95_);
v___x_128_ = v_reuseFailAlloc_132_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_130_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_128_);
v___x_130_ = v___x_105_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_del_object(v___x_97_);
lean_dec(v_val_95_);
v_a_134_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_102_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_102_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
v_a_144_ = lean_ctor_get(v___y_86_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___y_86_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___y_86_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___y_86_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre_0interp(lean_interpreter_value* stack)
{
lean_object* v_unfoldThm_75_ = stack[0].m_obj;
lean_object* v_e_76_ = stack[1].m_obj;
lean_object* v_a_77_ = stack[2].m_obj;
lean_object* v_a_78_ = stack[3].m_obj;
lean_object* v_a_79_ = stack[4].m_obj;
lean_object* v_a_80_ = stack[5].m_obj;
lean_object* v_a_81_ = stack[6].m_obj;
lean_object* v_a_82_ = stack[7].m_obj;
lean_object* v_a_83_ = stack[8].m_obj;
lean_object* v_res_201_;
v_res_201_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(v_unfoldThm_75_, v_e_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
stack->m_obj
 = v_res_201_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed(lean_object* v_unfoldThm_202_, lean_object* v_e_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(v_unfoldThm_202_, v_e_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_, v_a_208_, v_a_209_, v_a_210_);
lean_dec(v_a_210_);
lean_dec_ref(v_a_209_);
lean_dec(v_a_208_);
lean_dec_ref(v_a_207_);
lean_dec(v_a_206_);
lean_dec_ref(v_a_205_);
lean_dec(v_a_204_);
return v_res_212_;
}
}
lean_object* l_Lean_Meta_unfold___lam__0(lean_object* v_e_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_){
_start:
{
lean_object* v___x_222_; uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = lean_box(0);
v___x_223_ = 1;
v___x_224_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_224_, 0, v_e_213_);
lean_ctor_set(v___x_224_, 1, v___x_222_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*2, v___x_223_);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfold___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_213_ = stack[0].m_obj;
lean_object* v___y_214_ = stack[1].m_obj;
lean_object* v___y_215_ = stack[2].m_obj;
lean_object* v___y_216_ = stack[3].m_obj;
lean_object* v___y_217_ = stack[4].m_obj;
lean_object* v___y_218_ = stack[5].m_obj;
lean_object* v___y_219_ = stack[6].m_obj;
lean_object* v___y_220_ = stack[7].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Lean_Meta_unfold___lam__0(v_e_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0___boxed(lean_object* v_e_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Meta_unfold___lam__0(v_e_228_, v___y_229_, v___y_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v___y_229_);
return v_res_237_;
}
}
lean_object* l_Lean_Meta_unfold___lam__1(lean_object* v_x_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = ((lean_object*)(l_Lean_Meta_unfold___lam__1___closed__0));
v___x_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfold___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_240_ = stack[0].m_obj;
lean_object* v___y_241_ = stack[1].m_obj;
lean_object* v___y_242_ = stack[2].m_obj;
lean_object* v___y_243_ = stack[3].m_obj;
lean_object* v___y_244_ = stack[4].m_obj;
lean_object* v___y_245_ = stack[5].m_obj;
lean_object* v___y_246_ = stack[6].m_obj;
lean_object* v___y_247_ = stack[7].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_Lean_Meta_unfold___lam__1(v_x_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1___boxed(lean_object* v_x_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Meta_unfold___lam__1(v_x_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v_x_252_);
return v_res_261_;
}
}
lean_object* l_Lean_Meta_unfold___lam__2(lean_object* v_e_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_271_, 0, v_e_262_);
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfold___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_262_ = stack[0].m_obj;
lean_object* v___y_263_ = stack[1].m_obj;
lean_object* v___y_264_ = stack[2].m_obj;
lean_object* v___y_265_ = stack[3].m_obj;
lean_object* v___y_266_ = stack[4].m_obj;
lean_object* v___y_267_ = stack[5].m_obj;
lean_object* v___y_268_ = stack[6].m_obj;
lean_object* v___y_269_ = stack[7].m_obj;
lean_object* v_res_273_;
v_res_273_ = l_Lean_Meta_unfold___lam__2(v_e_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_);
stack->m_obj
 = v_res_273_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2___boxed(lean_object* v_e_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Meta_unfold___lam__2(v_e_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_);
lean_dec(v___y_281_);
lean_dec_ref(v___y_280_);
lean_dec(v___y_279_);
lean_dec_ref(v___y_278_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
return v_res_283_;
}
}
lean_object* l_Lean_Meta_unfold___lam__3(lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfold___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_284_ = stack[0].m_obj;
lean_object* v___y_285_ = stack[1].m_obj;
lean_object* v___y_286_ = stack[2].m_obj;
lean_object* v___y_287_ = stack[3].m_obj;
lean_object* v___y_288_ = stack[4].m_obj;
lean_object* v___y_289_ = stack[5].m_obj;
lean_object* v___y_290_ = stack[6].m_obj;
lean_object* v___y_291_ = stack[7].m_obj;
lean_object* v_res_295_;
v_res_295_ = l_Lean_Meta_unfold___lam__3(v_x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
stack->m_obj
 = v_res_295_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3___boxed(lean_object* v_x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_Meta_unfold___lam__3(v_x_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v_x_296_);
return v_res_305_;
}
}
uint8_t l_Lean_Meta_unfold___lam__4(lean_object* v_declName_306_, lean_object* v_x_307_){
_start:
{
uint8_t v___x_308_; 
v___x_308_ = lean_name_eq(v_x_307_, v_declName_306_);
return v___x_308_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfold___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_306_ = stack[0].m_obj;
lean_object* v_x_307_ = stack[1].m_obj;
uint8_t v_res_309_;
v_res_309_ = l_Lean_Meta_unfold___lam__4(v_declName_306_, v_x_307_);
stack->m_num = v_res_309_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__4___boxed(lean_object* v_declName_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = l_Lean_Meta_unfold___lam__4(v_declName_310_, v_x_311_);
lean_dec(v_x_311_);
lean_dec(v_declName_310_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__4(void){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__5(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_obj_once(&l_Lean_Meta_unfold___closed__4, &l_Lean_Meta_unfold___closed__4_once, _init_l_Lean_Meta_unfold___closed__4);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__6(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__7(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_324_ = lean_unsigned_to_nat(32u);
v___x_325_ = lean_mk_empty_array_with_capacity(v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__8(void){
_start:
{
size_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_327_ = ((size_t)5ULL);
v___x_328_ = lean_unsigned_to_nat(0u);
v___x_329_ = lean_unsigned_to_nat(32u);
v___x_330_ = lean_mk_empty_array_with_capacity(v___x_329_);
v___x_331_ = lean_obj_once(&l_Lean_Meta_unfold___closed__7, &l_Lean_Meta_unfold___closed__7_once, _init_l_Lean_Meta_unfold___closed__7);
v___x_332_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_332_, 0, v___x_331_);
lean_ctor_set(v___x_332_, 1, v___x_330_);
lean_ctor_set(v___x_332_, 2, v___x_328_);
lean_ctor_set(v___x_332_, 3, v___x_328_);
lean_ctor_set_usize(v___x_332_, 4, v___x_327_);
return v___x_332_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__9(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_333_ = lean_obj_once(&l_Lean_Meta_unfold___closed__8, &l_Lean_Meta_unfold___closed__8_once, _init_l_Lean_Meta_unfold___closed__8);
v___x_334_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_334_);
lean_ctor_set(v___x_335_, 2, v___x_334_);
lean_ctor_set(v___x_335_, 3, v___x_333_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__10(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_obj_once(&l_Lean_Meta_unfold___closed__9, &l_Lean_Meta_unfold___closed__9_once, _init_l_Lean_Meta_unfold___closed__9);
v___x_337_ = lean_obj_once(&l_Lean_Meta_unfold___closed__6, &l_Lean_Meta_unfold___closed__6_once, _init_l_Lean_Meta_unfold___closed__6);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
return v___x_338_;
}
}
lean_object* l_Lean_Meta_unfold(lean_object* v_e_339_, lean_object* v_declName_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___f_346_; lean_object* v___f_347_; lean_object* v___f_348_; lean_object* v___f_349_; lean_object* v___f_350_; uint8_t v___x_351_; lean_object* v___x_352_; 
v___f_346_ = ((lean_object*)(l_Lean_Meta_unfold___closed__0));
v___f_347_ = ((lean_object*)(l_Lean_Meta_unfold___closed__1));
v___f_348_ = ((lean_object*)(l_Lean_Meta_unfold___closed__2));
v___f_349_ = ((lean_object*)(l_Lean_Meta_unfold___closed__3));
lean_inc(v_declName_340_);
v___f_350_ = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__4___boxed), 2, 1);
lean_closure_set(v___f_350_, 0, v_declName_340_);
v___x_351_ = 0;
v___x_352_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_340_, v___x_351_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
if (lean_obj_tag(v_a_353_) == 1)
{
lean_object* v_val_354_; lean_object* v___x_355_; 
lean_dec_ref(v___f_350_);
v_val_354_ = lean_ctor_get(v_a_353_, 0);
lean_inc(v_val_354_);
lean_dec_ref_known(v_a_353_, 1);
v___x_355_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_341_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; uint8_t v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = lean_obj_once(&l_Lean_Meta_unfold___closed__10, &l_Lean_Meta_unfold___closed__10_once, _init_l_Lean_Meta_unfold___closed__10);
v___x_358_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed), 10, 1);
lean_closure_set(v___x_358_, 0, v_val_354_);
v___x_359_ = 1;
v___x_360_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___f_346_);
lean_ctor_set(v___x_360_, 2, v___f_347_);
lean_ctor_set(v___x_360_, 3, v___f_348_);
lean_ctor_set(v___x_360_, 4, v___f_349_);
lean_ctor_set_uint8(v___x_360_, sizeof(void*)*5, v___x_359_);
v___x_361_ = l_Lean_Meta_Simp_main(v_e_339_, v_a_356_, v___x_357_, v___x_360_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_370_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_370_ == 0)
{
v___x_364_ = v___x_361_;
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_361_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_370_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v_fst_366_; lean_object* v___x_368_; 
v_fst_366_ = lean_ctor_get(v_a_362_, 0);
lean_inc(v_fst_366_);
lean_dec(v_a_362_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v_fst_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_fst_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
v_a_371_ = lean_ctor_get(v___x_361_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_361_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_361_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
}
else
{
lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_386_; 
lean_dec(v_val_354_);
lean_dec_ref(v_e_339_);
v_a_379_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_386_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_386_ == 0)
{
v___x_381_ = v___x_355_;
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_dec(v___x_355_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_386_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_382_ == 0)
{
v___x_384_ = v___x_381_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_385_; 
v_reuseFailAlloc_385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_385_, 0, v_a_379_);
v___x_384_ = v_reuseFailAlloc_385_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
return v___x_384_;
}
}
}
}
else
{
lean_object* v___x_387_; 
lean_dec(v_a_353_);
v___x_387_ = l_Lean_Meta_deltaExpand(v_e_339_, v___f_350_, v___x_351_, v_a_343_, v_a_344_);
if (lean_obj_tag(v___x_387_) == 0)
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_398_; 
v_a_388_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_398_ == 0)
{
v___x_390_ = v___x_387_;
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_387_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_398_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_392_; uint8_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_396_; 
v___x_392_ = lean_box(0);
v___x_393_ = 1;
v___x_394_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_394_, 0, v_a_388_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*2, v___x_393_);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 0, v___x_394_);
v___x_396_ = v___x_390_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v___x_394_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_387_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_387_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_387_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_387_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_414_; 
lean_dec_ref(v___f_350_);
lean_dec_ref(v_e_339_);
v_a_407_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_414_ == 0)
{
v___x_409_ = v___x_352_;
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_352_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_414_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_412_; 
if (v_isShared_410_ == 0)
{
v___x_412_ = v___x_409_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_a_407_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_unfold_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_339_ = stack[0].m_obj;
lean_object* v_declName_340_ = stack[1].m_obj;
lean_object* v_a_341_ = stack[2].m_obj;
lean_object* v_a_342_ = stack[3].m_obj;
lean_object* v_a_343_ = stack[4].m_obj;
lean_object* v_a_344_ = stack[5].m_obj;
lean_object* v_res_415_;
v_res_415_ = l_Lean_Meta_unfold(v_e_339_, v_declName_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_);
stack->m_obj
 = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___boxed(lean_object* v_e_416_, lean_object* v_declName_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_unfold(v_e_416_, v_declName_417_, v_a_418_, v_a_419_, v_a_420_, v_a_421_);
lean_dec(v_a_421_);
lean_dec_ref(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_a_418_);
return v_res_423_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(lean_object* v_e_424_, lean_object* v___y_425_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = l_Lean_Expr_hasMVar(v_e_424_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_e_424_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v_mctx_430_; lean_object* v___x_431_; lean_object* v_fst_432_; lean_object* v_snd_433_; lean_object* v___x_434_; lean_object* v_cache_435_; lean_object* v_zetaDeltaFVarIds_436_; lean_object* v_postponed_437_; lean_object* v_diag_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_447_; 
v___x_429_ = lean_st_ref_get(v___y_425_);
v_mctx_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc_ref(v_mctx_430_);
lean_dec(v___x_429_);
v___x_431_ = l_Lean_instantiateMVarsCore(v_mctx_430_, v_e_424_);
v_fst_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_fst_432_);
v_snd_433_ = lean_ctor_get(v___x_431_, 1);
lean_inc(v_snd_433_);
lean_dec_ref(v___x_431_);
v___x_434_ = lean_st_ref_take(v___y_425_);
v_cache_435_ = lean_ctor_get(v___x_434_, 1);
v_zetaDeltaFVarIds_436_ = lean_ctor_get(v___x_434_, 2);
v_postponed_437_ = lean_ctor_get(v___x_434_, 3);
v_diag_438_ = lean_ctor_get(v___x_434_, 4);
v_isSharedCheck_447_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v___x_434_, 0);
lean_dec(v_unused_448_);
v___x_440_ = v___x_434_;
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_diag_438_);
lean_inc(v_postponed_437_);
lean_inc(v_zetaDeltaFVarIds_436_);
lean_inc(v_cache_435_);
lean_dec(v___x_434_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_447_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_443_; 
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_snd_433_);
v___x_443_ = v___x_440_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_snd_433_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v_cache_435_);
lean_ctor_set(v_reuseFailAlloc_446_, 2, v_zetaDeltaFVarIds_436_);
lean_ctor_set(v_reuseFailAlloc_446_, 3, v_postponed_437_);
lean_ctor_set(v_reuseFailAlloc_446_, 4, v_diag_438_);
v___x_443_ = v_reuseFailAlloc_446_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_444_ = lean_st_ref_put(v___y_425_, v___x_443_);
v___x_445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_445_, 0, v_fst_432_);
return v___x_445_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_424_ = stack[0].m_obj;
lean_object* v___y_425_ = stack[1].m_obj;
lean_object* v_res_449_;
v_res_449_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_424_, v___y_425_);
stack->m_obj
 = v_res_449_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg___boxed(lean_object* v_e_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_450_, v___y_451_);
lean_dec(v___y_451_);
return v_res_453_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(lean_object* v_e_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_454_, v___y_456_);
return v___x_460_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_454_ = stack[0].m_obj;
lean_object* v___y_455_ = stack[1].m_obj;
lean_object* v___y_456_ = stack[2].m_obj;
lean_object* v___y_457_ = stack[3].m_obj;
lean_object* v___y_458_ = stack[4].m_obj;
lean_object* v_res_461_;
v_res_461_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(v_e_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___boxed(lean_object* v_e_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(v_e_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
return v_res_468_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(lean_object* v_mvarId_469_, lean_object* v_x_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_469_, v_x_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_484_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_484_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_484_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_484_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_482_; 
if (v_isShared_480_ == 0)
{
v___x_482_ = v___x_479_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_a_477_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
return v___x_482_;
}
}
}
else
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_492_; 
v_a_485_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_492_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_492_ == 0)
{
v___x_487_ = v___x_476_;
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_476_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_492_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_490_; 
if (v_isShared_488_ == 0)
{
v___x_490_ = v___x_487_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_485_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_469_ = stack[0].m_obj;
lean_object* v_x_470_ = stack[1].m_obj;
lean_object* v___y_471_ = stack[2].m_obj;
lean_object* v___y_472_ = stack[3].m_obj;
lean_object* v___y_473_ = stack[4].m_obj;
lean_object* v___y_474_ = stack[5].m_obj;
lean_object* v_res_493_;
v_res_493_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_469_, v_x_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
stack->m_obj
 = v_res_493_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg___boxed(lean_object* v_mvarId_494_, lean_object* v_x_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_494_, v_x_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_501_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(lean_object* v_00_u03b1_502_, lean_object* v_mvarId_503_, lean_object* v_x_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_503_, v_x_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
return v___x_510_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_503_ = stack[1].m_obj;
lean_object* v_x_504_ = stack[2].m_obj;
lean_object* v___y_505_ = stack[3].m_obj;
lean_object* v___y_506_ = stack[4].m_obj;
lean_object* v___y_507_ = stack[5].m_obj;
lean_object* v___y_508_ = stack[6].m_obj;
lean_object* v_res_511_;
v_res_511_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(lean_box(0), v_mvarId_503_, v_x_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
stack->m_obj
 = v_res_511_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___boxed(lean_object* v_00_u03b1_512_, lean_object* v_mvarId_513_, lean_object* v_x_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(v_00_u03b1_512_, v_mvarId_513_, v_x_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec_ref(v___y_515_);
return v_res_520_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(lean_object* v_msgData_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v___x_527_; lean_object* v_env_528_; uint8_t v___x_529_; lean_object* v_env_530_; lean_object* v___x_531_; lean_object* v_toCold_532_; lean_object* v_mctx_533_; lean_object* v_lctx_534_; lean_object* v_options_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_527_ = lean_st_ref_get(v___y_525_);
v_env_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc_ref(v_env_528_);
lean_dec(v___x_527_);
v___x_529_ = 0;
v_env_530_ = l_Lean_Environment_setRecordingDeps(v_env_528_, v___x_529_);
v___x_531_ = lean_st_ref_get(v___y_523_);
v_toCold_532_ = lean_ctor_get(v___y_524_, 0);
v_mctx_533_ = lean_ctor_get(v___x_531_, 0);
lean_inc_ref(v_mctx_533_);
lean_dec(v___x_531_);
v_lctx_534_ = lean_ctor_get(v___y_522_, 2);
v_options_535_ = lean_ctor_get(v_toCold_532_, 2);
lean_inc_ref(v_options_535_);
lean_inc_ref(v_lctx_534_);
v___x_536_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_536_, 0, v_env_530_);
lean_ctor_set(v___x_536_, 1, v_mctx_533_);
lean_ctor_set(v___x_536_, 2, v_lctx_534_);
lean_ctor_set(v___x_536_, 3, v_options_535_);
v___x_537_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_msgData_521_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_521_ = stack[0].m_obj;
lean_object* v___y_522_ = stack[1].m_obj;
lean_object* v___y_523_ = stack[2].m_obj;
lean_object* v___y_524_ = stack[3].m_obj;
lean_object* v___y_525_ = stack[4].m_obj;
lean_object* v_res_539_;
v_res_539_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msgData_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_);
stack->m_obj
 = v_res_539_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1___boxed(lean_object* v_msgData_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msgData_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_546_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(lean_object* v_msg_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_ref_553_; lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_563_; 
v_ref_553_ = lean_ctor_get(v___y_550_, 2);
v___x_554_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
v_a_555_ = lean_ctor_get(v___x_554_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_563_ == 0)
{
v___x_557_ = v___x_554_;
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_554_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_563_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_559_; lean_object* v___x_561_; 
lean_inc(v_ref_553_);
v___x_559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_559_, 0, v_ref_553_);
lean_ctor_set(v___x_559_, 1, v_a_555_);
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 1);
lean_ctor_set(v___x_557_, 0, v___x_559_);
v___x_561_ = v___x_557_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
return v___x_561_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_547_ = stack[0].m_obj;
lean_object* v___y_548_ = stack[1].m_obj;
lean_object* v___y_549_ = stack[2].m_obj;
lean_object* v___y_550_ = stack[3].m_obj;
lean_object* v___y_551_ = stack[4].m_obj;
lean_object* v_res_564_;
v_res_564_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
stack->m_obj
 = v_res_564_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg___boxed(lean_object* v_msg_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
lean_dec(v___y_567_);
lean_dec_ref(v___y_566_);
return v_res_571_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_Meta_unfoldTarget___lam__0___closed__0));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_Meta_unfoldTarget___lam__0___closed__2));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
lean_object* l_Lean_Meta_unfoldTarget___lam__0(lean_object* v_mvarId_578_, lean_object* v_declName_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v___x_585_; 
lean_inc(v_mvarId_578_);
v___x_585_ = l_Lean_MVarId_getType(v_mvarId_578_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_a_586_; lean_object* v___x_587_; lean_object* v_a_588_; lean_object* v___x_589_; 
v_a_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_a_586_);
lean_dec_ref_known(v___x_585_, 1);
v___x_587_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_586_, v___y_581_);
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc_n(v_a_588_, 2);
lean_dec_ref(v___x_587_);
lean_inc(v_declName_579_);
v___x_589_ = l_Lean_Meta_unfold(v_a_588_, v_declName_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v_expr_591_; uint8_t v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref_known(v___x_589_, 1);
v_expr_591_ = lean_ctor_get(v_a_590_, 0);
v___x_592_ = lean_expr_eqv(v_expr_591_, v_a_588_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; 
lean_dec(v_declName_579_);
v___x_593_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_578_, v_a_588_, v_a_590_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v_a_588_);
return v___x_593_;
}
else
{
lean_object* v___x_594_; uint8_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
lean_dec(v_a_590_);
lean_dec(v_mvarId_578_);
v___x_594_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_595_ = 0;
v___x_596_ = l_Lean_MessageData_ofConstName(v_declName_579_, v___x_595_);
v___x_597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_594_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
v___x_598_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
v___x_600_ = l_Lean_indentExpr(v_a_588_);
v___x_601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_599_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_601_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
lean_dec(v_a_588_);
lean_dec(v_declName_579_);
lean_dec(v_mvarId_578_);
v_a_611_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_589_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_589_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
else
{
lean_object* v_a_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_626_; 
lean_dec(v_declName_579_);
lean_dec(v_mvarId_578_);
v_a_619_ = lean_ctor_get(v___x_585_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_626_ == 0)
{
v___x_621_ = v___x_585_;
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_a_619_);
lean_dec(v___x_585_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_626_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_624_; 
if (v_isShared_622_ == 0)
{
v___x_624_ = v___x_621_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_a_619_);
v___x_624_ = v_reuseFailAlloc_625_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
return v___x_624_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldTarget___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_578_ = stack[0].m_obj;
lean_object* v_declName_579_ = stack[1].m_obj;
lean_object* v___y_580_ = stack[2].m_obj;
lean_object* v___y_581_ = stack[3].m_obj;
lean_object* v___y_582_ = stack[4].m_obj;
lean_object* v___y_583_ = stack[5].m_obj;
lean_object* v_res_627_;
v_res_627_ = l_Lean_Meta_unfoldTarget___lam__0(v_mvarId_578_, v_declName_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0___boxed(lean_object* v_mvarId_628_, lean_object* v_declName_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_Meta_unfoldTarget___lam__0(v_mvarId_628_, v_declName_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_635_;
}
}
lean_object* l_Lean_Meta_unfoldTarget(lean_object* v_mvarId_636_, lean_object* v_declName_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v___f_643_; lean_object* v___x_644_; 
lean_inc(v_mvarId_636_);
v___f_643_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_643_, 0, v_mvarId_636_);
lean_closure_set(v___f_643_, 1, v_declName_637_);
v___x_644_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_636_, v___f_643_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
return v___x_644_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_636_ = stack[0].m_obj;
lean_object* v_declName_637_ = stack[1].m_obj;
lean_object* v_a_638_ = stack[2].m_obj;
lean_object* v_a_639_ = stack[3].m_obj;
lean_object* v_a_640_ = stack[4].m_obj;
lean_object* v_a_641_ = stack[5].m_obj;
lean_object* v_res_645_;
v_res_645_ = l_Lean_Meta_unfoldTarget(v_mvarId_636_, v_declName_637_, v_a_638_, v_a_639_, v_a_640_, v_a_641_);
stack->m_obj
 = v_res_645_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___boxed(lean_object* v_mvarId_646_, lean_object* v_declName_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Meta_unfoldTarget(v_mvarId_646_, v_declName_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_);
lean_dec(v_a_651_);
lean_dec_ref(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
return v_res_653_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(lean_object* v_00_u03b1_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_661_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_655_ = stack[1].m_obj;
lean_object* v___y_656_ = stack[2].m_obj;
lean_object* v___y_657_ = stack[3].m_obj;
lean_object* v___y_658_ = stack[4].m_obj;
lean_object* v___y_659_ = stack[5].m_obj;
lean_object* v_res_662_;
v_res_662_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(lean_box(0), v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
stack->m_obj
 = v_res_662_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___boxed(lean_object* v_00_u03b1_663_, lean_object* v_msg_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v_res_670_; 
v_res_670_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(v_00_u03b1_663_, v_msg_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_);
lean_dec(v___y_668_);
lean_dec_ref(v___y_667_);
lean_dec(v___y_666_);
lean_dec_ref(v___y_665_);
return v_res_670_;
}
}
lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(lean_object* v_msg_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v___f_678_; lean_object* v___x_784__overap_679_; lean_object* v___x_680_; 
v___f_678_ = ((lean_object*)(l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0));
v___x_784__overap_679_ = lean_panic_fn_borrowed(v___f_678_, v_msg_672_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc_ref(v___y_673_);
v___x_680_ = lean_apply_5(v___x_784__overap_679_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, lean_box(0));
return v___x_680_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_672_ = stack[0].m_obj;
lean_object* v___y_673_ = stack[1].m_obj;
lean_object* v___y_674_ = stack[2].m_obj;
lean_object* v___y_675_ = stack[3].m_obj;
lean_object* v___y_676_ = stack[4].m_obj;
lean_object* v_res_681_;
v_res_681_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v_msg_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
stack->m_obj
 = v_res_681_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___boxed(lean_object* v_msg_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v_msg_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
return v_res_688_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_692_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2));
v___x_693_ = lean_unsigned_to_nat(94u);
v___x_694_ = lean_unsigned_to_nat(43u);
v___x_695_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1));
v___x_696_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0));
v___x_697_ = l_mkPanicMessageWithDecl(v___x_696_, v___x_695_, v___x_694_, v___x_693_, v___x_692_);
return v___x_697_;
}
}
lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0(lean_object* v_fvarId_698_, lean_object* v_declName_699_, lean_object* v_mvarId_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; 
lean_inc(v_fvarId_698_);
v___x_706_ = l_Lean_FVarId_getType___redArg(v_fvarId_698_, v___y_701_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_708_; lean_object* v_a_709_; lean_object* v___x_710_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc_n(v_a_707_, 2);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_707_, v___y_702_);
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_a_709_);
lean_dec_ref(v___x_708_);
lean_inc(v_declName_699_);
v___x_710_ = l_Lean_Meta_unfold(v_a_709_, v_declName_699_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v_expr_739_; uint8_t v___x_740_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref_known(v___x_710_, 1);
v_expr_739_ = lean_ctor_get(v_a_711_, 0);
v___x_740_ = lean_expr_eqv(v_expr_739_, v_a_707_);
if (v___x_740_ == 0)
{
lean_dec(v_a_707_);
lean_dec(v_declName_699_);
v___y_713_ = v___y_701_;
v___y_714_ = v___y_702_;
v___y_715_ = v___y_703_;
v___y_716_ = v___y_704_;
goto v___jp_712_;
}
else
{
lean_object* v___x_741_; uint8_t v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v_a_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_757_; 
lean_dec(v_a_711_);
lean_dec(v_mvarId_700_);
lean_dec(v_fvarId_698_);
v___x_741_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_742_ = 0;
v___x_743_ = l_Lean_MessageData_ofConstName(v_declName_699_, v___x_742_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_741_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_744_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = l_Lean_indentExpr(v_a_707_);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_748_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
v_a_750_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_757_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_757_ == 0)
{
v___x_752_ = v___x_749_;
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_a_750_);
lean_dec(v___x_749_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_757_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_755_; 
if (v_isShared_753_ == 0)
{
v___x_755_ = v___x_752_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_a_750_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
v___jp_712_:
{
uint8_t v___x_717_; lean_object* v___x_718_; 
v___x_717_ = 0;
v___x_718_ = l_Lean_Meta_applySimpResultToLocalDecl(v_mvarId_700_, v_fvarId_698_, v_a_711_, v___x_717_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_730_; 
v_a_719_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_730_ == 0)
{
v___x_721_ = v___x_718_;
v_isShared_722_ = v_isSharedCheck_730_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_718_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_730_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
if (lean_obj_tag(v_a_719_) == 1)
{
lean_object* v_val_723_; lean_object* v_snd_724_; lean_object* v___x_726_; 
v_val_723_ = lean_ctor_get(v_a_719_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v_a_719_, 1);
v_snd_724_ = lean_ctor_get(v_val_723_, 1);
lean_inc(v_snd_724_);
lean_dec(v_val_723_);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 0, v_snd_724_);
v___x_726_ = v___x_721_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_snd_724_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; 
lean_del_object(v___x_721_);
lean_dec(v_a_719_);
v___x_728_ = lean_obj_once(&l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3, &l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3);
v___x_729_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v___x_728_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
return v___x_729_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
v_a_731_ = lean_ctor_get(v___x_718_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_718_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_718_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v_a_707_);
lean_dec(v_mvarId_700_);
lean_dec(v_declName_699_);
lean_dec(v_fvarId_698_);
v_a_758_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_710_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_710_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v_mvarId_700_);
lean_dec(v_declName_699_);
lean_dec(v_fvarId_698_);
v_a_766_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_706_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_706_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldLocalDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_698_ = stack[0].m_obj;
lean_object* v_declName_699_ = stack[1].m_obj;
lean_object* v_mvarId_700_ = stack[2].m_obj;
lean_object* v___y_701_ = stack[3].m_obj;
lean_object* v___y_702_ = stack[4].m_obj;
lean_object* v___y_703_ = stack[5].m_obj;
lean_object* v___y_704_ = stack[6].m_obj;
lean_object* v_res_774_;
v_res_774_ = l_Lean_Meta_unfoldLocalDecl___lam__0(v_fvarId_698_, v_declName_699_, v_mvarId_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
stack->m_obj
 = v_res_774_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___boxed(lean_object* v_fvarId_775_, lean_object* v_declName_776_, lean_object* v_mvarId_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Meta_unfoldLocalDecl___lam__0(v_fvarId_775_, v_declName_776_, v_mvarId_777_, v___y_778_, v___y_779_, v___y_780_, v___y_781_);
lean_dec(v___y_781_);
lean_dec_ref(v___y_780_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
return v_res_783_;
}
}
lean_object* l_Lean_Meta_unfoldLocalDecl(lean_object* v_mvarId_784_, lean_object* v_fvarId_785_, lean_object* v_declName_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v___f_792_; lean_object* v___x_793_; 
lean_inc(v_mvarId_784_);
v___f_792_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_792_, 0, v_fvarId_785_);
lean_closure_set(v___f_792_, 1, v_declName_786_);
lean_closure_set(v___f_792_, 2, v_mvarId_784_);
v___x_793_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_784_, v___f_792_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
return v___x_793_;
}
}
LEAN_EXPORT void l_Lean_Meta_unfoldLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_784_ = stack[0].m_obj;
lean_object* v_fvarId_785_ = stack[1].m_obj;
lean_object* v_declName_786_ = stack[2].m_obj;
lean_object* v_a_787_ = stack[3].m_obj;
lean_object* v_a_788_ = stack[4].m_obj;
lean_object* v_a_789_ = stack[5].m_obj;
lean_object* v_a_790_ = stack[6].m_obj;
lean_object* v_res_794_;
v_res_794_ = l_Lean_Meta_unfoldLocalDecl(v_mvarId_784_, v_fvarId_785_, v_declName_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_);
stack->m_obj
 = v_res_794_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___boxed(lean_object* v_mvarId_795_, lean_object* v_fvarId_796_, lean_object* v_declName_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Lean_Meta_unfoldLocalDecl(v_mvarId_795_, v_fvarId_796_, v_declName_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
return v_res_803_;
}
}
lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0(lean_object* v_mvarId_804_, lean_object* v_declFVarId_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; 
lean_inc(v_mvarId_804_);
v___x_811_ = l_Lean_MVarId_getType(v_mvarId_804_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_813_; lean_object* v_a_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
lean_inc(v_a_812_);
lean_dec_ref_known(v___x_811_, 1);
v___x_813_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_812_, v___y_807_);
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc_n(v_a_814_, 2);
lean_dec_ref(v___x_813_);
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_mk_empty_array_with_capacity(v___x_815_);
lean_inc(v_declFVarId_805_);
v___x_817_ = lean_array_push(v___x_816_, v_declFVarId_805_);
v___x_818_ = l_Lean_Meta_zetaDeltaFVars(v_a_814_, v___x_817_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; uint8_t v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v___x_820_ = lean_expr_eqv(v_a_819_, v_a_814_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; 
lean_dec(v_a_814_);
lean_dec(v_declFVarId_805_);
v___x_821_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_804_, v_a_819_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec(v_a_819_);
lean_dec(v_mvarId_804_);
v___x_822_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_823_ = l_Lean_Expr_fvar___override(v_declFVarId_805_);
v___x_824_ = l_Lean_MessageData_ofExpr(v___x_823_);
v___x_825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_822_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_825_);
lean_ctor_set(v___x_827_, 1, v___x_826_);
v___x_828_ = l_Lean_indentExpr(v_a_814_);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_829_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_830_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_830_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec(v_a_814_);
lean_dec(v_declFVarId_805_);
lean_dec(v_mvarId_804_);
v_a_839_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_818_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_818_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_object* v_a_847_; lean_object* v___x_849_; uint8_t v_isShared_850_; uint8_t v_isSharedCheck_854_; 
lean_dec(v_declFVarId_805_);
lean_dec(v_mvarId_804_);
v_a_847_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_854_ == 0)
{
v___x_849_ = v___x_811_;
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
else
{
lean_inc(v_a_847_);
lean_dec(v___x_811_);
v___x_849_ = lean_box(0);
v_isShared_850_ = v_isSharedCheck_854_;
goto v_resetjp_848_;
}
v_resetjp_848_:
{
lean_object* v___x_852_; 
if (v_isShared_850_ == 0)
{
v___x_852_ = v___x_849_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_zetaDeltaTarget___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_804_ = stack[0].m_obj;
lean_object* v_declFVarId_805_ = stack[1].m_obj;
lean_object* v___y_806_ = stack[2].m_obj;
lean_object* v___y_807_ = stack[3].m_obj;
lean_object* v___y_808_ = stack[4].m_obj;
lean_object* v___y_809_ = stack[5].m_obj;
lean_object* v_res_855_;
v_res_855_ = l_Lean_Meta_zetaDeltaTarget___lam__0(v_mvarId_804_, v_declFVarId_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
stack->m_obj
 = v_res_855_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0___boxed(lean_object* v_mvarId_856_, lean_object* v_declFVarId_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Meta_zetaDeltaTarget___lam__0(v_mvarId_856_, v_declFVarId_857_, v___y_858_, v___y_859_, v___y_860_, v___y_861_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec(v___y_859_);
lean_dec_ref(v___y_858_);
return v_res_863_;
}
}
lean_object* l_Lean_Meta_zetaDeltaTarget(lean_object* v_mvarId_864_, lean_object* v_declFVarId_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_){
_start:
{
lean_object* v___f_871_; lean_object* v___x_872_; 
lean_inc(v_mvarId_864_);
v___f_871_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_871_, 0, v_mvarId_864_);
lean_closure_set(v___f_871_, 1, v_declFVarId_865_);
v___x_872_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_864_, v___f_871_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
return v___x_872_;
}
}
LEAN_EXPORT void l_Lean_Meta_zetaDeltaTarget_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_864_ = stack[0].m_obj;
lean_object* v_declFVarId_865_ = stack[1].m_obj;
lean_object* v_a_866_ = stack[2].m_obj;
lean_object* v_a_867_ = stack[3].m_obj;
lean_object* v_a_868_ = stack[4].m_obj;
lean_object* v_a_869_ = stack[5].m_obj;
lean_object* v_res_873_;
v_res_873_ = l_Lean_Meta_zetaDeltaTarget(v_mvarId_864_, v_declFVarId_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
stack->m_obj
 = v_res_873_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___boxed(lean_object* v_mvarId_874_, lean_object* v_declFVarId_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_Meta_zetaDeltaTarget(v_mvarId_874_, v_declFVarId_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
return v_res_881_;
}
}
lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0(lean_object* v_fvarId_882_, lean_object* v_declFVarId_883_, lean_object* v_mvarId_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; 
lean_inc(v_fvarId_882_);
v___x_890_ = l_Lean_FVarId_getType___redArg(v_fvarId_882_, v___y_885_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v_a_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc_n(v_a_891_, 2);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_891_, v___y_886_);
v_a_893_ = lean_ctor_get(v___x_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref(v___x_892_);
v___x_894_ = lean_unsigned_to_nat(1u);
v___x_895_ = lean_mk_empty_array_with_capacity(v___x_894_);
v___x_896_ = lean_array_push(v___x_895_, v_declFVarId_883_);
v___x_897_ = l_Lean_Meta_zetaDeltaFVars(v_a_893_, v___x_896_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; uint8_t v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = lean_expr_eqv(v_a_898_, v_a_891_);
if (v___x_899_ == 0)
{
lean_object* v___x_900_; 
lean_dec(v_a_891_);
v___x_900_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_884_, v_fvarId_882_, v_a_898_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
return v___x_900_;
}
else
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_a_898_);
lean_dec(v_mvarId_884_);
v___x_901_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_902_ = l_Lean_Expr_fvar___override(v_fvarId_882_);
v___x_903_ = l_Lean_MessageData_ofExpr(v___x_902_);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_901_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = l_Lean_indentExpr(v_a_891_);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_908_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec(v_a_891_);
lean_dec(v_mvarId_884_);
lean_dec(v_fvarId_882_);
v_a_918_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_897_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_897_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec(v_mvarId_884_);
lean_dec(v_declFVarId_883_);
lean_dec(v_fvarId_882_);
v_a_926_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_890_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_890_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_zetaDeltaLocalDecl___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_882_ = stack[0].m_obj;
lean_object* v_declFVarId_883_ = stack[1].m_obj;
lean_object* v_mvarId_884_ = stack[2].m_obj;
lean_object* v___y_885_ = stack[3].m_obj;
lean_object* v___y_886_ = stack[4].m_obj;
lean_object* v___y_887_ = stack[5].m_obj;
lean_object* v___y_888_ = stack[6].m_obj;
lean_object* v_res_934_;
v_res_934_ = l_Lean_Meta_zetaDeltaLocalDecl___lam__0(v_fvarId_882_, v_declFVarId_883_, v_mvarId_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
stack->m_obj
 = v_res_934_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed(lean_object* v_fvarId_935_, lean_object* v_declFVarId_936_, lean_object* v_mvarId_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Lean_Meta_zetaDeltaLocalDecl___lam__0(v_fvarId_935_, v_declFVarId_936_, v_mvarId_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v___y_938_);
return v_res_943_;
}
}
lean_object* l_Lean_Meta_zetaDeltaLocalDecl(lean_object* v_mvarId_944_, lean_object* v_fvarId_945_, lean_object* v_declFVarId_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_){
_start:
{
lean_object* v___f_952_; lean_object* v___x_953_; 
lean_inc(v_mvarId_944_);
v___f_952_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_952_, 0, v_fvarId_945_);
lean_closure_set(v___f_952_, 1, v_declFVarId_946_);
lean_closure_set(v___f_952_, 2, v_mvarId_944_);
v___x_953_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_944_, v___f_952_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
return v___x_953_;
}
}
LEAN_EXPORT void l_Lean_Meta_zetaDeltaLocalDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_944_ = stack[0].m_obj;
lean_object* v_fvarId_945_ = stack[1].m_obj;
lean_object* v_declFVarId_946_ = stack[2].m_obj;
lean_object* v_a_947_ = stack[3].m_obj;
lean_object* v_a_948_ = stack[4].m_obj;
lean_object* v_a_949_ = stack[5].m_obj;
lean_object* v_a_950_ = stack[6].m_obj;
lean_object* v_res_954_;
v_res_954_ = l_Lean_Meta_zetaDeltaLocalDecl(v_mvarId_944_, v_fvarId_945_, v_declFVarId_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
stack->m_obj
 = v_res_954_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___boxed(lean_object* v_mvarId_955_, lean_object* v_fvarId_956_, lean_object* v_declFVarId_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Meta_zetaDeltaLocalDecl(v_mvarId_955_, v_fvarId_956_, v_declFVarId_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec_ref(v_a_958_);
return v_res_963_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Unfold(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
