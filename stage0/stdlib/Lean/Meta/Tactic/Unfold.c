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
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_reduceMatcher_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1;
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
lean_object* v_a_8_; lean_object* v___x_9_; lean_object* v_maxSteps_10_; lean_object* v_maxDischargeDepth_11_; uint8_t v_contextual_12_; uint8_t v_memoize_13_; uint8_t v_singlePass_14_; uint8_t v_zeta_15_; uint8_t v_beta_16_; uint8_t v_eta_17_; uint8_t v_etaStruct_18_; uint8_t v_iota_19_; uint8_t v_proj_20_; uint8_t v_decide_21_; uint8_t v_arith_22_; uint8_t v_autoUnfold_23_; uint8_t v_dsimp_24_; uint8_t v_failIfUnchanged_25_; uint8_t v_ground_26_; uint8_t v_unfoldPartialApp_27_; uint8_t v_zetaDelta_28_; uint8_t v_index_29_; uint8_t v_implicitDefEqProofs_30_; uint8_t v_zetaUnused_31_; uint8_t v_catchRuntime_32_; uint8_t v_zetaHave_33_; uint8_t v_congrConsts_34_; uint8_t v_bitVecOfNat_35_; uint8_t v_warnExponents_36_; uint8_t v_suggestions_37_; lean_object* v_maxSuggestions_38_; uint8_t v_locals_39_; uint8_t v_instances_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
lean_inc(v_a_8_);
lean_dec_ref(v___x_7_);
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
v___x_44_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_42_, v___x_43_, v_a_8_, v_a_3_, v_a_4_, v_a_5_);
return v___x_44_;
}
else
{
lean_object* v_a_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_52_; 
v_a_45_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_52_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_52_ == 0)
{
v___x_47_ = v___x_7_;
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_a_45_);
lean_dec(v___x_7_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_52_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_50_; 
if (v_isShared_48_ == 0)
{
v___x_50_ = v___x_47_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_a_45_);
v___x_50_ = v_reuseFailAlloc_51_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
return v___x_50_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___boxed(lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_53_, v_a_54_, v_a_55_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec_ref(v_a_53_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_58_, v_a_60_, v_a_61_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___boxed(lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(v_a_64_, v_a_65_, v_a_66_, v_a_67_);
lean_dec(v_a_67_);
lean_dec_ref(v_a_66_);
lean_dec(v_a_65_);
lean_dec_ref(v_a_64_);
return v_res_69_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1(void){
_start:
{
uint8_t v___x_72_; uint64_t v___x_73_; 
v___x_72_ = 2;
v___x_73_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(lean_object* v_unfoldThm_74_, lean_object* v_e_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_a_85_; lean_object* v___x_136_; 
lean_inc(v_unfoldThm_74_);
v___x_136_ = l_Lean_Meta_isRflTheorem(v_unfoldThm_74_, v_a_81_, v_a_82_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v_foApprox_141_; uint8_t v_ctxApprox_142_; uint8_t v_quasiPatternApprox_143_; uint8_t v_constApprox_144_; uint8_t v_isDefEqStuckEx_145_; uint8_t v_unificationHints_146_; uint8_t v_proofIrrelevance_147_; uint8_t v_assignSyntheticOpaque_148_; uint8_t v_offsetCnstrs_149_; uint8_t v_etaStruct_150_; uint8_t v_univApprox_151_; uint8_t v_iota_152_; uint8_t v_beta_153_; uint8_t v_proj_154_; uint8_t v_zeta_155_; uint8_t v_zetaDelta_156_; uint8_t v_zetaUnused_157_; uint8_t v_zetaHave_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_202_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref(v___x_136_);
v___x_138_ = lean_box(0);
lean_inc(v_unfoldThm_74_);
v___x_139_ = l_Lean_mkConst(v_unfoldThm_74_, v___x_138_);
v___x_140_ = l_Lean_Meta_Context_config(v_a_79_);
v_foApprox_141_ = lean_ctor_get_uint8(v___x_140_, 0);
v_ctxApprox_142_ = lean_ctor_get_uint8(v___x_140_, 1);
v_quasiPatternApprox_143_ = lean_ctor_get_uint8(v___x_140_, 2);
v_constApprox_144_ = lean_ctor_get_uint8(v___x_140_, 3);
v_isDefEqStuckEx_145_ = lean_ctor_get_uint8(v___x_140_, 4);
v_unificationHints_146_ = lean_ctor_get_uint8(v___x_140_, 5);
v_proofIrrelevance_147_ = lean_ctor_get_uint8(v___x_140_, 6);
v_assignSyntheticOpaque_148_ = lean_ctor_get_uint8(v___x_140_, 7);
v_offsetCnstrs_149_ = lean_ctor_get_uint8(v___x_140_, 8);
v_etaStruct_150_ = lean_ctor_get_uint8(v___x_140_, 10);
v_univApprox_151_ = lean_ctor_get_uint8(v___x_140_, 11);
v_iota_152_ = lean_ctor_get_uint8(v___x_140_, 12);
v_beta_153_ = lean_ctor_get_uint8(v___x_140_, 13);
v_proj_154_ = lean_ctor_get_uint8(v___x_140_, 14);
v_zeta_155_ = lean_ctor_get_uint8(v___x_140_, 15);
v_zetaDelta_156_ = lean_ctor_get_uint8(v___x_140_, 16);
v_zetaUnused_157_ = lean_ctor_get_uint8(v___x_140_, 17);
v_zetaHave_158_ = lean_ctor_get_uint8(v___x_140_, 18);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_202_ == 0)
{
v___x_160_ = v___x_140_;
v_isShared_161_ = v_isSharedCheck_202_;
goto v_resetjp_159_;
}
else
{
lean_dec(v___x_140_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_202_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
uint8_t v_trackZetaDelta_162_; lean_object* v_zetaDeltaSet_163_; lean_object* v_lctx_164_; lean_object* v_localInstances_165_; lean_object* v_defEqCtx_x3f_166_; lean_object* v_synthPendingDepth_167_; lean_object* v_canUnfold_x3f_168_; uint8_t v_univApprox_169_; uint8_t v_inTypeClassResolution_170_; uint8_t v_cacheInferType_171_; uint8_t v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v_config_177_; 
v_trackZetaDelta_162_ = lean_ctor_get_uint8(v_a_79_, sizeof(void*)*7);
v_zetaDeltaSet_163_ = lean_ctor_get(v_a_79_, 1);
v_lctx_164_ = lean_ctor_get(v_a_79_, 2);
v_localInstances_165_ = lean_ctor_get(v_a_79_, 3);
v_defEqCtx_x3f_166_ = lean_ctor_get(v_a_79_, 4);
v_synthPendingDepth_167_ = lean_ctor_get(v_a_79_, 5);
v_canUnfold_x3f_168_ = lean_ctor_get(v_a_79_, 6);
v_univApprox_169_ = lean_ctor_get_uint8(v_a_79_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_170_ = lean_ctor_get_uint8(v_a_79_, sizeof(void*)*7 + 2);
v_cacheInferType_171_ = lean_ctor_get_uint8(v_a_79_, sizeof(void*)*7 + 3);
v___x_172_ = 1;
v___x_173_ = 0;
v___x_174_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_174_, 0, v_unfoldThm_74_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*1, v___x_172_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*1 + 1, v___x_173_);
v___x_175_ = 2;
if (v_isShared_161_ == 0)
{
v_config_177_ = v___x_160_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 0, v_foApprox_141_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 1, v_ctxApprox_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 2, v_quasiPatternApprox_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 3, v_constApprox_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 4, v_isDefEqStuckEx_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 5, v_unificationHints_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 6, v_proofIrrelevance_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 7, v_assignSyntheticOpaque_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 8, v_offsetCnstrs_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 10, v_etaStruct_150_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 11, v_univApprox_151_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 12, v_iota_152_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 13, v_beta_153_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 14, v_proj_154_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 15, v_zeta_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 16, v_zetaDelta_156_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 17, v_zetaUnused_157_);
lean_ctor_set_uint8(v_reuseFailAlloc_201_, 18, v_zetaHave_158_);
v_config_177_ = v_reuseFailAlloc_201_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; uint64_t v_key_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
lean_ctor_set_uint8(v_config_177_, 9, v___x_175_);
v___x_178_ = l_Lean_Meta_Context_configKey(v_a_79_);
v___x_179_ = 2ULL;
v___x_180_ = lean_uint64_shift_right(v___x_178_, v___x_179_);
v___x_181_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0));
v___x_182_ = lean_unsigned_to_nat(1000u);
v___x_183_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_181_);
lean_ctor_set(v___x_183_, 2, v___x_139_);
lean_ctor_set(v___x_183_, 3, v___x_182_);
lean_ctor_set(v___x_183_, 4, v___x_174_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*5, v___x_172_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*5 + 1, v___x_173_);
v___x_184_ = lean_unbox(v_a_137_);
lean_dec(v_a_137_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*5 + 2, v___x_184_);
v___x_185_ = lean_uint64_shift_left(v___x_180_, v___x_179_);
v___x_186_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1, &l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1_once, _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1);
v_key_187_ = lean_uint64_lor(v___x_185_, v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_188_, 0, v_config_177_);
lean_ctor_set_uint64(v___x_188_, sizeof(void*)*1, v_key_187_);
lean_inc(v_canUnfold_x3f_168_);
lean_inc(v_synthPendingDepth_167_);
lean_inc(v_defEqCtx_x3f_166_);
lean_inc_ref(v_localInstances_165_);
lean_inc_ref(v_lctx_164_);
lean_inc(v_zetaDeltaSet_163_);
v___x_189_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_zetaDeltaSet_163_);
lean_ctor_set(v___x_189_, 2, v_lctx_164_);
lean_ctor_set(v___x_189_, 3, v_localInstances_165_);
lean_ctor_set(v___x_189_, 4, v_defEqCtx_x3f_166_);
lean_ctor_set(v___x_189_, 5, v_synthPendingDepth_167_);
lean_ctor_set(v___x_189_, 6, v_canUnfold_x3f_168_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*7, v_trackZetaDelta_162_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*7 + 1, v_univApprox_169_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*7 + 2, v_inTypeClassResolution_170_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*7 + 3, v_cacheInferType_171_);
v___x_190_ = l_Lean_Meta_Simp_tryTheorem_x3f(v_e_75_, v___x_183_, v_a_76_, v_a_77_, v_a_78_, v___x_189_, v_a_80_, v_a_81_, v_a_82_);
lean_dec_ref(v___x_189_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_191_; 
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref(v___x_190_);
v_a_85_ = v_a_191_;
goto v___jp_84_;
}
else
{
if (lean_obj_tag(v___x_190_) == 0)
{
lean_object* v_a_192_; 
v_a_192_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_192_);
lean_dec_ref(v___x_190_);
v_a_85_ = v_a_192_;
goto v___jp_84_;
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
v_a_193_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_190_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_190_);
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
}
}
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v_e_75_);
lean_dec(v_unfoldThm_74_);
v_a_203_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_136_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_136_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
v___jp_84_:
{
if (lean_obj_tag(v_a_85_) == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_86_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_86_, 0, v_a_85_);
v___x_87_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_135_; 
v_val_88_ = lean_ctor_get(v_a_85_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v_a_85_);
if (v_isSharedCheck_135_ == 0)
{
v___x_90_ = v_a_85_;
v_isShared_91_ = v_isSharedCheck_135_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_val_88_);
lean_dec(v_a_85_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_135_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v_expr_92_; lean_object* v_proof_x3f_93_; uint8_t v_cache_94_; lean_object* v___x_95_; 
v_expr_92_ = lean_ctor_get(v_val_88_, 0);
v_proof_x3f_93_ = lean_ctor_get(v_val_88_, 1);
v_cache_94_ = lean_ctor_get_uint8(v_val_88_, sizeof(void*)*2);
v___x_95_ = l_Lean_Meta_reduceMatcher_x3f(v_expr_92_, v_a_79_, v_a_80_, v_a_81_, v_a_82_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_126_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_126_ == 0)
{
v___x_98_ = v___x_95_;
v_isShared_99_ = v_isSharedCheck_126_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_a_96_);
lean_dec(v___x_95_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_126_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
if (lean_obj_tag(v_a_96_) == 0)
{
lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_117_; 
lean_inc(v_proof_x3f_93_);
lean_del_object(v___x_90_);
v_isSharedCheck_117_ = !lean_is_exclusive(v_val_88_);
if (v_isSharedCheck_117_ == 0)
{
lean_object* v_unused_118_; lean_object* v_unused_119_; 
v_unused_118_ = lean_ctor_get(v_val_88_, 1);
lean_dec(v_unused_118_);
v_unused_119_ = lean_ctor_get(v_val_88_, 0);
lean_dec(v_unused_119_);
v___x_101_ = v_val_88_;
v_isShared_102_ = v_isSharedCheck_117_;
goto v_resetjp_100_;
}
else
{
lean_dec(v_val_88_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_117_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v_val_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_116_; 
v_val_103_ = lean_ctor_get(v_a_96_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v_a_96_);
if (v_isSharedCheck_116_ == 0)
{
v___x_105_ = v_a_96_;
v_isShared_106_ = v_isSharedCheck_116_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_val_103_);
lean_dec(v_a_96_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_116_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 0, v_val_103_);
v___x_108_ = v___x_101_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v_val_103_);
lean_ctor_set(v_reuseFailAlloc_115_, 1, v_proof_x3f_93_);
lean_ctor_set_uint8(v_reuseFailAlloc_115_, sizeof(void*)*2, v_cache_94_);
v___x_108_ = v_reuseFailAlloc_115_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_110_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 0, v___x_108_);
v___x_110_ = v___x_105_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_114_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_110_);
v___x_112_ = v___x_98_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
}
else
{
lean_object* v___x_121_; 
lean_dec(v_a_96_);
if (v_isShared_91_ == 0)
{
lean_ctor_set_tag(v___x_90_, 0);
v___x_121_ = v___x_90_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_val_88_);
v___x_121_ = v_reuseFailAlloc_125_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
lean_object* v___x_123_; 
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_121_);
v___x_123_ = v___x_98_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
else
{
lean_object* v_a_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_134_; 
lean_del_object(v___x_90_);
lean_dec(v_val_88_);
v_a_127_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_134_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_134_ == 0)
{
v___x_129_ = v___x_95_;
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_a_127_);
lean_dec(v___x_95_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_134_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_133_; 
v_reuseFailAlloc_133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_133_, 0, v_a_127_);
v___x_132_ = v_reuseFailAlloc_133_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
return v___x_132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed(lean_object* v_unfoldThm_211_, lean_object* v_e_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(v_unfoldThm_211_, v_e_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec_ref(v_a_214_);
lean_dec(v_a_213_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0(lean_object* v_e_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_231_ = lean_box(0);
v___x_232_ = 1;
v___x_233_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_233_, 0, v_e_222_);
lean_ctor_set(v___x_233_, 1, v___x_231_);
lean_ctor_set_uint8(v___x_233_, sizeof(void*)*2, v___x_232_);
v___x_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_234_, 0, v___x_233_);
v___x_235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_235_, 0, v___x_234_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0___boxed(lean_object* v_e_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_unfold___lam__0(v_e_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1(lean_object* v_x_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_Meta_unfold___lam__1___closed__0));
v___x_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1___boxed(lean_object* v_x_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_unfold___lam__1(v_x_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v_x_259_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2(lean_object* v_e_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_278_, 0, v_e_269_);
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2___boxed(lean_object* v_e_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_unfold___lam__2(v_e_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
lean_dec(v___y_281_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3(lean_object* v_x_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_box(0);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3___boxed(lean_object* v_x_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Meta_unfold___lam__3(v_x_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec_ref(v_x_301_);
return v_res_310_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_unfold___lam__4(lean_object* v_declName_311_, lean_object* v_x_312_){
_start:
{
uint8_t v___x_313_; 
v___x_313_ = lean_name_eq(v_x_312_, v_declName_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__4___boxed(lean_object* v_declName_314_, lean_object* v_x_315_){
_start:
{
uint8_t v_res_316_; lean_object* v_r_317_; 
v_res_316_ = l_Lean_Meta_unfold___lam__4(v_declName_314_, v_x_315_);
lean_dec(v_x_315_);
lean_dec(v_declName_314_);
v_r_317_ = lean_box(v_res_316_);
return v_r_317_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__4(void){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__5(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Lean_Meta_unfold___closed__4, &l_Lean_Meta_unfold___closed__4_once, _init_l_Lean_Meta_unfold___closed__4);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__6(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__7(void){
_start:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_328_ = lean_unsigned_to_nat(32u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__8(void){
_start:
{
size_t v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_331_ = ((size_t)5ULL);
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_unsigned_to_nat(32u);
v___x_334_ = lean_mk_empty_array_with_capacity(v___x_333_);
v___x_335_ = lean_obj_once(&l_Lean_Meta_unfold___closed__7, &l_Lean_Meta_unfold___closed__7_once, _init_l_Lean_Meta_unfold___closed__7);
v___x_336_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
lean_ctor_set(v___x_336_, 2, v___x_332_);
lean_ctor_set(v___x_336_, 3, v___x_332_);
lean_ctor_set_usize(v___x_336_, 4, v___x_331_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__9(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_obj_once(&l_Lean_Meta_unfold___closed__8, &l_Lean_Meta_unfold___closed__8_once, _init_l_Lean_Meta_unfold___closed__8);
v___x_338_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
lean_ctor_set(v___x_339_, 2, v___x_338_);
lean_ctor_set(v___x_339_, 3, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__10(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_Lean_Meta_unfold___closed__9, &l_Lean_Meta_unfold___closed__9_once, _init_l_Lean_Meta_unfold___closed__9);
v___x_341_ = lean_obj_once(&l_Lean_Meta_unfold___closed__6, &l_Lean_Meta_unfold___closed__6_once, _init_l_Lean_Meta_unfold___closed__6);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold(lean_object* v_e_343_, lean_object* v_declName_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
uint8_t v___x_350_; lean_object* v___x_351_; 
v___x_350_ = 0;
lean_inc(v_declName_344_);
v___x_351_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_344_, v___x_350_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref(v___x_351_);
if (lean_obj_tag(v_a_352_) == 1)
{
lean_object* v_val_353_; lean_object* v___x_354_; 
lean_dec(v_declName_344_);
v_val_353_ = lean_ctor_get(v_a_352_, 0);
lean_inc(v_val_353_);
lean_dec_ref(v_a_352_);
v___x_354_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_345_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___f_356_; lean_object* v___f_357_; lean_object* v___f_358_; lean_object* v___f_359_; lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref(v___x_354_);
v___f_356_ = ((lean_object*)(l_Lean_Meta_unfold___closed__0));
v___f_357_ = ((lean_object*)(l_Lean_Meta_unfold___closed__1));
v___f_358_ = ((lean_object*)(l_Lean_Meta_unfold___closed__2));
v___f_359_ = ((lean_object*)(l_Lean_Meta_unfold___closed__3));
v___x_360_ = lean_obj_once(&l_Lean_Meta_unfold___closed__10, &l_Lean_Meta_unfold___closed__10_once, _init_l_Lean_Meta_unfold___closed__10);
v___x_361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed), 10, 1);
lean_closure_set(v___x_361_, 0, v_val_353_);
v___x_362_ = 1;
v___x_363_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___f_356_);
lean_ctor_set(v___x_363_, 2, v___f_357_);
lean_ctor_set(v___x_363_, 3, v___f_358_);
lean_ctor_set(v___x_363_, 4, v___f_359_);
lean_ctor_set_uint8(v___x_363_, sizeof(void*)*5, v___x_362_);
v___x_364_ = l_Lean_Meta_Simp_main(v_e_343_, v_a_355_, v___x_360_, v___x_363_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_373_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_373_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_373_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_fst_369_; lean_object* v___x_371_; 
v_fst_369_ = lean_ctor_get(v_a_365_, 0);
lean_inc(v_fst_369_);
lean_dec(v_a_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v_fst_369_);
v___x_371_ = v___x_367_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_fst_369_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
v_a_374_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_364_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_364_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
lean_dec(v_val_353_);
lean_dec_ref(v_e_343_);
v_a_382_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_354_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_354_);
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
else
{
lean_object* v___f_390_; lean_object* v___x_391_; 
lean_dec(v_a_352_);
v___f_390_ = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__4___boxed), 2, 1);
lean_closure_set(v___f_390_, 0, v_declName_344_);
v___x_391_ = l_Lean_Meta_deltaExpand(v_e_343_, v___f_390_, v___x_350_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_402_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_402_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_402_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_402_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; uint8_t v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_396_ = lean_box(0);
v___x_397_ = 1;
v___x_398_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_398_, 0, v_a_392_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*2, v___x_397_);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_398_);
v___x_400_ = v___x_394_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
else
{
lean_object* v_a_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_410_; 
v_a_403_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_410_ == 0)
{
v___x_405_ = v___x_391_;
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_a_403_);
lean_dec(v___x_391_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_410_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_408_; 
if (v_isShared_406_ == 0)
{
v___x_408_ = v___x_405_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v_a_403_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec(v_declName_344_);
lean_dec_ref(v_e_343_);
v_a_411_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_351_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_351_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___boxed(lean_object* v_e_419_, lean_object* v_declName_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Meta_unfold(v_e_419_, v_declName_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
lean_dec(v_a_424_);
lean_dec_ref(v_a_423_);
lean_dec(v_a_422_);
lean_dec_ref(v_a_421_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(lean_object* v_e_427_, lean_object* v___y_428_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = l_Lean_Expr_hasMVar(v_e_427_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_e_427_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v_mctx_433_; lean_object* v___x_434_; lean_object* v_fst_435_; lean_object* v_snd_436_; lean_object* v___x_437_; lean_object* v_cache_438_; lean_object* v_zetaDeltaFVarIds_439_; lean_object* v_postponed_440_; lean_object* v_diag_441_; lean_object* v___x_443_; uint8_t v_isShared_444_; uint8_t v_isSharedCheck_450_; 
v___x_432_ = lean_st_ref_get(v___y_428_);
v_mctx_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc_ref(v_mctx_433_);
lean_dec(v___x_432_);
v___x_434_ = l_Lean_instantiateMVarsCore(v_mctx_433_, v_e_427_);
v_fst_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_fst_435_);
v_snd_436_ = lean_ctor_get(v___x_434_, 1);
lean_inc(v_snd_436_);
lean_dec_ref(v___x_434_);
v___x_437_ = lean_st_ref_take(v___y_428_);
v_cache_438_ = lean_ctor_get(v___x_437_, 1);
v_zetaDeltaFVarIds_439_ = lean_ctor_get(v___x_437_, 2);
v_postponed_440_ = lean_ctor_get(v___x_437_, 3);
v_diag_441_ = lean_ctor_get(v___x_437_, 4);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_450_ == 0)
{
lean_object* v_unused_451_; 
v_unused_451_ = lean_ctor_get(v___x_437_, 0);
lean_dec(v_unused_451_);
v___x_443_ = v___x_437_;
v_isShared_444_ = v_isSharedCheck_450_;
goto v_resetjp_442_;
}
else
{
lean_inc(v_diag_441_);
lean_inc(v_postponed_440_);
lean_inc(v_zetaDeltaFVarIds_439_);
lean_inc(v_cache_438_);
lean_dec(v___x_437_);
v___x_443_ = lean_box(0);
v_isShared_444_ = v_isSharedCheck_450_;
goto v_resetjp_442_;
}
v_resetjp_442_:
{
lean_object* v___x_446_; 
if (v_isShared_444_ == 0)
{
lean_ctor_set(v___x_443_, 0, v_snd_436_);
v___x_446_ = v___x_443_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_snd_436_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_cache_438_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_zetaDeltaFVarIds_439_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_postponed_440_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_diag_441_);
v___x_446_ = v_reuseFailAlloc_449_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_447_ = lean_st_ref_set(v___y_428_, v___x_446_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v_fst_435_);
return v___x_448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg___boxed(lean_object* v_e_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_452_, v___y_453_);
lean_dec(v___y_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(lean_object* v_e_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_456_, v___y_458_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___boxed(lean_object* v_e_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(v_e_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
lean_dec_ref(v___y_464_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(lean_object* v_mvarId_470_, lean_object* v_x_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_470_, v_x_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_485_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_485_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_485_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v___x_483_; 
if (v_isShared_481_ == 0)
{
v___x_483_ = v___x_480_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_a_478_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
}
else
{
lean_object* v_a_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_493_; 
v_a_486_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_493_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_493_ == 0)
{
v___x_488_ = v___x_477_;
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_a_486_);
lean_dec(v___x_477_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_493_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_491_; 
if (v_isShared_489_ == 0)
{
v___x_491_ = v___x_488_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v_a_486_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(lean_object* v_00_u03b1_502_, lean_object* v_mvarId_503_, lean_object* v_x_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_503_, v_x_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___boxed(lean_object* v_00_u03b1_511_, lean_object* v_mvarId_512_, lean_object* v_x_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(v_00_u03b1_511_, v_mvarId_512_, v_x_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(lean_object* v_msgData_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v___x_526_; lean_object* v_env_527_; lean_object* v___x_528_; lean_object* v_mctx_529_; lean_object* v_lctx_530_; lean_object* v_options_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_526_ = lean_st_ref_get(v___y_524_);
v_env_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc_ref(v_env_527_);
lean_dec(v___x_526_);
v___x_528_ = lean_st_ref_get(v___y_522_);
v_mctx_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc_ref(v_mctx_529_);
lean_dec(v___x_528_);
v_lctx_530_ = lean_ctor_get(v___y_521_, 2);
v_options_531_ = lean_ctor_get(v___y_523_, 2);
lean_inc_ref(v_options_531_);
lean_inc_ref(v_lctx_530_);
v___x_532_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_532_, 0, v_env_527_);
lean_ctor_set(v___x_532_, 1, v_mctx_529_);
lean_ctor_set(v___x_532_, 2, v_lctx_530_);
lean_ctor_set(v___x_532_, 3, v_options_531_);
v___x_533_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_msgData_520_);
v___x_534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_534_, 0, v___x_533_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1___boxed(lean_object* v_msgData_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msgData_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_);
lean_dec(v___y_539_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(lean_object* v_msg_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_ref_548_; lean_object* v___x_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_558_; 
v_ref_548_ = lean_ctor_get(v___y_545_, 5);
v___x_549_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msg_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_558_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_558_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_556_; 
lean_inc(v_ref_548_);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v_ref_548_);
lean_ctor_set(v___x_554_, 1, v_a_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set_tag(v___x_552_, 1);
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_556_ = v___x_552_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg___boxed(lean_object* v_msg_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
return v_res_565_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Lean_Meta_unfoldTarget___lam__0___closed__0));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_Meta_unfoldTarget___lam__0___closed__2));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0(lean_object* v_mvarId_572_, lean_object* v_declName_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v___x_579_; 
lean_inc(v_mvarId_572_);
v___x_579_ = l_Lean_MVarId_getType(v_mvarId_572_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v_a_580_; lean_object* v___x_581_; lean_object* v_a_582_; lean_object* v___x_583_; 
v_a_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_a_580_);
lean_dec_ref(v___x_579_);
v___x_581_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_580_, v___y_575_);
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc_n(v_a_582_, 2);
lean_dec_ref(v___x_581_);
lean_inc(v_declName_573_);
v___x_583_ = l_Lean_Meta_unfold(v_a_582_, v_declName_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v_a_584_; lean_object* v_expr_585_; uint8_t v___x_586_; 
v_a_584_ = lean_ctor_get(v___x_583_, 0);
lean_inc(v_a_584_);
lean_dec_ref(v___x_583_);
v_expr_585_ = lean_ctor_get(v_a_584_, 0);
v___x_586_ = lean_expr_eqv(v_expr_585_, v_a_582_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; 
lean_dec(v_declName_573_);
v___x_587_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_572_, v_a_582_, v_a_584_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
lean_dec(v_a_582_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v_a_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_604_; 
lean_dec(v_a_584_);
lean_dec(v_mvarId_572_);
v___x_588_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_589_ = 0;
v___x_590_ = l_Lean_MessageData_ofConstName(v_declName_573_, v___x_589_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_588_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_indentExpr(v_a_582_);
v___x_595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_593_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
v___x_596_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_595_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
v_a_597_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_604_ == 0)
{
v___x_599_ = v___x_596_;
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_a_597_);
lean_dec(v___x_596_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_604_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_602_; 
if (v_isShared_600_ == 0)
{
v___x_602_ = v___x_599_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_a_597_);
v___x_602_ = v_reuseFailAlloc_603_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
return v___x_602_;
}
}
}
}
else
{
lean_object* v_a_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_612_; 
lean_dec(v_a_582_);
lean_dec(v_declName_573_);
lean_dec(v_mvarId_572_);
v_a_605_ = lean_ctor_get(v___x_583_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_583_);
if (v_isSharedCheck_612_ == 0)
{
v___x_607_ = v___x_583_;
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_a_605_);
lean_dec(v___x_583_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_612_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v___x_610_; 
if (v_isShared_608_ == 0)
{
v___x_610_ = v___x_607_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v_declName_573_);
lean_dec(v_mvarId_572_);
v_a_613_ = lean_ctor_get(v___x_579_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_579_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_579_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_579_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0___boxed(lean_object* v_mvarId_621_, lean_object* v_declName_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_Meta_unfoldTarget___lam__0(v_mvarId_621_, v_declName_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget(lean_object* v_mvarId_629_, lean_object* v_declName_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_){
_start:
{
lean_object* v___f_636_; lean_object* v___x_637_; 
lean_inc(v_mvarId_629_);
v___f_636_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_636_, 0, v_mvarId_629_);
lean_closure_set(v___f_636_, 1, v_declName_630_);
v___x_637_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_629_, v___f_636_, v_a_631_, v_a_632_, v_a_633_, v_a_634_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___boxed(lean_object* v_mvarId_638_, lean_object* v_declName_639_, lean_object* v_a_640_, lean_object* v_a_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_Meta_unfoldTarget(v_mvarId_638_, v_declName_639_, v_a_640_, v_a_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
lean_dec(v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(lean_object* v_00_u03b1_646_, lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___boxed(lean_object* v_00_u03b1_654_, lean_object* v_msg_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(v_00_u03b1_654_, v_msg_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(lean_object* v_msg_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_){
_start:
{
lean_object* v___f_669_; lean_object* v___x_976__overap_670_; lean_object* v___x_671_; 
v___f_669_ = ((lean_object*)(l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0));
v___x_976__overap_670_ = lean_panic_fn_borrowed(v___f_669_, v_msg_663_);
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
lean_inc(v___y_665_);
lean_inc_ref(v___y_664_);
v___x_671_ = lean_apply_5(v___x_976__overap_670_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, lean_box(0));
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___boxed(lean_object* v_msg_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v_msg_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_678_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_682_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2));
v___x_683_ = lean_unsigned_to_nat(94u);
v___x_684_ = lean_unsigned_to_nat(43u);
v___x_685_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1));
v___x_686_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0));
v___x_687_ = l_mkPanicMessageWithDecl(v___x_686_, v___x_685_, v___x_684_, v___x_683_, v___x_682_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0(lean_object* v_fvarId_688_, lean_object* v_declName_689_, lean_object* v_mvarId_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v___x_696_; 
lean_inc(v_fvarId_688_);
v___x_696_ = l_Lean_FVarId_getType___redArg(v_fvarId_688_, v___y_691_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v___x_698_; lean_object* v_a_699_; lean_object* v___x_700_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc_n(v_a_697_, 2);
lean_dec_ref(v___x_696_);
v___x_698_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_697_, v___y_692_);
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_698_);
lean_inc(v_declName_689_);
v___x_700_ = l_Lean_Meta_unfold(v_a_699_, v_declName_689_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v_expr_729_; uint8_t v___x_730_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref(v___x_700_);
v_expr_729_ = lean_ctor_get(v_a_701_, 0);
v___x_730_ = lean_expr_eqv(v_expr_729_, v_a_697_);
if (v___x_730_ == 0)
{
lean_dec(v_a_697_);
lean_dec(v_declName_689_);
v___y_703_ = v___y_691_;
v___y_704_ = v___y_692_;
v___y_705_ = v___y_693_;
v___y_706_ = v___y_694_;
goto v___jp_702_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
lean_dec(v_a_701_);
lean_dec(v_mvarId_690_);
lean_dec(v_fvarId_688_);
v___x_731_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_732_ = 0;
v___x_733_ = l_Lean_MessageData_ofConstName(v_declName_689_, v___x_732_);
v___x_734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_734_, 0, v___x_731_);
lean_ctor_set(v___x_734_, 1, v___x_733_);
v___x_735_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_734_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
v___x_737_ = l_Lean_indentExpr(v_a_697_);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_738_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
v___jp_702_:
{
uint8_t v___x_707_; lean_object* v___x_708_; 
v___x_707_ = 0;
v___x_708_ = l_Lean_Meta_applySimpResultToLocalDecl(v_mvarId_690_, v_fvarId_688_, v_a_701_, v___x_707_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_720_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_720_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_720_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_720_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
if (lean_obj_tag(v_a_709_) == 1)
{
lean_object* v_val_713_; lean_object* v_snd_714_; lean_object* v___x_716_; 
v_val_713_ = lean_ctor_get(v_a_709_, 0);
lean_inc(v_val_713_);
lean_dec_ref(v_a_709_);
v_snd_714_ = lean_ctor_get(v_val_713_, 1);
lean_inc(v_snd_714_);
lean_dec(v_val_713_);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v_snd_714_);
v___x_716_ = v___x_711_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_snd_714_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_del_object(v___x_711_);
lean_dec(v_a_709_);
v___x_718_ = lean_obj_once(&l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3, &l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3);
v___x_719_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v___x_718_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_719_;
}
}
}
else
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
v_a_721_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_708_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_708_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec(v_a_697_);
lean_dec(v_mvarId_690_);
lean_dec(v_declName_689_);
lean_dec(v_fvarId_688_);
v_a_748_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_700_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_700_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v_mvarId_690_);
lean_dec(v_declName_689_);
lean_dec(v_fvarId_688_);
v_a_756_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_696_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_696_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___boxed(lean_object* v_fvarId_764_, lean_object* v_declName_765_, lean_object* v_mvarId_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Meta_unfoldLocalDecl___lam__0(v_fvarId_764_, v_declName_765_, v_mvarId_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl(lean_object* v_mvarId_773_, lean_object* v_fvarId_774_, lean_object* v_declName_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___f_781_; lean_object* v___x_782_; 
lean_inc(v_mvarId_773_);
v___f_781_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_781_, 0, v_fvarId_774_);
lean_closure_set(v___f_781_, 1, v_declName_775_);
lean_closure_set(v___f_781_, 2, v_mvarId_773_);
v___x_782_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_773_, v___f_781_, v_a_776_, v_a_777_, v_a_778_, v_a_779_);
return v___x_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___boxed(lean_object* v_mvarId_783_, lean_object* v_fvarId_784_, lean_object* v_declName_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Lean_Meta_unfoldLocalDecl(v_mvarId_783_, v_fvarId_784_, v_declName_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_);
lean_dec(v_a_789_);
lean_dec_ref(v_a_788_);
lean_dec(v_a_787_);
lean_dec_ref(v_a_786_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0(lean_object* v_mvarId_792_, lean_object* v_declFVarId_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v___x_799_; 
lean_inc(v_mvarId_792_);
v___x_799_ = l_Lean_MVarId_getType(v_mvarId_792_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; lean_object* v___x_801_; lean_object* v_a_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
v___x_801_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_800_, v___y_795_);
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc_n(v_a_802_, 2);
lean_dec_ref(v___x_801_);
v___x_803_ = lean_unsigned_to_nat(1u);
v___x_804_ = lean_mk_empty_array_with_capacity(v___x_803_);
lean_inc(v_declFVarId_793_);
v___x_805_ = lean_array_push(v___x_804_, v_declFVarId_793_);
v___x_806_ = l_Lean_Meta_zetaDeltaFVars(v_a_802_, v___x_805_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; uint8_t v___x_808_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v___x_806_);
v___x_808_ = lean_expr_eqv(v_a_807_, v_a_802_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v_a_802_);
lean_dec(v_declFVarId_793_);
v___x_809_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_792_, v_a_807_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_a_807_);
lean_dec(v_mvarId_792_);
v___x_810_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_811_ = l_Lean_Expr_fvar___override(v_declFVarId_793_);
v___x_812_ = l_Lean_MessageData_ofExpr(v___x_811_);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_810_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = l_Lean_indentExpr(v_a_802_);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_817_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v_a_802_);
lean_dec(v_declFVarId_793_);
lean_dec(v_mvarId_792_);
v_a_827_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_806_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_806_);
v___x_829_ = lean_box(0);
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
v_resetjp_828_:
{
lean_object* v___x_832_; 
if (v_isShared_830_ == 0)
{
v___x_832_ = v___x_829_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_a_827_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec(v_declFVarId_793_);
lean_dec(v_mvarId_792_);
v_a_835_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_799_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_799_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0___boxed(lean_object* v_mvarId_843_, lean_object* v_declFVarId_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Meta_zetaDeltaTarget___lam__0(v_mvarId_843_, v_declFVarId_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget(lean_object* v_mvarId_851_, lean_object* v_declFVarId_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_){
_start:
{
lean_object* v___f_858_; lean_object* v___x_859_; 
lean_inc(v_mvarId_851_);
v___f_858_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_858_, 0, v_mvarId_851_);
lean_closure_set(v___f_858_, 1, v_declFVarId_852_);
v___x_859_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_851_, v___f_858_, v_a_853_, v_a_854_, v_a_855_, v_a_856_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___boxed(lean_object* v_mvarId_860_, lean_object* v_declFVarId_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Meta_zetaDeltaTarget(v_mvarId_860_, v_declFVarId_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0(lean_object* v_fvarId_868_, lean_object* v_declFVarId_869_, lean_object* v_mvarId_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v___x_876_; 
lean_inc(v_fvarId_868_);
v___x_876_ = l_Lean_FVarId_getType___redArg(v_fvarId_868_, v___y_871_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v_a_877_; lean_object* v___x_878_; lean_object* v_a_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_a_877_ = lean_ctor_get(v___x_876_, 0);
lean_inc_n(v_a_877_, 2);
lean_dec_ref(v___x_876_);
v___x_878_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_877_, v___y_872_);
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref(v___x_878_);
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = lean_mk_empty_array_with_capacity(v___x_880_);
v___x_882_ = lean_array_push(v___x_881_, v_declFVarId_869_);
v___x_883_ = l_Lean_Meta_zetaDeltaFVars(v_a_879_, v___x_882_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; uint8_t v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref(v___x_883_);
v___x_885_ = lean_expr_eqv(v_a_884_, v_a_877_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec(v_a_877_);
v___x_886_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_870_, v_fvarId_868_, v_a_884_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
return v___x_886_;
}
else
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec(v_a_884_);
lean_dec(v_mvarId_870_);
v___x_887_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_888_ = l_Lean_Expr_fvar___override(v_fvarId_868_);
v___x_889_ = l_Lean_MessageData_ofExpr(v___x_888_);
v___x_890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_887_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
v___x_891_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_892_, 0, v___x_890_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Lean_indentExpr(v_a_877_);
v___x_894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_892_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_894_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
v_a_896_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_895_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_895_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec(v_a_877_);
lean_dec(v_mvarId_870_);
lean_dec(v_fvarId_868_);
v_a_904_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_883_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_883_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_mvarId_870_);
lean_dec(v_declFVarId_869_);
lean_dec(v_fvarId_868_);
v_a_912_ = lean_ctor_get(v___x_876_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_876_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_876_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_876_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed(lean_object* v_fvarId_920_, lean_object* v_declFVarId_921_, lean_object* v_mvarId_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_Meta_zetaDeltaLocalDecl___lam__0(v_fvarId_920_, v_declFVarId_921_, v_mvarId_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl(lean_object* v_mvarId_929_, lean_object* v_fvarId_930_, lean_object* v_declFVarId_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___f_937_; lean_object* v___x_938_; 
lean_inc(v_mvarId_929_);
v___f_937_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_937_, 0, v_fvarId_930_);
lean_closure_set(v___f_937_, 1, v_declFVarId_931_);
lean_closure_set(v___f_937_, 2, v_mvarId_929_);
v___x_938_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_929_, v___f_937_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___boxed(lean_object* v_mvarId_939_, lean_object* v_fvarId_940_, lean_object* v_declFVarId_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Lean_Meta_zetaDeltaLocalDecl(v_mvarId_939_, v_fvarId_940_, v_declFVarId_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_947_;
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
