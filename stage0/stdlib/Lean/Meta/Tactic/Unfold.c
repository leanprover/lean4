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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* v_a_8_; lean_object* v___x_9_; lean_object* v_maxSteps_10_; lean_object* v_maxDischargeDepth_11_; uint8_t v_contextual_12_; uint8_t v_memoize_13_; uint8_t v_singlePass_14_; uint8_t v_zeta_15_; uint8_t v_beta_16_; uint8_t v_eta_17_; uint8_t v_etaStruct_18_; uint8_t v_iota_19_; uint8_t v_proj_20_; uint8_t v_decide_21_; uint8_t v_arith_22_; uint8_t v_autoUnfold_23_; uint8_t v_dsimp_24_; uint8_t v_failIfUnchanged_25_; uint8_t v_ground_26_; uint8_t v_unfoldPartialApp_27_; uint8_t v_zetaDelta_28_; uint8_t v_index_29_; uint8_t v_implicitDefEqProofs_30_; uint8_t v_zetaUnused_31_; uint8_t v_catchRuntime_32_; uint8_t v_zetaHave_33_; uint8_t v_congrConsts_34_; uint8_t v_bitVecOfNat_35_; uint8_t v_warnExponents_36_; uint8_t v_suggestions_37_; lean_object* v_maxSuggestions_38_; uint8_t v_locals_39_; uint8_t v_instances_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_50_; 
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
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_50_ == 0)
{
v___x_42_ = v___x_9_;
v_isShared_43_ = v_isSharedCheck_50_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_maxSuggestions_38_);
lean_inc(v_maxDischargeDepth_11_);
lean_inc(v_maxSteps_10_);
lean_dec(v___x_9_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_50_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
uint8_t v___x_44_; lean_object* v___x_46_; 
v___x_44_ = 1;
if (v_isShared_43_ == 0)
{
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_maxSteps_10_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_maxDischargeDepth_11_);
lean_ctor_set(v_reuseFailAlloc_49_, 2, v_maxSuggestions_38_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3, v_contextual_12_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 1, v_memoize_13_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 2, v_singlePass_14_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 3, v_zeta_15_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 4, v_beta_16_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 5, v_eta_17_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 6, v_etaStruct_18_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 7, v_iota_19_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 8, v_proj_20_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 9, v_decide_21_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 10, v_arith_22_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 11, v_autoUnfold_23_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 12, v_dsimp_24_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 13, v_failIfUnchanged_25_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 14, v_ground_26_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 15, v_unfoldPartialApp_27_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 16, v_zetaDelta_28_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 17, v_index_29_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 18, v_implicitDefEqProofs_30_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 19, v_zetaUnused_31_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 20, v_catchRuntime_32_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 21, v_zetaHave_33_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 23, v_congrConsts_34_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 24, v_bitVecOfNat_35_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 25, v_warnExponents_36_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 26, v_suggestions_37_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 27, v_locals_39_);
lean_ctor_set_uint8(v_reuseFailAlloc_49_, sizeof(void*)*3 + 28, v_instances_40_);
v___x_46_ = v_reuseFailAlloc_49_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
lean_ctor_set_uint8(v___x_46_, sizeof(void*)*3 + 22, v___x_44_);
v___x_47_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___closed__0));
v___x_48_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_46_, v___x_47_, v_a_8_, v_a_3_, v_a_4_, v_a_5_);
return v___x_48_;
}
}
}
else
{
lean_object* v_a_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_58_; 
v_a_51_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_58_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_58_ == 0)
{
v___x_53_ = v___x_7_;
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_a_51_);
lean_dec(v___x_7_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_58_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v___x_56_; 
if (v_isShared_54_ == 0)
{
v___x_56_ = v___x_53_;
goto v_reusejp_55_;
}
else
{
lean_object* v_reuseFailAlloc_57_; 
v_reuseFailAlloc_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_57_, 0, v_a_51_);
v___x_56_ = v_reuseFailAlloc_57_;
goto v_reusejp_55_;
}
v_reusejp_55_:
{
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg___boxed(lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_59_, v_a_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_a_60_);
lean_dec_ref(v_a_59_);
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_64_, v_a_66_, v_a_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___boxed(lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext(v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_75_;
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1(void){
_start:
{
uint8_t v___x_78_; uint64_t v___x_79_; 
v___x_78_ = 2;
v___x_79_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(lean_object* v_unfoldThm_80_, lean_object* v_e_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
lean_object* v_a_91_; lean_object* v___x_142_; 
lean_inc(v_unfoldThm_80_);
v___x_142_ = l_Lean_Meta_isRflTheorem(v_unfoldThm_80_, v_a_87_, v_a_88_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v_foApprox_147_; uint8_t v_ctxApprox_148_; uint8_t v_quasiPatternApprox_149_; uint8_t v_constApprox_150_; uint8_t v_isDefEqStuckEx_151_; uint8_t v_unificationHints_152_; uint8_t v_proofIrrelevance_153_; uint8_t v_assignSyntheticOpaque_154_; uint8_t v_offsetCnstrs_155_; uint8_t v_etaStruct_156_; uint8_t v_univApprox_157_; uint8_t v_iota_158_; uint8_t v_beta_159_; uint8_t v_proj_160_; uint8_t v_zeta_161_; uint8_t v_zetaDelta_162_; uint8_t v_zetaUnused_163_; uint8_t v_zetaHave_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_208_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref(v___x_142_);
v___x_144_ = lean_box(0);
lean_inc(v_unfoldThm_80_);
v___x_145_ = l_Lean_mkConst(v_unfoldThm_80_, v___x_144_);
v___x_146_ = l_Lean_Meta_Context_config(v_a_85_);
v_foApprox_147_ = lean_ctor_get_uint8(v___x_146_, 0);
v_ctxApprox_148_ = lean_ctor_get_uint8(v___x_146_, 1);
v_quasiPatternApprox_149_ = lean_ctor_get_uint8(v___x_146_, 2);
v_constApprox_150_ = lean_ctor_get_uint8(v___x_146_, 3);
v_isDefEqStuckEx_151_ = lean_ctor_get_uint8(v___x_146_, 4);
v_unificationHints_152_ = lean_ctor_get_uint8(v___x_146_, 5);
v_proofIrrelevance_153_ = lean_ctor_get_uint8(v___x_146_, 6);
v_assignSyntheticOpaque_154_ = lean_ctor_get_uint8(v___x_146_, 7);
v_offsetCnstrs_155_ = lean_ctor_get_uint8(v___x_146_, 8);
v_etaStruct_156_ = lean_ctor_get_uint8(v___x_146_, 10);
v_univApprox_157_ = lean_ctor_get_uint8(v___x_146_, 11);
v_iota_158_ = lean_ctor_get_uint8(v___x_146_, 12);
v_beta_159_ = lean_ctor_get_uint8(v___x_146_, 13);
v_proj_160_ = lean_ctor_get_uint8(v___x_146_, 14);
v_zeta_161_ = lean_ctor_get_uint8(v___x_146_, 15);
v_zetaDelta_162_ = lean_ctor_get_uint8(v___x_146_, 16);
v_zetaUnused_163_ = lean_ctor_get_uint8(v___x_146_, 17);
v_zetaHave_164_ = lean_ctor_get_uint8(v___x_146_, 18);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_208_ == 0)
{
v___x_166_ = v___x_146_;
v_isShared_167_ = v_isSharedCheck_208_;
goto v_resetjp_165_;
}
else
{
lean_dec(v___x_146_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_208_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
uint8_t v_trackZetaDelta_168_; lean_object* v_zetaDeltaSet_169_; lean_object* v_lctx_170_; lean_object* v_localInstances_171_; lean_object* v_defEqCtx_x3f_172_; lean_object* v_synthPendingDepth_173_; lean_object* v_canUnfold_x3f_174_; uint8_t v_univApprox_175_; uint8_t v_inTypeClassResolution_176_; uint8_t v_cacheInferType_177_; uint8_t v___x_178_; uint8_t v___x_179_; lean_object* v___x_180_; uint8_t v___x_181_; lean_object* v_config_183_; 
v_trackZetaDelta_168_ = lean_ctor_get_uint8(v_a_85_, sizeof(void*)*7);
v_zetaDeltaSet_169_ = lean_ctor_get(v_a_85_, 1);
v_lctx_170_ = lean_ctor_get(v_a_85_, 2);
v_localInstances_171_ = lean_ctor_get(v_a_85_, 3);
v_defEqCtx_x3f_172_ = lean_ctor_get(v_a_85_, 4);
v_synthPendingDepth_173_ = lean_ctor_get(v_a_85_, 5);
v_canUnfold_x3f_174_ = lean_ctor_get(v_a_85_, 6);
v_univApprox_175_ = lean_ctor_get_uint8(v_a_85_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_176_ = lean_ctor_get_uint8(v_a_85_, sizeof(void*)*7 + 2);
v_cacheInferType_177_ = lean_ctor_get_uint8(v_a_85_, sizeof(void*)*7 + 3);
v___x_178_ = 1;
v___x_179_ = 0;
v___x_180_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_180_, 0, v_unfoldThm_80_);
lean_ctor_set_uint8(v___x_180_, sizeof(void*)*1, v___x_178_);
lean_ctor_set_uint8(v___x_180_, sizeof(void*)*1 + 1, v___x_179_);
v___x_181_ = 2;
if (v_isShared_167_ == 0)
{
v_config_183_ = v___x_166_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 0, v_foApprox_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 1, v_ctxApprox_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 2, v_quasiPatternApprox_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 3, v_constApprox_150_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 4, v_isDefEqStuckEx_151_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 5, v_unificationHints_152_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 6, v_proofIrrelevance_153_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 7, v_assignSyntheticOpaque_154_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 8, v_offsetCnstrs_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 10, v_etaStruct_156_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 11, v_univApprox_157_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 12, v_iota_158_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 13, v_beta_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 14, v_proj_160_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 15, v_zeta_161_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 16, v_zetaDelta_162_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 17, v_zetaUnused_163_);
lean_ctor_set_uint8(v_reuseFailAlloc_207_, 18, v_zetaHave_164_);
v_config_183_ = v_reuseFailAlloc_207_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
uint64_t v___x_184_; uint64_t v___x_185_; uint64_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; uint64_t v___x_191_; uint64_t v___x_192_; uint64_t v_key_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
lean_ctor_set_uint8(v_config_183_, 9, v___x_181_);
v___x_184_ = l_Lean_Meta_Context_configKey(v_a_85_);
v___x_185_ = 2ULL;
v___x_186_ = lean_uint64_shift_right(v___x_184_, v___x_185_);
v___x_187_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0));
v___x_188_ = lean_unsigned_to_nat(1000u);
v___x_189_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_187_);
lean_ctor_set(v___x_189_, 2, v___x_145_);
lean_ctor_set(v___x_189_, 3, v___x_188_);
lean_ctor_set(v___x_189_, 4, v___x_180_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*5, v___x_178_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*5 + 1, v___x_179_);
v___x_190_ = lean_unbox(v_a_143_);
lean_dec(v_a_143_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*5 + 2, v___x_190_);
v___x_191_ = lean_uint64_shift_left(v___x_186_, v___x_185_);
v___x_192_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1, &l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1_once, _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1);
v_key_193_ = lean_uint64_lor(v___x_191_, v___x_192_);
v___x_194_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_194_, 0, v_config_183_);
lean_ctor_set_uint64(v___x_194_, sizeof(void*)*1, v_key_193_);
lean_inc(v_canUnfold_x3f_174_);
lean_inc(v_synthPendingDepth_173_);
lean_inc(v_defEqCtx_x3f_172_);
lean_inc_ref(v_localInstances_171_);
lean_inc_ref(v_lctx_170_);
lean_inc(v_zetaDeltaSet_169_);
v___x_195_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_zetaDeltaSet_169_);
lean_ctor_set(v___x_195_, 2, v_lctx_170_);
lean_ctor_set(v___x_195_, 3, v_localInstances_171_);
lean_ctor_set(v___x_195_, 4, v_defEqCtx_x3f_172_);
lean_ctor_set(v___x_195_, 5, v_synthPendingDepth_173_);
lean_ctor_set(v___x_195_, 6, v_canUnfold_x3f_174_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*7, v_trackZetaDelta_168_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*7 + 1, v_univApprox_175_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*7 + 2, v_inTypeClassResolution_176_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*7 + 3, v_cacheInferType_177_);
v___x_196_ = l_Lean_Meta_Simp_tryTheorem_x3f(v_e_81_, v___x_189_, v_a_82_, v_a_83_, v_a_84_, v___x_195_, v_a_86_, v_a_87_, v_a_88_);
lean_dec_ref(v___x_195_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref(v___x_196_);
v_a_91_ = v_a_197_;
goto v___jp_90_;
}
else
{
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_198_; 
v_a_198_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v___x_196_);
v_a_91_ = v_a_198_;
goto v___jp_90_;
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
v_a_199_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_196_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_196_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec_ref(v_e_81_);
lean_dec(v_unfoldThm_80_);
v_a_209_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_142_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_142_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
v___jp_90_:
{
if (lean_obj_tag(v_a_91_) == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_92_, 0, v_a_91_);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
else
{
lean_object* v_val_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_141_; 
v_val_94_ = lean_ctor_get(v_a_91_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v_a_91_);
if (v_isSharedCheck_141_ == 0)
{
v___x_96_ = v_a_91_;
v_isShared_97_ = v_isSharedCheck_141_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_val_94_);
lean_dec(v_a_91_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_141_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v_expr_98_; lean_object* v_proof_x3f_99_; uint8_t v_cache_100_; lean_object* v___x_101_; 
v_expr_98_ = lean_ctor_get(v_val_94_, 0);
v_proof_x3f_99_ = lean_ctor_get(v_val_94_, 1);
v_cache_100_ = lean_ctor_get_uint8(v_val_94_, sizeof(void*)*2);
lean_inc_ref(v_expr_98_);
v___x_101_ = l_Lean_Meta_reduceMatcher_x3f(v_expr_98_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_132_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_132_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_132_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_132_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
if (lean_obj_tag(v_a_102_) == 0)
{
lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_123_; 
lean_inc(v_proof_x3f_99_);
lean_del_object(v___x_96_);
v_isSharedCheck_123_ = !lean_is_exclusive(v_val_94_);
if (v_isSharedCheck_123_ == 0)
{
lean_object* v_unused_124_; lean_object* v_unused_125_; 
v_unused_124_ = lean_ctor_get(v_val_94_, 1);
lean_dec(v_unused_124_);
v_unused_125_ = lean_ctor_get(v_val_94_, 0);
lean_dec(v_unused_125_);
v___x_107_ = v_val_94_;
v_isShared_108_ = v_isSharedCheck_123_;
goto v_resetjp_106_;
}
else
{
lean_dec(v_val_94_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_123_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_val_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_122_; 
v_val_109_ = lean_ctor_get(v_a_102_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v_a_102_);
if (v_isSharedCheck_122_ == 0)
{
v___x_111_ = v_a_102_;
v_isShared_112_ = v_isSharedCheck_122_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_val_109_);
lean_dec(v_a_102_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_122_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v_val_109_);
v___x_114_ = v___x_107_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_val_109_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_proof_x3f_99_);
lean_ctor_set_uint8(v_reuseFailAlloc_121_, sizeof(void*)*2, v_cache_100_);
v___x_114_ = v_reuseFailAlloc_121_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v___x_116_; 
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_114_);
v___x_116_ = v___x_111_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_120_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v___x_118_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_116_);
v___x_118_ = v___x_104_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
else
{
lean_object* v___x_127_; 
lean_dec(v_a_102_);
if (v_isShared_97_ == 0)
{
lean_ctor_set_tag(v___x_96_, 0);
v___x_127_ = v___x_96_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_val_94_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_127_);
v___x_129_ = v___x_104_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_127_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
lean_del_object(v___x_96_);
lean_dec(v_val_94_);
v_a_133_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_101_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_101_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed(lean_object* v_unfoldThm_217_, lean_object* v_e_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(v_unfoldThm_217_, v_e_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0(lean_object* v_e_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___x_237_; uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_237_ = lean_box(0);
v___x_238_ = 1;
v___x_239_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_239_, 0, v_e_228_);
lean_ctor_set(v___x_239_, 1, v___x_237_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*2, v___x_238_);
v___x_240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
v___x_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0___boxed(lean_object* v_e_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Lean_Meta_unfold___lam__0(v_e_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
return v_res_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1(lean_object* v_x_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l_Lean_Meta_unfold___lam__1___closed__0));
v___x_264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1___boxed(lean_object* v_x_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_unfold___lam__1(v_x_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v_x_265_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2(lean_object* v_e_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_284_, 0, v_e_275_);
v___x_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2___boxed(lean_object* v_e_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_unfold___lam__2(v_e_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3(lean_object* v_x_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = lean_box(0);
v___x_306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3___boxed(lean_object* v_x_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Meta_unfold___lam__3(v_x_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v_x_307_);
return v_res_316_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_unfold___lam__4(lean_object* v_declName_317_, lean_object* v_x_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = lean_name_eq(v_x_318_, v_declName_317_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__4___boxed(lean_object* v_declName_320_, lean_object* v_x_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Lean_Meta_unfold___lam__4(v_declName_320_, v_x_321_);
lean_dec(v_x_321_);
lean_dec(v_declName_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__4(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__5(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_obj_once(&l_Lean_Meta_unfold___closed__4, &l_Lean_Meta_unfold___closed__4_once, _init_l_Lean_Meta_unfold___closed__4);
v___x_330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__6(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__7(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_unsigned_to_nat(32u);
v___x_335_ = lean_mk_empty_array_with_capacity(v___x_334_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__8(void){
_start:
{
size_t v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_337_ = ((size_t)5ULL);
v___x_338_ = lean_unsigned_to_nat(0u);
v___x_339_ = lean_unsigned_to_nat(32u);
v___x_340_ = lean_mk_empty_array_with_capacity(v___x_339_);
v___x_341_ = lean_obj_once(&l_Lean_Meta_unfold___closed__7, &l_Lean_Meta_unfold___closed__7_once, _init_l_Lean_Meta_unfold___closed__7);
v___x_342_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
lean_ctor_set(v___x_342_, 2, v___x_338_);
lean_ctor_set(v___x_342_, 3, v___x_338_);
lean_ctor_set_usize(v___x_342_, 4, v___x_337_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__9(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_343_ = lean_obj_once(&l_Lean_Meta_unfold___closed__8, &l_Lean_Meta_unfold___closed__8_once, _init_l_Lean_Meta_unfold___closed__8);
v___x_344_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_345_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
lean_ctor_set(v___x_345_, 2, v___x_344_);
lean_ctor_set(v___x_345_, 3, v___x_343_);
return v___x_345_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__10(void){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lean_obj_once(&l_Lean_Meta_unfold___closed__9, &l_Lean_Meta_unfold___closed__9_once, _init_l_Lean_Meta_unfold___closed__9);
v___x_347_ = lean_obj_once(&l_Lean_Meta_unfold___closed__6, &l_Lean_Meta_unfold___closed__6_once, _init_l_Lean_Meta_unfold___closed__6);
v___x_348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold(lean_object* v_e_349_, lean_object* v_declName_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_, lean_object* v_a_354_){
_start:
{
uint8_t v___x_356_; lean_object* v___x_357_; 
v___x_356_ = 0;
lean_inc(v_declName_350_);
v___x_357_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_350_, v___x_356_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_a_358_);
lean_dec_ref(v___x_357_);
if (lean_obj_tag(v_a_358_) == 1)
{
lean_object* v_val_359_; lean_object* v___x_360_; 
lean_dec(v_declName_350_);
v_val_359_ = lean_ctor_get(v_a_358_, 0);
lean_inc(v_val_359_);
lean_dec_ref(v_a_358_);
v___x_360_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_351_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_360_) == 0)
{
lean_object* v_a_361_; lean_object* v___f_362_; lean_object* v___f_363_; lean_object* v___f_364_; lean_object* v___f_365_; lean_object* v___x_366_; lean_object* v___x_367_; uint8_t v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v_a_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_a_361_);
lean_dec_ref(v___x_360_);
v___f_362_ = ((lean_object*)(l_Lean_Meta_unfold___closed__0));
v___f_363_ = ((lean_object*)(l_Lean_Meta_unfold___closed__1));
v___f_364_ = ((lean_object*)(l_Lean_Meta_unfold___closed__2));
v___f_365_ = ((lean_object*)(l_Lean_Meta_unfold___closed__3));
v___x_366_ = lean_obj_once(&l_Lean_Meta_unfold___closed__10, &l_Lean_Meta_unfold___closed__10_once, _init_l_Lean_Meta_unfold___closed__10);
v___x_367_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed), 10, 1);
lean_closure_set(v___x_367_, 0, v_val_359_);
v___x_368_ = 1;
v___x_369_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___f_362_);
lean_ctor_set(v___x_369_, 2, v___f_363_);
lean_ctor_set(v___x_369_, 3, v___f_364_);
lean_ctor_set(v___x_369_, 4, v___f_365_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*5, v___x_368_);
v___x_370_ = l_Lean_Meta_Simp_main(v_e_349_, v_a_361_, v___x_366_, v___x_369_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_379_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_379_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_379_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_379_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_fst_375_; lean_object* v___x_377_; 
v_fst_375_ = lean_ctor_get(v_a_371_, 0);
lean_inc(v_fst_375_);
lean_dec(v_a_371_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v_fst_375_);
v___x_377_ = v___x_373_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_fst_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
else
{
lean_object* v_a_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_387_; 
v_a_380_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_387_ == 0)
{
v___x_382_ = v___x_370_;
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_a_380_);
lean_dec(v___x_370_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_387_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v_a_380_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
else
{
lean_object* v_a_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_395_; 
lean_dec(v_val_359_);
lean_dec_ref(v_e_349_);
v_a_388_ = lean_ctor_get(v___x_360_, 0);
v_isSharedCheck_395_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_395_ == 0)
{
v___x_390_ = v___x_360_;
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_a_388_);
lean_dec(v___x_360_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_395_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v___x_393_; 
if (v_isShared_391_ == 0)
{
v___x_393_ = v___x_390_;
goto v_reusejp_392_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_a_388_);
v___x_393_ = v_reuseFailAlloc_394_;
goto v_reusejp_392_;
}
v_reusejp_392_:
{
return v___x_393_;
}
}
}
}
else
{
lean_object* v___f_396_; lean_object* v___x_397_; 
lean_dec(v_a_358_);
v___f_396_ = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__4___boxed), 2, 1);
lean_closure_set(v___f_396_, 0, v_declName_350_);
v___x_397_ = l_Lean_Meta_deltaExpand(v_e_349_, v___f_396_, v___x_356_, v_a_353_, v_a_354_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_408_; 
v_a_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_408_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_408_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_408_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; uint8_t v___x_403_; lean_object* v___x_404_; lean_object* v___x_406_; 
v___x_402_ = lean_box(0);
v___x_403_ = 1;
v___x_404_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_404_, 0, v_a_398_);
lean_ctor_set(v___x_404_, 1, v___x_402_);
lean_ctor_set_uint8(v___x_404_, sizeof(void*)*2, v___x_403_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_404_);
v___x_406_ = v___x_400_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_404_);
v___x_406_ = v_reuseFailAlloc_407_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
return v___x_406_;
}
}
}
else
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_416_; 
v_a_409_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_416_ == 0)
{
v___x_411_ = v___x_397_;
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_397_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_416_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_414_; 
if (v_isShared_412_ == 0)
{
v___x_414_ = v___x_411_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec(v_declName_350_);
lean_dec_ref(v_e_349_);
v_a_417_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_357_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_357_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___boxed(lean_object* v_e_425_, lean_object* v_declName_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Meta_unfold(v_e_425_, v_declName_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
lean_dec(v_a_428_);
lean_dec_ref(v_a_427_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(lean_object* v_e_433_, lean_object* v___y_434_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = l_Lean_Expr_hasMVar(v_e_433_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
v___x_437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_437_, 0, v_e_433_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; lean_object* v_mctx_439_; lean_object* v___x_440_; lean_object* v_fst_441_; lean_object* v_snd_442_; lean_object* v___x_443_; lean_object* v_cache_444_; lean_object* v_zetaDeltaFVarIds_445_; lean_object* v_postponed_446_; lean_object* v_diag_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_456_; 
v___x_438_ = lean_st_ref_get(v___y_434_);
v_mctx_439_ = lean_ctor_get(v___x_438_, 0);
lean_inc_ref(v_mctx_439_);
lean_dec(v___x_438_);
v___x_440_ = l_Lean_instantiateMVarsCore(v_mctx_439_, v_e_433_);
v_fst_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_fst_441_);
v_snd_442_ = lean_ctor_get(v___x_440_, 1);
lean_inc(v_snd_442_);
lean_dec_ref(v___x_440_);
v___x_443_ = lean_st_ref_take(v___y_434_);
v_cache_444_ = lean_ctor_get(v___x_443_, 1);
v_zetaDeltaFVarIds_445_ = lean_ctor_get(v___x_443_, 2);
v_postponed_446_ = lean_ctor_get(v___x_443_, 3);
v_diag_447_ = lean_ctor_get(v___x_443_, 4);
v_isSharedCheck_456_ = !lean_is_exclusive(v___x_443_);
if (v_isSharedCheck_456_ == 0)
{
lean_object* v_unused_457_; 
v_unused_457_ = lean_ctor_get(v___x_443_, 0);
lean_dec(v_unused_457_);
v___x_449_ = v___x_443_;
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_diag_447_);
lean_inc(v_postponed_446_);
lean_inc(v_zetaDeltaFVarIds_445_);
lean_inc(v_cache_444_);
lean_dec(v___x_443_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_456_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v_snd_442_);
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_snd_442_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_cache_444_);
lean_ctor_set(v_reuseFailAlloc_455_, 2, v_zetaDeltaFVarIds_445_);
lean_ctor_set(v_reuseFailAlloc_455_, 3, v_postponed_446_);
lean_ctor_set(v_reuseFailAlloc_455_, 4, v_diag_447_);
v___x_452_ = v_reuseFailAlloc_455_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_453_ = lean_st_ref_set(v___y_434_, v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_454_, 0, v_fst_441_);
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg___boxed(lean_object* v_e_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_458_, v___y_459_);
lean_dec(v___y_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(lean_object* v_e_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_462_, v___y_464_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___boxed(lean_object* v_e_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(v_e_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(lean_object* v_mvarId_476_, lean_object* v_x_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_476_, v_x_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
if (lean_obj_tag(v___x_483_) == 0)
{
lean_object* v_a_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_a_484_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_483_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_a_484_);
lean_dec(v___x_483_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_a_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
lean_object* v_a_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_499_; 
v_a_492_ = lean_ctor_get(v___x_483_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_483_);
if (v_isSharedCheck_499_ == 0)
{
v___x_494_ = v___x_483_;
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_a_492_);
lean_dec(v___x_483_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_499_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_497_; 
if (v_isShared_495_ == 0)
{
v___x_497_ = v___x_494_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_a_492_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg___boxed(lean_object* v_mvarId_500_, lean_object* v_x_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_500_, v_x_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_);
lean_dec(v___y_505_);
lean_dec_ref(v___y_504_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(lean_object* v_00_u03b1_508_, lean_object* v_mvarId_509_, lean_object* v_x_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_509_, v_x_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___boxed(lean_object* v_00_u03b1_517_, lean_object* v_mvarId_518_, lean_object* v_x_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(v_00_u03b1_517_, v_mvarId_518_, v_x_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(lean_object* v_msgData_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v___x_532_; lean_object* v_env_533_; lean_object* v___x_534_; lean_object* v_mctx_535_; lean_object* v_lctx_536_; lean_object* v_options_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_532_ = lean_st_ref_get(v___y_530_);
v_env_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc_ref(v_env_533_);
lean_dec(v___x_532_);
v___x_534_ = lean_st_ref_get(v___y_528_);
v_mctx_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc_ref(v_mctx_535_);
lean_dec(v___x_534_);
v_lctx_536_ = lean_ctor_get(v___y_527_, 2);
v_options_537_ = lean_ctor_get(v___y_529_, 2);
lean_inc_ref(v_options_537_);
lean_inc_ref(v_lctx_536_);
v___x_538_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_538_, 0, v_env_533_);
lean_ctor_set(v___x_538_, 1, v_mctx_535_);
lean_ctor_set(v___x_538_, 2, v_lctx_536_);
lean_ctor_set(v___x_538_, 3, v_options_537_);
v___x_539_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_msgData_526_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1___boxed(lean_object* v_msgData_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msgData_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(lean_object* v_msg_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_ref_554_; lean_object* v___x_555_; lean_object* v_a_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_564_; 
v_ref_554_ = lean_ctor_get(v___y_551_, 5);
v___x_555_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msg_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
v_a_556_ = lean_ctor_get(v___x_555_, 0);
v_isSharedCheck_564_ = !lean_is_exclusive(v___x_555_);
if (v_isSharedCheck_564_ == 0)
{
v___x_558_ = v___x_555_;
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_a_556_);
lean_dec(v___x_555_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_564_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
lean_inc(v_ref_554_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_ref_554_);
lean_ctor_set(v___x_560_, 1, v_a_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set_tag(v___x_558_, 1);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0(lean_object* v_mvarId_578_, lean_object* v_declName_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
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
lean_dec_ref(v___x_585_);
v___x_587_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_586_, v___y_581_);
v_a_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_a_588_);
lean_dec_ref(v___x_587_);
lean_inc(v_declName_579_);
lean_inc(v_a_588_);
v___x_589_ = l_Lean_Meta_unfold(v_a_588_, v_declName_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v_expr_591_; uint8_t v___x_592_; 
v_a_590_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_590_);
lean_dec_ref(v___x_589_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0___boxed(lean_object* v_mvarId_627_, lean_object* v_declName_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lean_Meta_unfoldTarget___lam__0(v_mvarId_627_, v_declName_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_);
lean_dec(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget(lean_object* v_mvarId_635_, lean_object* v_declName_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v___f_642_; lean_object* v___x_643_; 
lean_inc(v_mvarId_635_);
v___f_642_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_642_, 0, v_mvarId_635_);
lean_closure_set(v___f_642_, 1, v_declName_636_);
v___x_643_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_635_, v___f_642_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___boxed(lean_object* v_mvarId_644_, lean_object* v_declName_645_, lean_object* v_a_646_, lean_object* v_a_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_unfoldTarget(v_mvarId_644_, v_declName_645_, v_a_646_, v_a_647_, v_a_648_, v_a_649_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
lean_dec(v_a_647_);
lean_dec_ref(v_a_646_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(lean_object* v_00_u03b1_652_, lean_object* v_msg_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___boxed(lean_object* v_00_u03b1_660_, lean_object* v_msg_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(v_00_u03b1_660_, v_msg_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec(v___y_665_);
lean_dec_ref(v___y_664_);
lean_dec(v___y_663_);
lean_dec_ref(v___y_662_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(lean_object* v_msg_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
lean_object* v___f_675_; lean_object* v___x_975__overap_676_; lean_object* v___x_677_; 
v___f_675_ = ((lean_object*)(l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0));
v___x_975__overap_676_ = lean_panic_fn(v___f_675_, v_msg_669_);
lean_inc(v___y_673_);
lean_inc_ref(v___y_672_);
lean_inc(v___y_671_);
lean_inc_ref(v___y_670_);
v___x_677_ = lean_apply_5(v___x_975__overap_676_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, lean_box(0));
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___boxed(lean_object* v_msg_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v_msg_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
return v_res_684_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_688_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2));
v___x_689_ = lean_unsigned_to_nat(94u);
v___x_690_ = lean_unsigned_to_nat(43u);
v___x_691_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1));
v___x_692_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0));
v___x_693_ = l_mkPanicMessageWithDecl(v___x_692_, v___x_691_, v___x_690_, v___x_689_, v___x_688_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0(lean_object* v_fvarId_694_, lean_object* v_declName_695_, lean_object* v_mvarId_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; 
lean_inc(v_fvarId_694_);
v___x_702_ = l_Lean_FVarId_getType___redArg(v_fvarId_694_, v___y_697_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; lean_object* v_a_705_; lean_object* v___x_706_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
lean_inc(v_a_703_);
v___x_704_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_703_, v___y_698_);
v_a_705_ = lean_ctor_get(v___x_704_, 0);
lean_inc(v_a_705_);
lean_dec_ref(v___x_704_);
lean_inc(v_declName_695_);
v___x_706_ = l_Lean_Meta_unfold(v_a_705_, v_declName_695_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v_expr_735_; uint8_t v___x_736_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref(v___x_706_);
v_expr_735_ = lean_ctor_get(v_a_707_, 0);
v___x_736_ = lean_expr_eqv(v_expr_735_, v_a_703_);
if (v___x_736_ == 0)
{
lean_dec(v_a_703_);
lean_dec(v_declName_695_);
v___y_709_ = v___y_697_;
v___y_710_ = v___y_698_;
v___y_711_ = v___y_699_;
v___y_712_ = v___y_700_;
goto v___jp_708_;
}
else
{
lean_object* v___x_737_; uint8_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec(v_a_707_);
lean_dec(v_mvarId_696_);
lean_dec(v_fvarId_694_);
v___x_737_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_738_ = 0;
v___x_739_ = l_Lean_MessageData_ofConstName(v_declName_695_, v___x_738_);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_737_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
v___x_741_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_indentExpr(v_a_703_);
v___x_744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_742_);
lean_ctor_set(v___x_744_, 1, v___x_743_);
v___x_745_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_744_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
v_a_746_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_745_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_745_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
v___jp_708_:
{
uint8_t v___x_713_; lean_object* v___x_714_; 
v___x_713_ = 0;
v___x_714_ = l_Lean_Meta_applySimpResultToLocalDecl(v_mvarId_696_, v_fvarId_694_, v_a_707_, v___x_713_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_726_; 
v_a_715_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_726_ == 0)
{
v___x_717_ = v___x_714_;
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_714_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_726_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
if (lean_obj_tag(v_a_715_) == 1)
{
lean_object* v_val_719_; lean_object* v_snd_720_; lean_object* v___x_722_; 
v_val_719_ = lean_ctor_get(v_a_715_, 0);
lean_inc(v_val_719_);
lean_dec_ref(v_a_715_);
v_snd_720_ = lean_ctor_get(v_val_719_, 1);
lean_inc(v_snd_720_);
lean_dec(v_val_719_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 0, v_snd_720_);
v___x_722_ = v___x_717_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_snd_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; 
lean_del_object(v___x_717_);
lean_dec(v_a_715_);
v___x_724_ = lean_obj_once(&l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3, &l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3);
v___x_725_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v___x_724_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
return v___x_725_;
}
}
}
else
{
lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
v_a_727_ = lean_ctor_get(v___x_714_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v___x_714_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_714_);
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
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec(v_a_703_);
lean_dec(v_mvarId_696_);
lean_dec(v_declName_695_);
lean_dec(v_fvarId_694_);
v_a_754_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_706_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_706_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_a_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_769_; 
lean_dec(v_mvarId_696_);
lean_dec(v_declName_695_);
lean_dec(v_fvarId_694_);
v_a_762_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_769_ == 0)
{
v___x_764_ = v___x_702_;
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_a_762_);
lean_dec(v___x_702_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_769_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_767_; 
if (v_isShared_765_ == 0)
{
v___x_767_ = v___x_764_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_a_762_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___boxed(lean_object* v_fvarId_770_, lean_object* v_declName_771_, lean_object* v_mvarId_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Meta_unfoldLocalDecl___lam__0(v_fvarId_770_, v_declName_771_, v_mvarId_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl(lean_object* v_mvarId_779_, lean_object* v_fvarId_780_, lean_object* v_declName_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___f_787_; lean_object* v___x_788_; 
lean_inc(v_mvarId_779_);
v___f_787_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_787_, 0, v_fvarId_780_);
lean_closure_set(v___f_787_, 1, v_declName_781_);
lean_closure_set(v___f_787_, 2, v_mvarId_779_);
v___x_788_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_779_, v___f_787_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___boxed(lean_object* v_mvarId_789_, lean_object* v_fvarId_790_, lean_object* v_declName_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_Meta_unfoldLocalDecl(v_mvarId_789_, v_fvarId_790_, v_declName_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0(lean_object* v_mvarId_798_, lean_object* v_declFVarId_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
lean_inc(v_mvarId_798_);
v___x_805_ = l_Lean_MVarId_getType(v_mvarId_798_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; lean_object* v___x_807_; lean_object* v_a_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref(v___x_805_);
v___x_807_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_806_, v___y_801_);
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref(v___x_807_);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_mk_empty_array_with_capacity(v___x_809_);
lean_inc(v_declFVarId_799_);
v___x_811_ = lean_array_push(v___x_810_, v_declFVarId_799_);
lean_inc(v_a_808_);
v___x_812_ = l_Lean_Meta_zetaDeltaFVars(v_a_808_, v___x_811_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; uint8_t v___x_814_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_812_);
v___x_814_ = lean_expr_eqv(v_a_813_, v_a_808_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; 
lean_dec(v_a_808_);
lean_dec(v_declFVarId_799_);
v___x_815_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_798_, v_a_813_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v_a_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_832_; 
lean_dec(v_a_813_);
lean_dec(v_mvarId_798_);
v___x_816_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_817_ = l_Lean_Expr_fvar___override(v_declFVarId_799_);
v___x_818_ = l_Lean_MessageData_ofExpr(v___x_817_);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_816_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
v___x_820_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = l_Lean_indentExpr(v_a_808_);
v___x_823_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_823_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
v_a_825_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_832_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_832_ == 0)
{
v___x_827_ = v___x_824_;
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_a_825_);
lean_dec(v___x_824_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_832_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_830_; 
if (v_isShared_828_ == 0)
{
v___x_830_ = v___x_827_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_a_825_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
}
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec(v_a_808_);
lean_dec(v_declFVarId_799_);
lean_dec(v_mvarId_798_);
v_a_833_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_812_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_812_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec(v_declFVarId_799_);
lean_dec(v_mvarId_798_);
v_a_841_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_805_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_805_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0___boxed(lean_object* v_mvarId_849_, lean_object* v_declFVarId_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_Meta_zetaDeltaTarget___lam__0(v_mvarId_849_, v_declFVarId_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget(lean_object* v_mvarId_857_, lean_object* v_declFVarId_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___f_864_; lean_object* v___x_865_; 
lean_inc(v_mvarId_857_);
v___f_864_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_864_, 0, v_mvarId_857_);
lean_closure_set(v___f_864_, 1, v_declFVarId_858_);
v___x_865_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_857_, v___f_864_, v_a_859_, v_a_860_, v_a_861_, v_a_862_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___boxed(lean_object* v_mvarId_866_, lean_object* v_declFVarId_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Meta_zetaDeltaTarget(v_mvarId_866_, v_declFVarId_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0(lean_object* v_fvarId_874_, lean_object* v_declFVarId_875_, lean_object* v_mvarId_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; 
lean_inc(v_fvarId_874_);
v___x_882_ = l_Lean_FVarId_getType___redArg(v_fvarId_874_, v___y_877_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v_a_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref(v___x_882_);
lean_inc(v_a_883_);
v___x_884_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_883_, v___y_878_);
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref(v___x_884_);
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_mk_empty_array_with_capacity(v___x_886_);
v___x_888_ = lean_array_push(v___x_887_, v_declFVarId_875_);
v___x_889_ = l_Lean_Meta_zetaDeltaFVars(v_a_885_, v___x_888_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; uint8_t v___x_891_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v___x_889_);
v___x_891_ = lean_expr_eqv(v_a_890_, v_a_883_);
if (v___x_891_ == 0)
{
lean_object* v___x_892_; 
lean_dec(v_a_883_);
v___x_892_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_876_, v_fvarId_874_, v_a_890_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
return v___x_892_;
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_a_890_);
lean_dec(v_mvarId_876_);
v___x_893_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_894_ = l_Lean_Expr_fvar___override(v_fvarId_874_);
v___x_895_ = l_Lean_MessageData_ofExpr(v___x_894_);
v___x_896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_893_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l_Lean_indentExpr(v_a_883_);
v___x_900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_900_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec(v_a_883_);
lean_dec(v_mvarId_876_);
lean_dec(v_fvarId_874_);
v_a_910_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_889_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_889_);
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
lean_dec(v_mvarId_876_);
lean_dec(v_declFVarId_875_);
lean_dec(v_fvarId_874_);
v_a_918_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_882_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_882_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed(lean_object* v_fvarId_926_, lean_object* v_declFVarId_927_, lean_object* v_mvarId_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Meta_zetaDeltaLocalDecl___lam__0(v_fvarId_926_, v_declFVarId_927_, v_mvarId_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl(lean_object* v_mvarId_935_, lean_object* v_fvarId_936_, lean_object* v_declFVarId_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___f_943_; lean_object* v___x_944_; 
lean_inc(v_mvarId_935_);
v___f_943_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_943_, 0, v_fvarId_936_);
lean_closure_set(v___f_943_, 1, v_declFVarId_937_);
lean_closure_set(v___f_943_, 2, v_mvarId_935_);
v___x_944_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_935_, v___f_943_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___boxed(lean_object* v_mvarId_945_, lean_object* v_fvarId_946_, lean_object* v_declFVarId_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Meta_zetaDeltaLocalDecl(v_mvarId_945_, v_fvarId_946_, v_declFVarId_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec_ref(v_a_948_);
return v_res_953_;
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
