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
static uint64_t _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1(void){
_start:
{
uint8_t v___x_73_; uint64_t v___x_74_; 
v___x_73_ = 2;
v___x_74_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(lean_object* v_unfoldThm_75_, lean_object* v_e_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_a_86_; lean_object* v___x_137_; 
lean_inc(v_unfoldThm_75_);
v___x_137_ = l_Lean_Meta_isRflTheorem(v_unfoldThm_75_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_139_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_a_138_);
lean_dec_ref_known(v___x_137_, 1);
lean_inc(v_unfoldThm_75_);
v___x_139_ = l_Lean_Meta_isBackwardRflTheorem(v_unfoldThm_75_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v_foApprox_144_; uint8_t v_ctxApprox_145_; uint8_t v_quasiPatternApprox_146_; uint8_t v_constApprox_147_; uint8_t v_isDefEqStuckEx_148_; uint8_t v_unificationHints_149_; uint8_t v_proofIrrelevance_150_; uint8_t v_assignSyntheticOpaque_151_; uint8_t v_offsetCnstrs_152_; uint8_t v_etaStruct_153_; uint8_t v_univApprox_154_; uint8_t v_iota_155_; uint8_t v_beta_156_; uint8_t v_proj_157_; uint8_t v_zeta_158_; uint8_t v_zetaDelta_159_; uint8_t v_zetaUnused_160_; uint8_t v_zetaHave_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_206_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
lean_inc(v_a_140_);
lean_dec_ref_known(v___x_139_, 1);
v___x_141_ = lean_box(0);
lean_inc(v_unfoldThm_75_);
v___x_142_ = l_Lean_mkConst(v_unfoldThm_75_, v___x_141_);
v___x_143_ = l_Lean_Meta_Context_config(v_a_80_);
v_foApprox_144_ = lean_ctor_get_uint8(v___x_143_, 0);
v_ctxApprox_145_ = lean_ctor_get_uint8(v___x_143_, 1);
v_quasiPatternApprox_146_ = lean_ctor_get_uint8(v___x_143_, 2);
v_constApprox_147_ = lean_ctor_get_uint8(v___x_143_, 3);
v_isDefEqStuckEx_148_ = lean_ctor_get_uint8(v___x_143_, 4);
v_unificationHints_149_ = lean_ctor_get_uint8(v___x_143_, 5);
v_proofIrrelevance_150_ = lean_ctor_get_uint8(v___x_143_, 6);
v_assignSyntheticOpaque_151_ = lean_ctor_get_uint8(v___x_143_, 7);
v_offsetCnstrs_152_ = lean_ctor_get_uint8(v___x_143_, 8);
v_etaStruct_153_ = lean_ctor_get_uint8(v___x_143_, 10);
v_univApprox_154_ = lean_ctor_get_uint8(v___x_143_, 11);
v_iota_155_ = lean_ctor_get_uint8(v___x_143_, 12);
v_beta_156_ = lean_ctor_get_uint8(v___x_143_, 13);
v_proj_157_ = lean_ctor_get_uint8(v___x_143_, 14);
v_zeta_158_ = lean_ctor_get_uint8(v___x_143_, 15);
v_zetaDelta_159_ = lean_ctor_get_uint8(v___x_143_, 16);
v_zetaUnused_160_ = lean_ctor_get_uint8(v___x_143_, 17);
v_zetaHave_161_ = lean_ctor_get_uint8(v___x_143_, 18);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_206_ == 0)
{
v___x_163_ = v___x_143_;
v_isShared_164_ = v_isSharedCheck_206_;
goto v_resetjp_162_;
}
else
{
lean_dec(v___x_143_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_206_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
uint8_t v_trackZetaDelta_165_; lean_object* v_zetaDeltaSet_166_; lean_object* v_lctx_167_; lean_object* v_localInstances_168_; lean_object* v_defEqCtx_x3f_169_; lean_object* v_synthPendingDepth_170_; lean_object* v_canUnfold_x3f_171_; uint8_t v_univApprox_172_; uint8_t v_inTypeClassResolution_173_; uint8_t v_cacheInferType_174_; uint8_t v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v_config_180_; 
v_trackZetaDelta_165_ = lean_ctor_get_uint8(v_a_80_, sizeof(void*)*7);
v_zetaDeltaSet_166_ = lean_ctor_get(v_a_80_, 1);
v_lctx_167_ = lean_ctor_get(v_a_80_, 2);
v_localInstances_168_ = lean_ctor_get(v_a_80_, 3);
v_defEqCtx_x3f_169_ = lean_ctor_get(v_a_80_, 4);
v_synthPendingDepth_170_ = lean_ctor_get(v_a_80_, 5);
v_canUnfold_x3f_171_ = lean_ctor_get(v_a_80_, 6);
v_univApprox_172_ = lean_ctor_get_uint8(v_a_80_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_173_ = lean_ctor_get_uint8(v_a_80_, sizeof(void*)*7 + 2);
v_cacheInferType_174_ = lean_ctor_get_uint8(v_a_80_, sizeof(void*)*7 + 3);
v___x_175_ = 1;
v___x_176_ = 0;
v___x_177_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v___x_177_, 0, v_unfoldThm_75_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*1, v___x_175_);
lean_ctor_set_uint8(v___x_177_, sizeof(void*)*1 + 1, v___x_176_);
v___x_178_ = 2;
if (v_isShared_164_ == 0)
{
v_config_180_ = v___x_163_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 0, v_foApprox_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 1, v_ctxApprox_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 2, v_quasiPatternApprox_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 3, v_constApprox_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 4, v_isDefEqStuckEx_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 5, v_unificationHints_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 6, v_proofIrrelevance_150_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 7, v_assignSyntheticOpaque_151_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 8, v_offsetCnstrs_152_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 10, v_etaStruct_153_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 11, v_univApprox_154_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 12, v_iota_155_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 13, v_beta_156_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 14, v_proj_157_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 15, v_zeta_158_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 16, v_zetaDelta_159_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 17, v_zetaUnused_160_);
lean_ctor_set_uint8(v_reuseFailAlloc_205_, 18, v_zetaHave_161_);
v_config_180_ = v_reuseFailAlloc_205_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
uint64_t v___x_181_; uint64_t v___x_182_; uint64_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; uint8_t v___x_188_; uint64_t v___x_189_; uint64_t v___x_190_; uint64_t v_key_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
lean_ctor_set_uint8(v_config_180_, 9, v___x_178_);
v___x_181_ = l_Lean_Meta_Context_configKey(v_a_80_);
v___x_182_ = 3ULL;
v___x_183_ = lean_uint64_shift_right(v___x_181_, v___x_182_);
v___x_184_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__0));
v___x_185_ = lean_unsigned_to_nat(1000u);
v___x_186_ = lean_alloc_ctor(0, 5, 4);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___x_142_);
lean_ctor_set(v___x_186_, 3, v___x_185_);
lean_ctor_set(v___x_186_, 4, v___x_177_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*5, v___x_175_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*5 + 1, v___x_176_);
v___x_187_ = lean_unbox(v_a_138_);
lean_dec(v_a_138_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*5 + 2, v___x_187_);
v___x_188_ = lean_unbox(v_a_140_);
lean_dec(v_a_140_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*5 + 3, v___x_188_);
v___x_189_ = lean_uint64_shift_left(v___x_183_, v___x_182_);
v___x_190_ = lean_uint64_once(&l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1, &l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1_once, _init_l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___closed__1);
v_key_191_ = lean_uint64_lor(v___x_189_, v___x_190_);
v___x_192_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_192_, 0, v_config_180_);
lean_ctor_set_uint64(v___x_192_, sizeof(void*)*1, v_key_191_);
lean_inc(v_canUnfold_x3f_171_);
lean_inc(v_synthPendingDepth_170_);
lean_inc(v_defEqCtx_x3f_169_);
lean_inc_ref(v_localInstances_168_);
lean_inc_ref(v_lctx_167_);
lean_inc(v_zetaDeltaSet_166_);
v___x_193_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_zetaDeltaSet_166_);
lean_ctor_set(v___x_193_, 2, v_lctx_167_);
lean_ctor_set(v___x_193_, 3, v_localInstances_168_);
lean_ctor_set(v___x_193_, 4, v_defEqCtx_x3f_169_);
lean_ctor_set(v___x_193_, 5, v_synthPendingDepth_170_);
lean_ctor_set(v___x_193_, 6, v_canUnfold_x3f_171_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*7, v_trackZetaDelta_165_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*7 + 1, v_univApprox_172_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*7 + 2, v_inTypeClassResolution_173_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*7 + 3, v_cacheInferType_174_);
v___x_194_ = l_Lean_Meta_Simp_tryTheorem_x3f(v_e_76_, v___x_186_, v_a_77_, v_a_78_, v_a_79_, v___x_193_, v_a_81_, v_a_82_, v_a_83_);
lean_dec_ref_known(v___x_193_, 7);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_194_, 1);
v_a_86_ = v_a_195_;
goto v___jp_85_;
}
else
{
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_196_; 
v_a_196_ = lean_ctor_get(v___x_194_, 0);
lean_inc(v_a_196_);
lean_dec_ref_known(v___x_194_, 1);
v_a_86_ = v_a_196_;
goto v___jp_85_;
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
v_a_197_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_194_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_194_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_a_138_);
lean_dec_ref(v_e_76_);
lean_dec(v_unfoldThm_75_);
v_a_207_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_139_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_139_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec_ref(v_e_76_);
lean_dec(v_unfoldThm_75_);
v_a_215_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_137_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_137_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
v___jp_85_:
{
if (lean_obj_tag(v_a_86_) == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_87_, 0, v_a_86_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_136_; 
v_val_89_ = lean_ctor_get(v_a_86_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_a_86_);
if (v_isSharedCheck_136_ == 0)
{
v___x_91_ = v_a_86_;
v_isShared_92_ = v_isSharedCheck_136_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_val_89_);
lean_dec(v_a_86_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_136_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_expr_93_; lean_object* v_proof_x3f_94_; uint8_t v_cache_95_; lean_object* v___x_96_; 
v_expr_93_ = lean_ctor_get(v_val_89_, 0);
v_proof_x3f_94_ = lean_ctor_get(v_val_89_, 1);
v_cache_95_ = lean_ctor_get_uint8(v_val_89_, sizeof(void*)*2);
v___x_96_ = l_Lean_Meta_reduceMatcher_x3f(v_expr_93_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_127_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_127_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_127_ == 0)
{
v___x_99_ = v___x_96_;
v_isShared_100_ = v_isSharedCheck_127_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_127_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
if (lean_obj_tag(v_a_97_) == 0)
{
lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_118_; 
lean_inc(v_proof_x3f_94_);
lean_del_object(v___x_91_);
v_isSharedCheck_118_ = !lean_is_exclusive(v_val_89_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; lean_object* v_unused_120_; 
v_unused_119_ = lean_ctor_get(v_val_89_, 1);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_val_89_, 0);
lean_dec(v_unused_120_);
v___x_102_ = v_val_89_;
v_isShared_103_ = v_isSharedCheck_118_;
goto v_resetjp_101_;
}
else
{
lean_dec(v_val_89_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_118_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v_val_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_117_; 
v_val_104_ = lean_ctor_get(v_a_97_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v_a_97_);
if (v_isSharedCheck_117_ == 0)
{
v___x_106_ = v_a_97_;
v_isShared_107_ = v_isSharedCheck_117_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_val_104_);
lean_dec(v_a_97_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_117_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 0, v_val_104_);
v___x_109_ = v___x_102_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_val_104_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_proof_x3f_94_);
lean_ctor_set_uint8(v_reuseFailAlloc_116_, sizeof(void*)*2, v_cache_95_);
v___x_109_ = v_reuseFailAlloc_116_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_109_);
v___x_111_ = v___x_106_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_109_);
v___x_111_ = v_reuseFailAlloc_115_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_113_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_111_);
v___x_113_ = v___x_99_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_114_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
return v___x_113_;
}
}
}
}
}
}
else
{
lean_object* v___x_122_; 
lean_dec(v_a_97_);
if (v_isShared_92_ == 0)
{
lean_ctor_set_tag(v___x_91_, 0);
v___x_122_ = v___x_91_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_val_89_);
v___x_122_ = v_reuseFailAlloc_126_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v___x_124_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_122_);
v___x_124_ = v___x_99_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
}
else
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_135_; 
lean_del_object(v___x_91_);
lean_dec(v_val_89_);
v_a_128_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_135_ == 0)
{
v___x_130_ = v___x_96_;
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_96_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_135_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_133_; 
if (v_isShared_131_ == 0)
{
v___x_133_ = v___x_130_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_a_128_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
return v___x_133_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed(lean_object* v_unfoldThm_223_, lean_object* v_e_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre(v_unfoldThm_223_, v_e_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0(lean_object* v_e_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_243_ = lean_box(0);
v___x_244_ = 1;
v___x_245_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_245_, 0, v_e_234_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*2, v___x_244_);
v___x_246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__0___boxed(lean_object* v_e_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_Meta_unfold___lam__0(v_e_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1(lean_object* v_x_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = ((lean_object*)(l_Lean_Meta_unfold___lam__1___closed__0));
v___x_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__1___boxed(lean_object* v_x_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_Meta_unfold___lam__1(v_x_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v_x_271_);
return v_res_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2(lean_object* v_e_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v_e_281_);
v___x_291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__2___boxed(lean_object* v_e_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Lean_Meta_unfold___lam__2(v_e_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3(lean_object* v_x_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__3___boxed(lean_object* v_x_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Meta_unfold___lam__3(v_x_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v_x_313_);
return v_res_322_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_unfold___lam__4(lean_object* v_declName_323_, lean_object* v_x_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = lean_name_eq(v_x_324_, v_declName_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___lam__4___boxed(lean_object* v_declName_326_, lean_object* v_x_327_){
_start:
{
uint8_t v_res_328_; lean_object* v_r_329_; 
v_res_328_ = l_Lean_Meta_unfold___lam__4(v_declName_326_, v_x_327_);
lean_dec(v_x_327_);
lean_dec(v_declName_326_);
v_r_329_ = lean_box(v_res_328_);
return v_r_329_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__4(void){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__5(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_obj_once(&l_Lean_Meta_unfold___closed__4, &l_Lean_Meta_unfold___closed__4_once, _init_l_Lean_Meta_unfold___closed__4);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__6(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__7(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_unsigned_to_nat(32u);
v___x_341_ = lean_mk_empty_array_with_capacity(v___x_340_);
v___x_342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__8(void){
_start:
{
size_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_343_ = ((size_t)5ULL);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_unsigned_to_nat(32u);
v___x_346_ = lean_mk_empty_array_with_capacity(v___x_345_);
v___x_347_ = lean_obj_once(&l_Lean_Meta_unfold___closed__7, &l_Lean_Meta_unfold___closed__7_once, _init_l_Lean_Meta_unfold___closed__7);
v___x_348_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_348_, 0, v___x_347_);
lean_ctor_set(v___x_348_, 1, v___x_346_);
lean_ctor_set(v___x_348_, 2, v___x_344_);
lean_ctor_set(v___x_348_, 3, v___x_344_);
lean_ctor_set_usize(v___x_348_, 4, v___x_343_);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__9(void){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = lean_obj_once(&l_Lean_Meta_unfold___closed__8, &l_Lean_Meta_unfold___closed__8_once, _init_l_Lean_Meta_unfold___closed__8);
v___x_350_ = lean_obj_once(&l_Lean_Meta_unfold___closed__5, &l_Lean_Meta_unfold___closed__5_once, _init_l_Lean_Meta_unfold___closed__5);
v___x_351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
lean_ctor_set(v___x_351_, 2, v___x_350_);
lean_ctor_set(v___x_351_, 3, v___x_349_);
return v___x_351_;
}
}
static lean_object* _init_l_Lean_Meta_unfold___closed__10(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_obj_once(&l_Lean_Meta_unfold___closed__9, &l_Lean_Meta_unfold___closed__9_once, _init_l_Lean_Meta_unfold___closed__9);
v___x_353_ = lean_obj_once(&l_Lean_Meta_unfold___closed__6, &l_Lean_Meta_unfold___closed__6_once, _init_l_Lean_Meta_unfold___closed__6);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold(lean_object* v_e_355_, lean_object* v_declName_356_, lean_object* v_a_357_, lean_object* v_a_358_, lean_object* v_a_359_, lean_object* v_a_360_){
_start:
{
uint8_t v___x_362_; lean_object* v___x_363_; 
v___x_362_ = 0;
lean_inc(v_declName_356_);
v___x_363_ = l_Lean_Meta_getUnfoldEqnFor_x3f(v_declName_356_, v___x_362_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_363_) == 0)
{
lean_object* v_a_364_; 
v_a_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_a_364_);
lean_dec_ref_known(v___x_363_, 1);
if (lean_obj_tag(v_a_364_) == 1)
{
lean_object* v_val_365_; lean_object* v___x_366_; 
lean_dec(v_declName_356_);
v_val_365_ = lean_ctor_get(v_a_364_, 0);
lean_inc(v_val_365_);
lean_dec_ref_known(v_a_364_, 1);
v___x_366_ = l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_getSimpUnfoldContext___redArg(v_a_357_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_object* v_a_367_; lean_object* v___f_368_; lean_object* v___f_369_; lean_object* v___f_370_; lean_object* v___f_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_a_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_a_367_);
lean_dec_ref_known(v___x_366_, 1);
v___f_368_ = ((lean_object*)(l_Lean_Meta_unfold___closed__0));
v___f_369_ = ((lean_object*)(l_Lean_Meta_unfold___closed__1));
v___f_370_ = ((lean_object*)(l_Lean_Meta_unfold___closed__2));
v___f_371_ = ((lean_object*)(l_Lean_Meta_unfold___closed__3));
v___x_372_ = lean_obj_once(&l_Lean_Meta_unfold___closed__10, &l_Lean_Meta_unfold___closed__10_once, _init_l_Lean_Meta_unfold___closed__10);
v___x_373_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Unfold_0__Lean_Meta_unfold_pre___boxed), 10, 1);
lean_closure_set(v___x_373_, 0, v_val_365_);
v___x_374_ = 1;
v___x_375_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___f_368_);
lean_ctor_set(v___x_375_, 2, v___f_369_);
lean_ctor_set(v___x_375_, 3, v___f_370_);
lean_ctor_set(v___x_375_, 4, v___f_371_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*5, v___x_374_);
v___x_376_ = l_Lean_Meta_Simp_main(v_e_355_, v_a_367_, v___x_372_, v___x_375_, v_a_357_, v_a_358_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_385_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_385_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_385_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_fst_381_; lean_object* v___x_383_; 
v_fst_381_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_fst_381_);
lean_dec(v_a_377_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_fst_381_);
v___x_383_ = v___x_379_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_fst_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
else
{
lean_object* v_a_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_393_; 
v_a_386_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_393_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_393_ == 0)
{
v___x_388_ = v___x_376_;
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_a_386_);
lean_dec(v___x_376_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_393_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_391_; 
if (v_isShared_389_ == 0)
{
v___x_391_ = v___x_388_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_a_386_);
v___x_391_ = v_reuseFailAlloc_392_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
return v___x_391_;
}
}
}
}
else
{
lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_401_; 
lean_dec(v_val_365_);
lean_dec_ref(v_e_355_);
v_a_394_ = lean_ctor_get(v___x_366_, 0);
v_isSharedCheck_401_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_401_ == 0)
{
v___x_396_ = v___x_366_;
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_366_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_401_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_400_; 
v_reuseFailAlloc_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_400_, 0, v_a_394_);
v___x_399_ = v_reuseFailAlloc_400_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
return v___x_399_;
}
}
}
}
else
{
lean_object* v___f_402_; lean_object* v___x_403_; 
lean_dec(v_a_364_);
v___f_402_ = lean_alloc_closure((void*)(l_Lean_Meta_unfold___lam__4___boxed), 2, 1);
lean_closure_set(v___f_402_, 0, v_declName_356_);
v___x_403_ = l_Lean_Meta_deltaExpand(v_e_355_, v___f_402_, v___x_362_, v_a_359_, v_a_360_);
if (lean_obj_tag(v___x_403_) == 0)
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_414_; 
v_a_404_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_414_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_414_ == 0)
{
v___x_406_ = v___x_403_;
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_403_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_414_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; uint8_t v___x_409_; lean_object* v___x_410_; lean_object* v___x_412_; 
v___x_408_ = lean_box(0);
v___x_409_ = 1;
v___x_410_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_410_, 0, v_a_404_);
lean_ctor_set(v___x_410_, 1, v___x_408_);
lean_ctor_set_uint8(v___x_410_, sizeof(void*)*2, v___x_409_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_410_);
v___x_412_ = v___x_406_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
}
}
}
else
{
lean_object* v_a_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
v_a_415_ = lean_ctor_get(v___x_403_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_403_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v___x_403_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_a_415_);
lean_dec(v___x_403_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_a_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
lean_dec(v_declName_356_);
lean_dec_ref(v_e_355_);
v_a_423_ = lean_ctor_get(v___x_363_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_363_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_363_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_363_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfold___boxed(lean_object* v_e_431_, lean_object* v_declName_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_Meta_unfold(v_e_431_, v_declName_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_);
lean_dec(v_a_436_);
lean_dec_ref(v_a_435_);
lean_dec(v_a_434_);
lean_dec_ref(v_a_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(lean_object* v_e_439_, lean_object* v___y_440_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = l_Lean_Expr_hasMVar(v_e_439_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
v___x_443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_443_, 0, v_e_439_);
return v___x_443_;
}
else
{
lean_object* v___x_444_; lean_object* v_mctx_445_; lean_object* v___x_446_; lean_object* v_fst_447_; lean_object* v_snd_448_; lean_object* v___x_449_; lean_object* v_cache_450_; lean_object* v_zetaDeltaFVarIds_451_; lean_object* v_postponed_452_; lean_object* v_diag_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_462_; 
v___x_444_ = lean_st_ref_get(v___y_440_);
v_mctx_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc_ref(v_mctx_445_);
lean_dec(v___x_444_);
v___x_446_ = l_Lean_instantiateMVarsCore(v_mctx_445_, v_e_439_);
v_fst_447_ = lean_ctor_get(v___x_446_, 0);
lean_inc(v_fst_447_);
v_snd_448_ = lean_ctor_get(v___x_446_, 1);
lean_inc(v_snd_448_);
lean_dec_ref(v___x_446_);
v___x_449_ = lean_st_ref_take(v___y_440_);
v_cache_450_ = lean_ctor_get(v___x_449_, 1);
v_zetaDeltaFVarIds_451_ = lean_ctor_get(v___x_449_, 2);
v_postponed_452_ = lean_ctor_get(v___x_449_, 3);
v_diag_453_ = lean_ctor_get(v___x_449_, 4);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_449_);
if (v_isSharedCheck_462_ == 0)
{
lean_object* v_unused_463_; 
v_unused_463_ = lean_ctor_get(v___x_449_, 0);
lean_dec(v_unused_463_);
v___x_455_ = v___x_449_;
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_diag_453_);
lean_inc(v_postponed_452_);
lean_inc(v_zetaDeltaFVarIds_451_);
lean_inc(v_cache_450_);
lean_dec(v___x_449_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_462_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v_snd_448_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_snd_448_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v_cache_450_);
lean_ctor_set(v_reuseFailAlloc_461_, 2, v_zetaDeltaFVarIds_451_);
lean_ctor_set(v_reuseFailAlloc_461_, 3, v_postponed_452_);
lean_ctor_set(v_reuseFailAlloc_461_, 4, v_diag_453_);
v___x_458_ = v_reuseFailAlloc_461_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_459_; lean_object* v___x_460_; 
v___x_459_ = lean_st_ref_set(v___y_440_, v___x_458_);
v___x_460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_460_, 0, v_fst_447_);
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg___boxed(lean_object* v_e_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_464_, v___y_465_);
lean_dec(v___y_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(lean_object* v_e_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_e_468_, v___y_470_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___boxed(lean_object* v_e_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0(v_e_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(lean_object* v_mvarId_482_, lean_object* v_x_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
v___x_489_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_482_, v_x_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_489_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg___boxed(lean_object* v_mvarId_506_, lean_object* v_x_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_506_, v_x_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec_ref(v___y_508_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(lean_object* v_00_u03b1_514_, lean_object* v_mvarId_515_, lean_object* v_x_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_515_, v_x_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
return v___x_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___boxed(lean_object* v_00_u03b1_523_, lean_object* v_mvarId_524_, lean_object* v_x_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2(v_00_u03b1_523_, v_mvarId_524_, v_x_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(lean_object* v_msgData_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
lean_object* v___x_538_; lean_object* v_env_539_; lean_object* v___x_540_; lean_object* v_mctx_541_; lean_object* v_lctx_542_; lean_object* v_options_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_538_ = lean_st_ref_get(v___y_536_);
v_env_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc_ref(v_env_539_);
lean_dec(v___x_538_);
v___x_540_ = lean_st_ref_get(v___y_534_);
v_mctx_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc_ref(v_mctx_541_);
lean_dec(v___x_540_);
v_lctx_542_ = lean_ctor_get(v___y_533_, 2);
v_options_543_ = lean_ctor_get(v___y_535_, 2);
lean_inc_ref(v_options_543_);
lean_inc_ref(v_lctx_542_);
v___x_544_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_544_, 0, v_env_539_);
lean_ctor_set(v___x_544_, 1, v_mctx_541_);
lean_ctor_set(v___x_544_, 2, v_lctx_542_);
lean_ctor_set(v___x_544_, 3, v_options_543_);
v___x_545_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_544_);
lean_ctor_set(v___x_545_, 1, v_msgData_532_);
v___x_546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1___boxed(lean_object* v_msgData_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msgData_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(lean_object* v_msg_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_ref_560_; lean_object* v___x_561_; lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_570_; 
v_ref_560_ = lean_ctor_get(v___y_557_, 5);
v___x_561_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1_spec__1(v_msg_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_570_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_570_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
lean_inc(v_ref_560_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v_ref_560_);
lean_ctor_set(v___x_566_, 1, v_a_562_);
if (v_isShared_565_ == 0)
{
lean_ctor_set_tag(v___x_564_, 1);
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg___boxed(lean_object* v_msg_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v___y_573_);
lean_dec_ref(v___y_572_);
return v_res_577_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_Meta_unfoldTarget___lam__0___closed__0));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l_Lean_Meta_unfoldTarget___lam__0___closed__2));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0(lean_object* v_mvarId_584_, lean_object* v_declName_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; 
lean_inc(v_mvarId_584_);
v___x_591_ = l_Lean_MVarId_getType(v_mvarId_584_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v___x_595_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
lean_inc(v_a_592_);
lean_dec_ref_known(v___x_591_, 1);
v___x_593_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_592_, v___y_587_);
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc_n(v_a_594_, 2);
lean_dec_ref(v___x_593_);
lean_inc(v_declName_585_);
v___x_595_ = l_Lean_Meta_unfold(v_a_594_, v_declName_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v_expr_597_; uint8_t v___x_598_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v_expr_597_ = lean_ctor_get(v_a_596_, 0);
v___x_598_ = lean_expr_eqv(v_expr_597_, v_a_594_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
lean_dec(v_declName_585_);
v___x_599_ = l_Lean_Meta_applySimpResultToTarget(v_mvarId_584_, v_a_594_, v_a_596_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
lean_dec(v_a_594_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; uint8_t v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v_a_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_616_; 
lean_dec(v_a_596_);
lean_dec(v_mvarId_584_);
v___x_600_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_601_ = 0;
v___x_602_ = l_Lean_MessageData_ofConstName(v_declName_585_, v___x_601_);
v___x_603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_600_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
v___x_604_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_603_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_indentExpr(v_a_594_);
v___x_607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_605_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_607_, v___y_586_, v___y_587_, v___y_588_, v___y_589_);
v_a_609_ = lean_ctor_get(v___x_608_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_616_ == 0)
{
v___x_611_ = v___x_608_;
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_a_609_);
lean_dec(v___x_608_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_616_;
goto v_resetjp_610_;
}
v_resetjp_610_:
{
lean_object* v___x_614_; 
if (v_isShared_612_ == 0)
{
v___x_614_ = v___x_611_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
else
{
lean_object* v_a_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
lean_dec(v_a_594_);
lean_dec(v_declName_585_);
lean_dec(v_mvarId_584_);
v_a_617_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_624_ == 0)
{
v___x_619_ = v___x_595_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_a_617_);
lean_dec(v___x_595_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_617_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
}
else
{
lean_object* v_a_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_632_; 
lean_dec(v_declName_585_);
lean_dec(v_mvarId_584_);
v_a_625_ = lean_ctor_get(v___x_591_, 0);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_591_);
if (v_isSharedCheck_632_ == 0)
{
v___x_627_ = v___x_591_;
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_a_625_);
lean_dec(v___x_591_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_632_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_630_; 
if (v_isShared_628_ == 0)
{
v___x_630_ = v___x_627_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v_a_625_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___lam__0___boxed(lean_object* v_mvarId_633_, lean_object* v_declName_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Lean_Meta_unfoldTarget___lam__0(v_mvarId_633_, v_declName_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget(lean_object* v_mvarId_641_, lean_object* v_declName_642_, lean_object* v_a_643_, lean_object* v_a_644_, lean_object* v_a_645_, lean_object* v_a_646_){
_start:
{
lean_object* v___f_648_; lean_object* v___x_649_; 
lean_inc(v_mvarId_641_);
v___f_648_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_648_, 0, v_mvarId_641_);
lean_closure_set(v___f_648_, 1, v_declName_642_);
v___x_649_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_641_, v___f_648_, v_a_643_, v_a_644_, v_a_645_, v_a_646_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldTarget___boxed(lean_object* v_mvarId_650_, lean_object* v_declName_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_Meta_unfoldTarget(v_mvarId_650_, v_declName_651_, v_a_652_, v_a_653_, v_a_654_, v_a_655_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec(v_a_653_);
lean_dec_ref(v_a_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(lean_object* v_00_u03b1_658_, lean_object* v_msg_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v_msg_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___boxed(lean_object* v_00_u03b1_666_, lean_object* v_msg_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1(v_00_u03b1_666_, v_msg_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(lean_object* v_msg_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___f_681_; lean_object* v___x_976__overap_682_; lean_object* v___x_683_; 
v___f_681_ = ((lean_object*)(l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___closed__0));
v___x_976__overap_682_ = lean_panic_fn_borrowed(v___f_681_, v_msg_675_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
v___x_683_ = lean_apply_5(v___x_976__overap_682_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, lean_box(0));
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0___boxed(lean_object* v_msg_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v_msg_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_690_;
}
}
static lean_object* _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_694_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__2));
v___x_695_ = lean_unsigned_to_nat(94u);
v___x_696_ = lean_unsigned_to_nat(43u);
v___x_697_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__1));
v___x_698_ = ((lean_object*)(l_Lean_Meta_unfoldLocalDecl___lam__0___closed__0));
v___x_699_ = l_mkPanicMessageWithDecl(v___x_698_, v___x_697_, v___x_696_, v___x_695_, v___x_694_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0(lean_object* v_fvarId_700_, lean_object* v_declName_701_, lean_object* v_mvarId_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v___x_708_; 
lean_inc(v_fvarId_700_);
v___x_708_ = l_Lean_FVarId_getType___redArg(v_fvarId_700_, v___y_703_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_710_; lean_object* v_a_711_; lean_object* v___x_712_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
lean_inc_n(v_a_709_, 2);
lean_dec_ref_known(v___x_708_, 1);
v___x_710_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_709_, v___y_704_);
v_a_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_a_711_);
lean_dec_ref(v___x_710_);
lean_inc(v_declName_701_);
v___x_712_ = l_Lean_Meta_unfold(v_a_711_, v_declName_701_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v_a_713_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v_expr_741_; uint8_t v___x_742_; 
v_a_713_ = lean_ctor_get(v___x_712_, 0);
lean_inc(v_a_713_);
lean_dec_ref_known(v___x_712_, 1);
v_expr_741_ = lean_ctor_get(v_a_713_, 0);
v___x_742_ = lean_expr_eqv(v_expr_741_, v_a_709_);
if (v___x_742_ == 0)
{
lean_dec(v_a_709_);
lean_dec(v_declName_701_);
v___y_715_ = v___y_703_;
v___y_716_ = v___y_704_;
v___y_717_ = v___y_705_;
v___y_718_ = v___y_706_;
goto v___jp_714_;
}
else
{
lean_object* v___x_743_; uint8_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v_a_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_759_; 
lean_dec(v_a_713_);
lean_dec(v_mvarId_702_);
lean_dec(v_fvarId_700_);
v___x_743_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_744_ = 0;
v___x_745_ = l_Lean_MessageData_ofConstName(v_declName_701_, v___x_744_);
v___x_746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_743_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_746_);
lean_ctor_set(v___x_748_, 1, v___x_747_);
v___x_749_ = l_Lean_indentExpr(v_a_709_);
v___x_750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_749_);
v___x_751_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_750_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
v_a_752_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_759_ == 0)
{
v___x_754_ = v___x_751_;
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_a_752_);
lean_dec(v___x_751_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_759_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_757_; 
if (v_isShared_755_ == 0)
{
v___x_757_ = v___x_754_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
v___jp_714_:
{
uint8_t v___x_719_; lean_object* v___x_720_; 
v___x_719_ = 0;
v___x_720_ = l_Lean_Meta_applySimpResultToLocalDecl(v_mvarId_702_, v_fvarId_700_, v_a_713_, v___x_719_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
if (lean_obj_tag(v___x_720_) == 0)
{
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_732_; 
v_a_721_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_732_ == 0)
{
v___x_723_ = v___x_720_;
v_isShared_724_ = v_isSharedCheck_732_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_732_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
if (lean_obj_tag(v_a_721_) == 1)
{
lean_object* v_val_725_; lean_object* v_snd_726_; lean_object* v___x_728_; 
v_val_725_ = lean_ctor_get(v_a_721_, 0);
lean_inc(v_val_725_);
lean_dec_ref_known(v_a_721_, 1);
v_snd_726_ = lean_ctor_get(v_val_725_, 1);
lean_inc(v_snd_726_);
lean_dec(v_val_725_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 0, v_snd_726_);
v___x_728_ = v___x_723_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_snd_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
else
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_del_object(v___x_723_);
lean_dec(v_a_721_);
v___x_730_ = lean_obj_once(&l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3, &l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldLocalDecl___lam__0___closed__3);
v___x_731_ = l_panic___at___00Lean_Meta_unfoldLocalDecl_spec__0(v___x_730_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
return v___x_731_;
}
}
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v___x_720_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_720_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_720_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_720_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec(v_a_709_);
lean_dec(v_mvarId_702_);
lean_dec(v_declName_701_);
lean_dec(v_fvarId_700_);
v_a_760_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_712_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_712_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v_mvarId_702_);
lean_dec(v_declName_701_);
lean_dec(v_fvarId_700_);
v_a_768_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_708_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_708_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl___lam__0___boxed(lean_object* v_fvarId_776_, lean_object* v_declName_777_, lean_object* v_mvarId_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Meta_unfoldLocalDecl___lam__0(v_fvarId_776_, v_declName_777_, v_mvarId_778_, v___y_779_, v___y_780_, v___y_781_, v___y_782_);
lean_dec(v___y_782_);
lean_dec_ref(v___y_781_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unfoldLocalDecl(lean_object* v_mvarId_785_, lean_object* v_fvarId_786_, lean_object* v_declName_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___f_793_; lean_object* v___x_794_; 
lean_inc(v_mvarId_785_);
v___f_793_ = lean_alloc_closure((void*)(l_Lean_Meta_unfoldLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_793_, 0, v_fvarId_786_);
lean_closure_set(v___f_793_, 1, v_declName_787_);
lean_closure_set(v___f_793_, 2, v_mvarId_785_);
v___x_794_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_785_, v___f_793_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
return v___x_794_;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0(lean_object* v_mvarId_804_, lean_object* v_declFVarId_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
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
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___lam__0___boxed(lean_object* v_mvarId_855_, lean_object* v_declFVarId_856_, lean_object* v___y_857_, lean_object* v___y_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Meta_zetaDeltaTarget___lam__0(v_mvarId_855_, v_declFVarId_856_, v___y_857_, v___y_858_, v___y_859_, v___y_860_);
lean_dec(v___y_860_);
lean_dec_ref(v___y_859_);
lean_dec(v___y_858_);
lean_dec_ref(v___y_857_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget(lean_object* v_mvarId_863_, lean_object* v_declFVarId_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v___f_870_; lean_object* v___x_871_; 
lean_inc(v_mvarId_863_);
v___f_870_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaTarget___lam__0___boxed), 7, 2);
lean_closure_set(v___f_870_, 0, v_mvarId_863_);
lean_closure_set(v___f_870_, 1, v_declFVarId_864_);
v___x_871_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_863_, v___f_870_, v_a_865_, v_a_866_, v_a_867_, v_a_868_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaTarget___boxed(lean_object* v_mvarId_872_, lean_object* v_declFVarId_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_Meta_zetaDeltaTarget(v_mvarId_872_, v_declFVarId_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0(lean_object* v_fvarId_880_, lean_object* v_declFVarId_881_, lean_object* v_mvarId_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v___x_888_; 
lean_inc(v_fvarId_880_);
v___x_888_ = l_Lean_FVarId_getType___redArg(v_fvarId_880_, v___y_883_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc_n(v_a_889_, 2);
lean_dec_ref_known(v___x_888_, 1);
v___x_890_ = l_Lean_instantiateMVars___at___00Lean_Meta_unfoldTarget_spec__0___redArg(v_a_889_, v___y_884_);
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_890_);
v___x_892_ = lean_unsigned_to_nat(1u);
v___x_893_ = lean_mk_empty_array_with_capacity(v___x_892_);
v___x_894_ = lean_array_push(v___x_893_, v_declFVarId_881_);
v___x_895_ = l_Lean_Meta_zetaDeltaFVars(v_a_891_, v___x_894_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; uint8_t v___x_897_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v___x_897_ = lean_expr_eqv(v_a_896_, v_a_889_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec(v_a_889_);
v___x_898_ = l_Lean_MVarId_replaceLocalDeclDefEq(v_mvarId_882_, v_fvarId_880_, v_a_896_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
lean_dec(v_a_896_);
lean_dec(v_mvarId_882_);
v___x_899_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__1, &l_Lean_Meta_unfoldTarget___lam__0___closed__1_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__1);
v___x_900_ = l_Lean_Expr_fvar___override(v_fvarId_880_);
v___x_901_ = l_Lean_MessageData_ofExpr(v___x_900_);
v___x_902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_899_);
lean_ctor_set(v___x_902_, 1, v___x_901_);
v___x_903_ = lean_obj_once(&l_Lean_Meta_unfoldTarget___lam__0___closed__3, &l_Lean_Meta_unfoldTarget___lam__0___closed__3_once, _init_l_Lean_Meta_unfoldTarget___lam__0___closed__3);
v___x_904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = l_Lean_indentExpr(v_a_889_);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_904_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
v___x_907_ = l_Lean_throwError___at___00Lean_Meta_unfoldTarget_spec__1___redArg(v___x_906_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
v_a_908_ = lean_ctor_get(v___x_907_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_907_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_907_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_907_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_a_889_);
lean_dec(v_mvarId_882_);
lean_dec(v_fvarId_880_);
v_a_916_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_895_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_895_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_mvarId_882_);
lean_dec(v_declFVarId_881_);
lean_dec(v_fvarId_880_);
v_a_924_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_888_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_888_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed(lean_object* v_fvarId_932_, lean_object* v_declFVarId_933_, lean_object* v_mvarId_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_Meta_zetaDeltaLocalDecl___lam__0(v_fvarId_932_, v_declFVarId_933_, v_mvarId_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl(lean_object* v_mvarId_941_, lean_object* v_fvarId_942_, lean_object* v_declFVarId_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_){
_start:
{
lean_object* v___f_949_; lean_object* v___x_950_; 
lean_inc(v_mvarId_941_);
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Meta_zetaDeltaLocalDecl___lam__0___boxed), 8, 3);
lean_closure_set(v___f_949_, 0, v_fvarId_942_);
lean_closure_set(v___f_949_, 1, v_declFVarId_943_);
lean_closure_set(v___f_949_, 2, v_mvarId_941_);
v___x_950_ = l_Lean_MVarId_withContext___at___00Lean_Meta_unfoldTarget_spec__2___redArg(v_mvarId_941_, v___f_949_, v_a_944_, v_a_945_, v_a_946_, v_a_947_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_zetaDeltaLocalDecl___boxed(lean_object* v_mvarId_951_, lean_object* v_fvarId_952_, lean_object* v_declFVarId_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Meta_zetaDeltaLocalDecl(v_mvarId_951_, v_fvarId_952_, v_declFVarId_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
return v_res_959_;
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
