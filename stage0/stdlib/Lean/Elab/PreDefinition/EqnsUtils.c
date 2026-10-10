// Lean compiler output
// Module: Lean.Elab.PreDefinition.EqnsUtils
// Imports: public import Lean.Meta.Basic import Lean.Meta.Tactic.Split import Lean.Meta.Tactic.Refl import Lean.Meta.Tactic.Delta import Lean.Meta.Tactic.SplitIf import Lean.Meta.Tactic.Contradiction
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
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpIfTarget(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint16_t l_Lean_OptionFlags_ofOptions(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint16_t lean_uint16_land(uint16_t, uint16_t);
uint8_t lean_uint16_dec_eq(uint16_t, uint16_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
lean_object* l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Eqns_tryURefl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_tryURefl___closed__0;
static lean_once_cell_t l_Lean_Elab_Eqns_tryURefl___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_tryURefl___closed__1;
static lean_once_cell_t l_Lean_Elab_Eqns_tryURefl___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_tryURefl___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deltaLHS"};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(208, 64, 102, 150, 180, 16, 252, 96)}};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3_value;
static const lean_string_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "equality expected"};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__4_value)}};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6;
static lean_once_cell_t l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7;
static const lean_string_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "failed to delta reduce lhs"};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__8_value)}};
static const lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10;
static lean_once_cell_t l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Eqns_tryContradiction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(16) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 1, 1, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Eqns_tryContradiction___closed__0 = (const lean_object*)&l_Lean_Elab_Eqns_tryContradiction___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(lean_object*);
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0;
static const lean_string_object l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2_value;
static const lean_string_object l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3 = (const lean_object*)&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3_value;
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object* v_mvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
lean_inc(v_mvarId_1_);
v___x_7_ = l_Lean_Meta_Split_simpMatchTarget(v_mvarId_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_21_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_21_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_21_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint8_t v___x_12_; 
v___x_12_ = l_Lean_instBEqMVarId_beq(v_mvarId_1_, v_a_8_);
lean_dec(v_mvarId_1_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; lean_object* v___x_15_; 
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v_a_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_13_);
v___x_15_ = v___x_10_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v___x_13_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
else
{
lean_object* v___x_17_; lean_object* v___x_19_; 
lean_dec(v_a_8_);
v___x_17_ = lean_box(0);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_17_);
v___x_19_ = v___x_10_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v___x_17_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
else
{
lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_mvarId_1_);
v_a_22_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v___x_7_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_dec(v___x_7_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_a_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Eqns_simpMatch_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f___boxed(lean_object* v_mvarId_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
return v_res_37_;
}
}
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object* v_mvarId_38_, uint8_t v_useNewSemantics_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
uint8_t v___x_45_; lean_object* v___x_46_; 
v___x_45_ = 1;
lean_inc(v_mvarId_38_);
v___x_46_ = l_Lean_Meta_simpIfTarget(v_mvarId_38_, v___x_45_, v_useNewSemantics_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_60_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_60_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_60_ == 0)
{
v___x_49_ = v___x_46_;
v_isShared_50_ = v_isSharedCheck_60_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_60_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
uint8_t v___x_51_; 
v___x_51_ = l_Lean_instBEqMVarId_beq(v_mvarId_38_, v_a_47_);
lean_dec(v_mvarId_38_);
if (v___x_51_ == 0)
{
lean_object* v___x_52_; lean_object* v___x_54_; 
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_a_47_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_52_);
v___x_54_ = v___x_49_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v___x_52_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
else
{
lean_object* v___x_56_; lean_object* v___x_58_; 
lean_dec(v_a_47_);
v___x_56_ = lean_box(0);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_56_);
v___x_58_ = v___x_49_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
else
{
lean_object* v_a_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_68_; 
lean_dec(v_mvarId_38_);
v_a_61_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_68_ == 0)
{
v___x_63_ = v___x_46_;
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_a_61_);
lean_dec(v___x_46_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_68_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_66_; 
if (v_isShared_64_ == 0)
{
v___x_66_ = v___x_63_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_a_61_);
v___x_66_ = v_reuseFailAlloc_67_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
return v___x_66_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Eqns_simpIf_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_38_ = stack[0].m_obj;
uint8_t v_useNewSemantics_39_ = stack[1].m_num;
lean_object* v_a_40_ = stack[2].m_obj;
lean_object* v_a_41_ = stack[3].m_obj;
lean_object* v_a_42_ = stack[4].m_obj;
lean_object* v_a_43_ = stack[5].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_38_, v_useNewSemantics_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f___boxed(lean_object* v_mvarId_70_, lean_object* v_useNewSemantics_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
uint8_t v_useNewSemantics_boxed_77_; lean_object* v_res_78_; 
v_useNewSemantics_boxed_77_ = lean_unbox(v_useNewSemantics_71_);
v_res_78_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_70_, v_useNewSemantics_boxed_77_, v_a_72_, v_a_73_, v_a_74_, v_a_75_);
lean_dec(v_a_75_);
lean_dec_ref(v_a_74_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
return v_res_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0(lean_object* v_opts_79_, lean_object* v_opt_80_){
_start:
{
lean_object* v_name_81_; lean_object* v_defValue_82_; lean_object* v_map_83_; lean_object* v___x_84_; 
v_name_81_ = lean_ctor_get(v_opt_80_, 0);
v_defValue_82_ = lean_ctor_get(v_opt_80_, 1);
v_map_83_ = lean_ctor_get(v_opts_79_, 0);
v___x_84_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_83_, v_name_81_);
if (lean_obj_tag(v___x_84_) == 0)
{
lean_inc(v_defValue_82_);
return v_defValue_82_;
}
else
{
lean_object* v_val_85_; 
v_val_85_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_val_85_);
lean_dec_ref_known(v___x_84_, 1);
if (lean_obj_tag(v_val_85_) == 3)
{
lean_object* v_v_86_; 
v_v_86_ = lean_ctor_get(v_val_85_, 0);
lean_inc(v_v_86_);
lean_dec_ref_known(v_val_85_, 1);
return v_v_86_;
}
else
{
lean_dec(v_val_85_);
lean_inc(v_defValue_82_);
return v_defValue_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0___boxed(lean_object* v_opts_87_, lean_object* v_opt_88_){
_start:
{
lean_object* v_res_89_; 
v_res_89_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0(v_opts_87_, v_opt_88_);
lean_dec_ref(v_opt_88_);
lean_dec_ref(v_opts_87_);
return v_res_89_;
}
}
lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(lean_object* v_o_93_, lean_object* v_k_94_, uint8_t v_v_95_){
_start:
{
lean_object* v_map_96_; uint8_t v_hasTrace_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_111_; 
v_map_96_ = lean_ctor_get(v_o_93_, 0);
v_hasTrace_97_ = lean_ctor_get_uint8(v_o_93_, sizeof(void*)*1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_o_93_);
if (v_isSharedCheck_111_ == 0)
{
v___x_99_ = v_o_93_;
v_isShared_100_ = v_isSharedCheck_111_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_map_96_);
lean_dec(v_o_93_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_111_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_101_, 0, v_v_95_);
lean_inc(v_k_94_);
v___x_102_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_94_, v___x_101_, v_map_96_);
if (v_hasTrace_97_ == 0)
{
lean_object* v___x_103_; uint8_t v___x_104_; lean_object* v___x_106_; 
v___x_103_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___closed__1));
v___x_104_ = l_Lean_Name_isPrefixOf(v___x_103_, v_k_94_);
lean_dec(v_k_94_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_102_);
v___x_106_ = v___x_99_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_102_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_ctor_set_uint8(v___x_106_, sizeof(void*)*1, v___x_104_);
return v___x_106_;
}
}
else
{
lean_object* v___x_109_; 
lean_dec(v_k_94_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 0, v___x_102_);
v___x_109_ = v___x_99_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_102_);
lean_ctor_set_uint8(v_reuseFailAlloc_110_, sizeof(void*)*1, v_hasTrace_97_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_93_ = stack[0].m_obj;
lean_object* v_k_94_ = stack[1].m_obj;
uint8_t v_v_95_ = stack[2].m_num;
lean_object* v_res_112_;
v_res_112_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(v_o_93_, v_k_94_, v_v_95_);
stack->m_obj
 = v_res_112_;
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___boxed(lean_object* v_o_113_, lean_object* v_k_114_, lean_object* v_v_115_){
_start:
{
uint8_t v_v_boxed_116_; lean_object* v_res_117_; 
v_v_boxed_116_ = lean_unbox(v_v_115_);
v_res_117_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(v_o_113_, v_k_114_, v_v_boxed_116_);
return v_res_117_;
}
}
lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1(lean_object* v_opts_118_, lean_object* v_opt_119_, uint8_t v_val_120_){
_start:
{
lean_object* v_name_121_; lean_object* v___x_122_; 
v_name_121_ = lean_ctor_get(v_opt_119_, 0);
lean_inc(v_name_121_);
lean_dec_ref(v_opt_119_);
v___x_122_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(v_opts_118_, v_name_121_, v_val_120_);
return v___x_122_;
}
}
LEAN_EXPORT void l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_118_ = stack[0].m_obj;
lean_object* v_opt_119_ = stack[1].m_obj;
uint8_t v_val_120_ = stack[2].m_num;
lean_object* v_res_123_;
v_res_123_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_opts_118_, v_opt_119_, v_val_120_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1___boxed(lean_object* v_opts_124_, lean_object* v_opt_125_, lean_object* v_val_126_){
_start:
{
uint8_t v_val_boxed_127_; lean_object* v_res_128_; 
v_val_boxed_127_ = lean_unbox(v_val_126_);
v_res_128_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_opts_124_, v_opt_125_, v_val_boxed_127_);
return v_res_128_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__0(void){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__1(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__0, &l_Lean_Elab_Eqns_tryURefl___closed__0_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__0);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
return v___x_131_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__2(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__1, &l_Lean_Elab_Eqns_tryURefl___closed__1_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__1);
v___x_133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
return v___x_133_;
}
}
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object* v_mvarId_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___y_141_; uint8_t v___y_142_; lean_object* v_toCold_146_; lean_object* v_currRecDepth_147_; lean_object* v_ref_148_; uint8_t v_suppressElabErrors_149_; uint8_t v_isRecordingDeps_150_; lean_object* v_fileName_151_; lean_object* v_fileMap_152_; lean_object* v_options_153_; lean_object* v_currNamespace_154_; lean_object* v_openDecls_155_; lean_object* v_initHeartbeats_156_; lean_object* v_maxHeartbeats_157_; lean_object* v_quotContext_158_; lean_object* v_currMacroScope_159_; lean_object* v_cancelTk_x3f_160_; lean_object* v_inheritedTraceOptions_161_; uint8_t v___x_162_; lean_object* v___y_164_; uint16_t v___y_165_; lean_object* v_fileName_166_; lean_object* v_fileMap_167_; lean_object* v_currNamespace_168_; lean_object* v_openDecls_169_; lean_object* v_initHeartbeats_170_; lean_object* v_maxHeartbeats_171_; lean_object* v_quotContext_172_; lean_object* v_currMacroScope_173_; lean_object* v_cancelTk_x3f_174_; lean_object* v_inheritedTraceOptions_175_; lean_object* v_currRecDepth_176_; lean_object* v_ref_177_; uint8_t v_suppressElabErrors_178_; uint8_t v_isRecordingDeps_179_; lean_object* v___y_180_; lean_object* v___y_199_; uint16_t v___y_200_; uint8_t v___y_201_; lean_object* v___y_224_; 
v_toCold_146_ = lean_ctor_get(v_a_137_, 0);
v_currRecDepth_147_ = lean_ctor_get(v_a_137_, 1);
v_ref_148_ = lean_ctor_get(v_a_137_, 2);
v_suppressElabErrors_149_ = lean_ctor_get_uint8(v_a_137_, sizeof(void*)*3 + 2);
v_isRecordingDeps_150_ = lean_ctor_get_uint8(v_a_137_, sizeof(void*)*3 + 3);
v_fileName_151_ = lean_ctor_get(v_toCold_146_, 0);
v_fileMap_152_ = lean_ctor_get(v_toCold_146_, 1);
v_options_153_ = lean_ctor_get(v_toCold_146_, 2);
v_currNamespace_154_ = lean_ctor_get(v_toCold_146_, 4);
v_openDecls_155_ = lean_ctor_get(v_toCold_146_, 5);
v_initHeartbeats_156_ = lean_ctor_get(v_toCold_146_, 6);
v_maxHeartbeats_157_ = lean_ctor_get(v_toCold_146_, 7);
v_quotContext_158_ = lean_ctor_get(v_toCold_146_, 8);
v_currMacroScope_159_ = lean_ctor_get(v_toCold_146_, 9);
v_cancelTk_x3f_160_ = lean_ctor_get(v_toCold_146_, 10);
v_inheritedTraceOptions_161_ = lean_ctor_get(v_toCold_146_, 11);
v___x_162_ = 1;
if (v_isRecordingDeps_150_ == 0)
{
lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_234_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_153_);
v___x_235_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_options_153_, v___x_234_, v_isRecordingDeps_150_);
v___y_224_ = v___x_235_;
goto v___jp_223_;
}
else
{
lean_object* v___x_236_; 
lean_inc_ref(v_options_153_);
v___x_236_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_153_);
v___y_224_ = v___x_236_;
goto v___jp_223_;
}
v___jp_140_:
{
if (v___y_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
lean_dec_ref(v___y_141_);
v___x_143_ = lean_box(v___y_142_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; 
v___x_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_145_, 0, v___y_141_);
return v___x_145_;
}
}
v___jp_163_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_181_ = l_Lean_maxRecDepth;
v___x_182_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0(v___y_164_, v___x_181_);
v___x_183_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_183_, 0, v_fileName_166_);
lean_ctor_set(v___x_183_, 1, v_fileMap_167_);
lean_ctor_set(v___x_183_, 2, v___y_164_);
lean_ctor_set(v___x_183_, 3, v___x_182_);
lean_ctor_set(v___x_183_, 4, v_currNamespace_168_);
lean_ctor_set(v___x_183_, 5, v_openDecls_169_);
lean_ctor_set(v___x_183_, 6, v_initHeartbeats_170_);
lean_ctor_set(v___x_183_, 7, v_maxHeartbeats_171_);
lean_ctor_set(v___x_183_, 8, v_quotContext_172_);
lean_ctor_set(v___x_183_, 9, v_currMacroScope_173_);
lean_ctor_set(v___x_183_, 10, v_cancelTk_x3f_174_);
lean_ctor_set(v___x_183_, 11, v_inheritedTraceOptions_175_);
lean_inc(v_ref_177_);
lean_inc(v_currRecDepth_176_);
v___x_184_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_currRecDepth_176_);
lean_ctor_set(v___x_184_, 2, v_ref_177_);
lean_ctor_set_uint16(v___x_184_, sizeof(void*)*3, v___y_165_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3 + 2, v_suppressElabErrors_178_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*3 + 3, v_isRecordingDeps_179_);
v___x_185_ = l_Lean_MVarId_refl(v_mvarId_134_, v___x_162_, v_a_135_, v_a_136_, v___x_184_, v___y_180_);
lean_dec_ref_known(v___x_184_, 3);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_193_ == 0)
{
lean_object* v_unused_194_; 
v_unused_194_ = lean_ctor_get(v___x_185_, 0);
lean_dec(v_unused_194_);
v___x_187_ = v___x_185_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_dec(v___x_185_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_189_ = lean_box(v___x_162_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v___x_189_);
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
else
{
lean_object* v_a_195_; uint8_t v___x_196_; 
v_a_195_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_195_);
lean_dec_ref_known(v___x_185_, 1);
v___x_196_ = l_Lean_Exception_isInterrupt(v_a_195_);
if (v___x_196_ == 0)
{
uint8_t v___x_197_; 
lean_inc(v_a_195_);
v___x_197_ = l_Lean_Exception_isRuntime(v_a_195_);
v___y_141_ = v_a_195_;
v___y_142_ = v___x_197_;
goto v___jp_140_;
}
else
{
v___y_141_ = v_a_195_;
v___y_142_ = v___x_196_;
goto v___jp_140_;
}
}
}
v___jp_198_:
{
lean_object* v___x_202_; lean_object* v_env_203_; lean_object* v_nextMacroScope_204_; lean_object* v_ngen_205_; lean_object* v_auxDeclNGen_206_; lean_object* v_traceState_207_; lean_object* v_recordedDeps_208_; lean_object* v_messages_209_; lean_object* v_infoState_210_; lean_object* v_snapshotTasks_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_221_; 
v___x_202_ = lean_st_ref_take(v_a_138_);
v_env_203_ = lean_ctor_get(v___x_202_, 0);
v_nextMacroScope_204_ = lean_ctor_get(v___x_202_, 1);
v_ngen_205_ = lean_ctor_get(v___x_202_, 2);
v_auxDeclNGen_206_ = lean_ctor_get(v___x_202_, 3);
v_traceState_207_ = lean_ctor_get(v___x_202_, 4);
v_recordedDeps_208_ = lean_ctor_get(v___x_202_, 6);
v_messages_209_ = lean_ctor_get(v___x_202_, 7);
v_infoState_210_ = lean_ctor_get(v___x_202_, 8);
v_snapshotTasks_211_ = lean_ctor_get(v___x_202_, 9);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_221_ == 0)
{
lean_object* v_unused_222_; 
v_unused_222_ = lean_ctor_get(v___x_202_, 5);
lean_dec(v_unused_222_);
v___x_213_ = v___x_202_;
v_isShared_214_ = v_isSharedCheck_221_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_snapshotTasks_211_);
lean_inc(v_infoState_210_);
lean_inc(v_messages_209_);
lean_inc(v_recordedDeps_208_);
lean_inc(v_traceState_207_);
lean_inc(v_auxDeclNGen_206_);
lean_inc(v_ngen_205_);
lean_inc(v_nextMacroScope_204_);
lean_inc(v_env_203_);
lean_dec(v___x_202_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_221_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_218_; 
v___x_215_ = l_Lean_Kernel_enableDiag(v_env_203_, v___y_201_);
v___x_216_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__2, &l_Lean_Elab_Eqns_tryURefl___closed__2_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__2);
if (v_isShared_214_ == 0)
{
lean_ctor_set(v___x_213_, 5, v___x_216_);
lean_ctor_set(v___x_213_, 0, v___x_215_);
v___x_218_ = v___x_213_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v___x_215_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_nextMacroScope_204_);
lean_ctor_set(v_reuseFailAlloc_220_, 2, v_ngen_205_);
lean_ctor_set(v_reuseFailAlloc_220_, 3, v_auxDeclNGen_206_);
lean_ctor_set(v_reuseFailAlloc_220_, 4, v_traceState_207_);
lean_ctor_set(v_reuseFailAlloc_220_, 5, v___x_216_);
lean_ctor_set(v_reuseFailAlloc_220_, 6, v_recordedDeps_208_);
lean_ctor_set(v_reuseFailAlloc_220_, 7, v_messages_209_);
lean_ctor_set(v_reuseFailAlloc_220_, 8, v_infoState_210_);
lean_ctor_set(v_reuseFailAlloc_220_, 9, v_snapshotTasks_211_);
v___x_218_ = v_reuseFailAlloc_220_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_object* v___x_219_; 
v___x_219_ = lean_st_ref_put(v_a_138_, v___x_218_);
lean_inc_ref(v_inheritedTraceOptions_161_);
lean_inc(v_cancelTk_x3f_160_);
lean_inc(v_currMacroScope_159_);
lean_inc(v_quotContext_158_);
lean_inc(v_maxHeartbeats_157_);
lean_inc(v_initHeartbeats_156_);
lean_inc(v_openDecls_155_);
lean_inc(v_currNamespace_154_);
lean_inc_ref(v_fileMap_152_);
lean_inc_ref(v_fileName_151_);
v___y_164_ = v___y_199_;
v___y_165_ = v___y_200_;
v_fileName_166_ = v_fileName_151_;
v_fileMap_167_ = v_fileMap_152_;
v_currNamespace_168_ = v_currNamespace_154_;
v_openDecls_169_ = v_openDecls_155_;
v_initHeartbeats_170_ = v_initHeartbeats_156_;
v_maxHeartbeats_171_ = v_maxHeartbeats_157_;
v_quotContext_172_ = v_quotContext_158_;
v_currMacroScope_173_ = v_currMacroScope_159_;
v_cancelTk_x3f_174_ = v_cancelTk_x3f_160_;
v_inheritedTraceOptions_175_ = v_inheritedTraceOptions_161_;
v_currRecDepth_176_ = v_currRecDepth_147_;
v_ref_177_ = v_ref_148_;
v_suppressElabErrors_178_ = v_suppressElabErrors_149_;
v_isRecordingDeps_179_ = v_isRecordingDeps_150_;
v___y_180_ = v_a_138_;
goto v___jp_163_;
}
}
}
v___jp_223_:
{
uint16_t v___x_225_; lean_object* v___x_226_; lean_object* v_env_227_; uint8_t v___x_228_; uint16_t v___x_229_; uint16_t v___x_230_; uint16_t v___x_231_; uint8_t v___x_232_; 
v___x_225_ = l_Lean_OptionFlags_ofOptions(v___y_224_);
v___x_226_ = lean_st_ref_get(v_a_138_);
v_env_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc_ref(v_env_227_);
lean_dec(v___x_226_);
v___x_228_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_227_);
lean_dec_ref(v_env_227_);
v___x_229_ = 512;
v___x_230_ = lean_uint16_land(v___x_225_, v___x_229_);
v___x_231_ = 0;
v___x_232_ = lean_uint16_dec_eq(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
if (v___x_228_ == 0)
{
v___y_199_ = v___y_224_;
v___y_200_ = v___x_225_;
v___y_201_ = v___x_162_;
goto v___jp_198_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_161_);
lean_inc(v_cancelTk_x3f_160_);
lean_inc(v_currMacroScope_159_);
lean_inc(v_quotContext_158_);
lean_inc(v_maxHeartbeats_157_);
lean_inc(v_initHeartbeats_156_);
lean_inc(v_openDecls_155_);
lean_inc(v_currNamespace_154_);
lean_inc_ref(v_fileMap_152_);
lean_inc_ref(v_fileName_151_);
v___y_164_ = v___y_224_;
v___y_165_ = v___x_225_;
v_fileName_166_ = v_fileName_151_;
v_fileMap_167_ = v_fileMap_152_;
v_currNamespace_168_ = v_currNamespace_154_;
v_openDecls_169_ = v_openDecls_155_;
v_initHeartbeats_170_ = v_initHeartbeats_156_;
v_maxHeartbeats_171_ = v_maxHeartbeats_157_;
v_quotContext_172_ = v_quotContext_158_;
v_currMacroScope_173_ = v_currMacroScope_159_;
v_cancelTk_x3f_174_ = v_cancelTk_x3f_160_;
v_inheritedTraceOptions_175_ = v_inheritedTraceOptions_161_;
v_currRecDepth_176_ = v_currRecDepth_147_;
v_ref_177_ = v_ref_148_;
v_suppressElabErrors_178_ = v_suppressElabErrors_149_;
v_isRecordingDeps_179_ = v_isRecordingDeps_150_;
v___y_180_ = v_a_138_;
goto v___jp_163_;
}
}
else
{
if (v___x_228_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_161_);
lean_inc(v_cancelTk_x3f_160_);
lean_inc(v_currMacroScope_159_);
lean_inc(v_quotContext_158_);
lean_inc(v_maxHeartbeats_157_);
lean_inc(v_initHeartbeats_156_);
lean_inc(v_openDecls_155_);
lean_inc(v_currNamespace_154_);
lean_inc_ref(v_fileMap_152_);
lean_inc_ref(v_fileName_151_);
v___y_164_ = v___y_224_;
v___y_165_ = v___x_225_;
v_fileName_166_ = v_fileName_151_;
v_fileMap_167_ = v_fileMap_152_;
v_currNamespace_168_ = v_currNamespace_154_;
v_openDecls_169_ = v_openDecls_155_;
v_initHeartbeats_170_ = v_initHeartbeats_156_;
v_maxHeartbeats_171_ = v_maxHeartbeats_157_;
v_quotContext_172_ = v_quotContext_158_;
v_currMacroScope_173_ = v_currMacroScope_159_;
v_cancelTk_x3f_174_ = v_cancelTk_x3f_160_;
v_inheritedTraceOptions_175_ = v_inheritedTraceOptions_161_;
v_currRecDepth_176_ = v_currRecDepth_147_;
v_ref_177_ = v_ref_148_;
v_suppressElabErrors_178_ = v_suppressElabErrors_149_;
v_isRecordingDeps_179_ = v_isRecordingDeps_150_;
v___y_180_ = v_a_138_;
goto v___jp_163_;
}
else
{
uint8_t v___x_233_; 
v___x_233_ = 0;
v___y_199_ = v___y_224_;
v___y_200_ = v___x_225_;
v___y_201_ = v___x_233_;
goto v___jp_198_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Eqns_tryURefl_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_134_ = stack[0].m_obj;
lean_object* v_a_135_ = stack[1].m_obj;
lean_object* v_a_136_ = stack[2].m_obj;
lean_object* v_a_137_ = stack[3].m_obj;
lean_object* v_a_138_ = stack[4].m_obj;
lean_object* v_res_237_;
v_res_237_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_);
stack->m_obj
 = v_res_237_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object* v_mvarId_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
return v_res_244_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(lean_object* v_mvarId_245_, lean_object* v_x_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_252_; 
v___x_252_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_245_, v_x_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
v_a_253_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_252_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_252_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
v_a_261_ = lean_ctor_get(v___x_252_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_252_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_252_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_252_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_245_ = stack[0].m_obj;
lean_object* v_x_246_ = stack[1].m_obj;
lean_object* v___y_247_ = stack[2].m_obj;
lean_object* v___y_248_ = stack[3].m_obj;
lean_object* v___y_249_ = stack[4].m_obj;
lean_object* v___y_250_ = stack[5].m_obj;
lean_object* v_res_269_;
v_res_269_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_245_, v_x_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
stack->m_obj
 = v_res_269_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg___boxed(lean_object* v_mvarId_270_, lean_object* v_x_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_270_, v_x_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_277_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(lean_object* v_00_u03b1_278_, lean_object* v_mvarId_279_, lean_object* v_x_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_279_, v_x_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
return v___x_286_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_279_ = stack[1].m_obj;
lean_object* v_x_280_ = stack[2].m_obj;
lean_object* v___y_281_ = stack[3].m_obj;
lean_object* v___y_282_ = stack[4].m_obj;
lean_object* v___y_283_ = stack[5].m_obj;
lean_object* v___y_284_ = stack[6].m_obj;
lean_object* v_res_287_;
v_res_287_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(lean_box(0), v_mvarId_279_, v_x_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___boxed(lean_object* v_00_u03b1_288_, lean_object* v_mvarId_289_, lean_object* v_x_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(v_00_u03b1_288_, v_mvarId_289_, v_x_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
return v_res_296_;
}
}
uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t v___x_297_, lean_object* v_x_298_){
_start:
{
return v___x_297_;
}
}
LEAN_EXPORT void l_Lean_Elab_Eqns_deltaLHS___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_297_ = stack[0].m_num;
lean_object* v_x_298_ = stack[1].m_obj;
uint8_t v_res_299_;
v_res_299_ = l_Lean_Elab_Eqns_deltaLHS___lam__0(v___x_297_, v_x_298_);
stack->m_num = v_res_299_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object* v___x_300_, lean_object* v_x_301_){
_start:
{
uint8_t v___x_1031__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v___x_1031__boxed_302_ = lean_unbox(v___x_300_);
v_res_303_ = l_Lean_Elab_Eqns_deltaLHS___lam__0(v___x_1031__boxed_302_, v_x_301_);
lean_dec(v_x_301_);
v_r_304_ = lean_box(v_res_303_);
return v_r_304_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5));
v___x_315_ = l_Lean_MessageData_ofFormat(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9));
v___x_322_ = l_Lean_MessageData_ofFormat(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10);
v___x_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object* v_mvarId_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v___x_331_; 
lean_inc(v_mvarId_325_);
v___x_331_ = l_Lean_MVarId_getType_x27(v_mvarId_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
v___x_333_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_334_ = lean_unsigned_to_nat(3u);
v___x_335_ = l_Lean_Expr_isAppOfArity(v_a_332_, v___x_333_, v___x_334_);
if (v___x_335_ == 0)
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
lean_dec(v_a_332_);
v___x_336_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_337_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7);
v___x_338_ = l_Lean_Meta_throwTacticEx___redArg(v___x_336_, v_mvarId_325_, v___x_337_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___f_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; 
v___x_339_ = lean_box(v___x_335_);
v___f_340_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_340_, 0, v___x_339_);
v___x_341_ = l_Lean_Expr_appFn_x21(v_a_332_);
v___x_342_ = l_Lean_Expr_appArg_x21(v___x_341_);
lean_dec_ref(v___x_341_);
v___x_343_ = l_Lean_Expr_appArg_x21(v_a_332_);
lean_dec(v_a_332_);
v___x_344_ = 0;
v___x_345_ = l_Lean_Meta_delta_x3f(v___x_342_, v___f_340_, v___x_344_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
if (lean_obj_tag(v_a_346_) == 1)
{
lean_object* v_val_347_; lean_object* v___x_348_; 
v_val_347_ = lean_ctor_get(v_a_346_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v_a_346_, 1);
v___x_348_ = l_Lean_Meta_mkEq(v_val_347_, v___x_343_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_348_) == 0)
{
lean_object* v_a_349_; lean_object* v___x_350_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
lean_inc(v_a_349_);
lean_dec_ref_known(v___x_348_, 1);
v___x_350_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_325_, v_a_349_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_350_;
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
lean_dec(v_mvarId_325_);
v_a_351_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_348_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_348_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v_a_346_);
lean_dec_ref(v___x_343_);
v___x_359_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_360_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11);
v___x_361_ = l_Lean_Meta_throwTacticEx___redArg(v___x_359_, v_mvarId_325_, v___x_360_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
return v___x_361_;
}
}
else
{
lean_object* v_a_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_369_; 
lean_dec_ref(v___x_343_);
lean_dec(v_mvarId_325_);
v_a_362_ = lean_ctor_get(v___x_345_, 0);
v_isSharedCheck_369_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_369_ == 0)
{
v___x_364_ = v___x_345_;
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_a_362_);
lean_dec(v___x_345_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_369_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_367_; 
if (v_isShared_365_ == 0)
{
v___x_367_ = v___x_364_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
return v___x_367_;
}
}
}
}
}
else
{
lean_object* v_a_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_377_; 
lean_dec(v_mvarId_325_);
v_a_370_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_377_ == 0)
{
v___x_372_ = v___x_331_;
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_a_370_);
lean_dec(v___x_331_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_377_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_375_; 
if (v_isShared_373_ == 0)
{
v___x_375_ = v___x_372_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_370_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Eqns_deltaLHS___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_325_ = stack[0].m_obj;
lean_object* v___y_326_ = stack[1].m_obj;
lean_object* v___y_327_ = stack[2].m_obj;
lean_object* v___y_328_ = stack[3].m_obj;
lean_object* v___y_329_ = stack[4].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Lean_Elab_Eqns_deltaLHS___lam__1(v_mvarId_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(lean_object* v_mvarId_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_Elab_Eqns_deltaLHS___lam__1(v_mvarId_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
lean_dec(v___y_383_);
lean_dec_ref(v___y_382_);
lean_dec(v___y_381_);
lean_dec_ref(v___y_380_);
return v_res_385_;
}
}
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object* v_mvarId_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___f_392_; lean_object* v___x_393_; 
lean_inc(v_mvarId_386_);
v___f_392_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed), 6, 1);
lean_closure_set(v___f_392_, 0, v_mvarId_386_);
v___x_393_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_386_, v___f_392_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
return v___x_393_;
}
}
LEAN_EXPORT void l_Lean_Elab_Eqns_deltaLHS_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_386_ = stack[0].m_obj;
lean_object* v_a_387_ = stack[1].m_obj;
lean_object* v_a_388_ = stack[2].m_obj;
lean_object* v_a_389_ = stack[3].m_obj;
lean_object* v_a_390_ = stack[4].m_obj;
lean_object* v_res_394_;
v_res_394_ = l_Lean_Elab_Eqns_deltaLHS(v_mvarId_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object* v_mvarId_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Elab_Eqns_deltaLHS(v_mvarId_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec_ref(v_a_398_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
return v_res_401_;
}
}
lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object* v_mvarId_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
v___x_411_ = ((lean_object*)(l_Lean_Elab_Eqns_tryContradiction___closed__0));
v___x_412_ = l_Lean_MVarId_contradictionCore(v_mvarId_405_, v___x_411_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
return v___x_412_;
}
}
LEAN_EXPORT void l_Lean_Elab_Eqns_tryContradiction_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_405_ = stack[0].m_obj;
lean_object* v_a_406_ = stack[1].m_obj;
lean_object* v_a_407_ = stack[2].m_obj;
lean_object* v_a_408_ = stack[3].m_obj;
lean_object* v_a_409_ = stack[4].m_obj;
lean_object* v_res_413_;
v_res_413_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
stack->m_obj
 = v_res_413_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object* v_mvarId_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(lean_object* v_msg_421_){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = l_Lean_instInhabitedExpr;
v___x_423_ = lean_panic_fn_borrowed(v___x_422_, v_msg_421_);
return v___x_423_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0(void){
_start:
{
lean_object* v___x_424_; lean_object* v_dummy_425_; 
v___x_424_ = lean_box(0);
v_dummy_425_ = l_Lean_Expr_sort___override(v___x_424_);
return v_dummy_425_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_429_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3));
v___x_430_ = lean_unsigned_to_nat(18u);
v___x_431_ = lean_unsigned_to_nat(1913u);
v___x_432_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2));
v___x_433_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1));
v___x_434_ = l_mkPanicMessageWithDecl(v___x_433_, v___x_432_, v___x_431_, v___x_430_, v___x_429_);
return v___x_434_;
}
}
lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(lean_object* v_e_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_Lean_Meta_whnfR(v_e_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
if (lean_obj_tag(v___x_441_) == 0)
{
lean_object* v_a_442_; lean_object* v___x_443_; 
v_a_442_ = lean_ctor_get(v___x_441_, 0);
v___x_443_ = l_Lean_Expr_getAppFn(v_a_442_);
if (lean_obj_tag(v___x_443_) == 11)
{
lean_object* v_struct_444_; lean_object* v___x_445_; 
lean_inc(v_a_442_);
lean_dec_ref_known(v___x_441_, 1);
v_struct_444_ = lean_ctor_get(v___x_443_, 2);
lean_inc_ref(v_struct_444_);
v___x_445_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_struct_444_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_471_; 
v_a_446_ = lean_ctor_get(v___x_445_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_471_ == 0)
{
v___x_448_ = v___x_445_;
v_isShared_449_ = v_isSharedCheck_471_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_445_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_471_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___y_451_; 
if (lean_obj_tag(v___x_443_) == 11)
{
lean_object* v_typeName_462_; lean_object* v_idx_463_; lean_object* v_struct_464_; size_t v___x_465_; size_t v___x_466_; uint8_t v___x_467_; 
v_typeName_462_ = lean_ctor_get(v___x_443_, 0);
v_idx_463_ = lean_ctor_get(v___x_443_, 1);
v_struct_464_ = lean_ctor_get(v___x_443_, 2);
v___x_465_ = lean_ptr_addr(v_struct_464_);
v___x_466_ = lean_ptr_addr(v_a_446_);
v___x_467_ = lean_usize_dec_eq(v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; 
lean_inc(v_idx_463_);
lean_inc(v_typeName_462_);
lean_dec_ref_known(v___x_443_, 3);
v___x_468_ = l_Lean_Expr_proj___override(v_typeName_462_, v_idx_463_, v_a_446_);
v___y_451_ = v___x_468_;
goto v___jp_450_;
}
else
{
lean_dec(v_a_446_);
v___y_451_ = v___x_443_;
goto v___jp_450_;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec(v_a_446_);
lean_dec_ref_known(v___x_443_, 3);
v___x_469_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4);
v___x_470_ = l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(v___x_469_);
v___y_451_ = v___x_470_;
goto v___jp_450_;
}
v___jp_450_:
{
lean_object* v_dummy_452_; lean_object* v_nargs_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v_dummy_452_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0);
v_nargs_453_ = l_Lean_Expr_getAppNumArgs(v_a_442_);
lean_inc(v_nargs_453_);
v___x_454_ = lean_mk_array(v_nargs_453_, v_dummy_452_);
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_sub(v_nargs_453_, v___x_455_);
lean_dec(v_nargs_453_);
v___x_457_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_442_, v___x_454_, v___x_456_);
v___x_458_ = l_Lean_mkAppN(v___y_451_, v___x_457_);
lean_dec_ref(v___x_457_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_458_);
v___x_460_ = v___x_448_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_443_, 3);
lean_dec(v_a_442_);
return v___x_445_;
}
}
else
{
lean_dec_ref(v___x_443_);
return v___x_441_;
}
}
else
{
return v___x_441_;
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_435_ = stack[0].m_obj;
lean_object* v_a_436_ = stack[1].m_obj;
lean_object* v_a_437_ = stack[2].m_obj;
lean_object* v_a_438_ = stack[3].m_obj;
lean_object* v_a_439_ = stack[4].m_obj;
lean_object* v_res_472_;
v_res_472_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_e_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object* v_e_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_e_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
lean_dec(v_a_475_);
lean_dec_ref(v_a_474_);
return v_res_479_;
}
}
lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object* v_mvarId_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
lean_object* v___x_486_; 
lean_inc(v_mvarId_480_);
v___x_486_ = l_Lean_MVarId_getType_x27(v_mvarId_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_548_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_548_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_548_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_548_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_492_ = lean_unsigned_to_nat(3u);
v___x_493_ = l_Lean_Expr_isAppOfArity(v_a_487_, v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_494_; lean_object* v___x_496_; 
lean_dec(v_a_487_);
lean_dec(v_mvarId_480_);
v___x_494_ = lean_box(0);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_494_);
v___x_496_ = v___x_489_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v___x_494_);
v___x_496_ = v_reuseFailAlloc_497_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
return v___x_496_;
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_del_object(v___x_489_);
v___x_498_ = l_Lean_Expr_appFn_x21(v_a_487_);
v___x_499_ = l_Lean_Expr_appArg_x21(v___x_498_);
lean_dec_ref(v___x_498_);
v___x_500_ = l_Lean_Expr_appArg_x21(v_a_487_);
lean_dec(v_a_487_);
lean_inc_ref(v___x_499_);
v___x_501_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v___x_499_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_539_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_539_ == 0)
{
v___x_504_ = v___x_501_;
v_isShared_505_ = v_isSharedCheck_539_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_539_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
uint8_t v___x_506_; 
v___x_506_ = lean_expr_eqv(v_a_502_, v___x_499_);
lean_dec_ref(v___x_499_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_del_object(v___x_504_);
v___x_507_ = l_Lean_Meta_mkEq(v_a_502_, v___x_500_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; lean_object* v___x_509_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
v___x_509_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_480_, v_a_508_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
if (lean_obj_tag(v___x_509_) == 0)
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_518_; 
v_a_510_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_518_ == 0)
{
v___x_512_ = v___x_509_;
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_509_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_518_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v_a_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
v_a_519_ = lean_ctor_get(v___x_509_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_509_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_509_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_509_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_524_; 
if (v_isShared_522_ == 0)
{
v___x_524_ = v___x_521_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v_a_519_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_mvarId_480_);
v_a_527_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_507_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_507_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_537_; 
lean_dec(v_a_502_);
lean_dec_ref(v___x_500_);
lean_dec(v_mvarId_480_);
v___x_535_ = lean_box(0);
if (v_isShared_505_ == 0)
{
lean_ctor_set(v___x_504_, 0, v___x_535_);
v___x_537_ = v___x_504_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v___x_500_);
lean_dec_ref(v___x_499_);
lean_dec(v_mvarId_480_);
v_a_540_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_501_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_501_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
return v___x_545_;
}
}
}
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec(v_mvarId_480_);
v_a_549_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_486_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_486_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_480_ = stack[0].m_obj;
lean_object* v___y_481_ = stack[1].m_obj;
lean_object* v___y_482_ = stack[2].m_obj;
lean_object* v___y_483_ = stack[3].m_obj;
lean_object* v___y_484_ = stack[4].m_obj;
lean_object* v_res_557_;
v_res_557_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(v_mvarId_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
stack->m_obj
 = v_res_557_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(lean_object* v_mvarId_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(v_mvarId_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
return v_res_564_;
}
}
lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object* v_mvarId_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___f_571_; lean_object* v___x_572_; 
lean_inc(v_mvarId_565_);
v___f_571_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_571_, 0, v_mvarId_565_);
v___x_572_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_565_, v___f_571_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
return v___x_572_;
}
}
LEAN_EXPORT void l_Lean_Elab_Eqns_whnfReducibleLHS_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_565_ = stack[0].m_obj;
lean_object* v_a_566_ = stack[1].m_obj;
lean_object* v_a_567_ = stack[2].m_obj;
lean_object* v_a_568_ = stack[3].m_obj;
lean_object* v_a_569_ = stack[4].m_obj;
lean_object* v_res_573_;
v_res_573_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_);
stack->m_obj
 = v_res_573_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object* v_mvarId_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_);
lean_dec(v_a_578_);
lean_dec_ref(v_a_577_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
return v_res_580_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Delta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_SplitIf(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_PreDefinition_EqnsUtils(builtin);
}
#ifdef __cplusplus
}
#endif
