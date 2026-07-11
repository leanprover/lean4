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
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_replaceTargetDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpIfTarget(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Split_simpMatchTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Meta_smartUnfolding;
extern lean_object* l_Lean_diagnostics;
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__0 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__1 = (const lean_object*)&l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object* v_mvarId_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v___x_7_; 
lean_inc(v_mvarId_1_);
v___x_7_ = l_Lean_Meta_Split_simpMatchTarget(v_mvarId_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_7_) == 0)
{
lean_object* v_a_8_; lean_object* v___x_10_; uint8_t v_isShared_11_; uint8_t v_isSharedCheck_22_; 
v_a_8_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_22_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_22_ == 0)
{
v___x_10_ = v___x_7_;
v_isShared_11_ = v_isSharedCheck_22_;
goto v_resetjp_9_;
}
else
{
lean_inc(v_a_8_);
lean_dec(v___x_7_);
v___x_10_ = lean_box(0);
v_isShared_11_ = v_isSharedCheck_22_;
goto v_resetjp_9_;
}
v_resetjp_9_:
{
uint8_t v___x_12_; uint8_t v___x_13_; 
v___x_12_ = l_Lean_instBEqMVarId_beq(v_mvarId_1_, v_a_8_);
lean_dec(v_mvarId_1_);
v___x_13_ = lean_bool_not(v___x_12_);
if (v___x_13_ == 0)
{
lean_object* v___x_14_; lean_object* v___x_16_; 
lean_dec(v_a_8_);
v___x_14_ = lean_box(0);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_14_);
v___x_16_ = v___x_10_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
else
{
lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_18_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_18_, 0, v_a_8_);
if (v_isShared_11_ == 0)
{
lean_ctor_set(v___x_10_, 0, v___x_18_);
v___x_20_ = v___x_10_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_30_; 
lean_dec(v_mvarId_1_);
v_a_23_ = lean_ctor_get(v___x_7_, 0);
v_isSharedCheck_30_ = !lean_is_exclusive(v___x_7_);
if (v_isSharedCheck_30_ == 0)
{
v___x_25_ = v___x_7_;
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_7_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_30_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_29_; 
v_reuseFailAlloc_29_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_29_, 0, v_a_23_);
v___x_28_ = v_reuseFailAlloc_29_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
return v___x_28_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object* v_mvarId_38_, uint8_t v_useNewSemantics_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
uint8_t v___x_45_; lean_object* v___x_46_; 
v___x_45_ = 1;
lean_inc(v_mvarId_38_);
v___x_46_ = l_Lean_Meta_simpIfTarget(v_mvarId_38_, v___x_45_, v_useNewSemantics_39_, v_a_40_, v_a_41_, v_a_42_, v_a_43_);
if (lean_obj_tag(v___x_46_) == 0)
{
lean_object* v_a_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_61_; 
v_a_47_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_61_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_61_ == 0)
{
v___x_49_ = v___x_46_;
v_isShared_50_ = v_isSharedCheck_61_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_a_47_);
lean_dec(v___x_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_61_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
uint8_t v___x_51_; uint8_t v___x_52_; 
v___x_51_ = l_Lean_instBEqMVarId_beq(v_mvarId_38_, v_a_47_);
lean_dec(v_mvarId_38_);
v___x_52_ = lean_bool_not(v___x_51_);
if (v___x_52_ == 0)
{
lean_object* v___x_53_; lean_object* v___x_55_; 
lean_dec(v_a_47_);
v___x_53_ = lean_box(0);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_53_);
v___x_55_ = v___x_49_;
goto v_reusejp_54_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v___x_53_);
v___x_55_ = v_reuseFailAlloc_56_;
goto v_reusejp_54_;
}
v_reusejp_54_:
{
return v___x_55_;
}
}
else
{
lean_object* v___x_57_; lean_object* v___x_59_; 
v___x_57_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_57_, 0, v_a_47_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_57_);
v___x_59_ = v___x_49_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
else
{
lean_object* v_a_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_69_; 
lean_dec(v_mvarId_38_);
v_a_62_ = lean_ctor_get(v___x_46_, 0);
v_isSharedCheck_69_ = !lean_is_exclusive(v___x_46_);
if (v_isSharedCheck_69_ == 0)
{
v___x_64_ = v___x_46_;
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_a_62_);
lean_dec(v___x_46_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_69_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v___x_67_; 
if (v_isShared_65_ == 0)
{
v___x_67_ = v___x_64_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_62_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(lean_object* v_opts_79_, lean_object* v_opt_80_){
_start:
{
lean_object* v_name_81_; lean_object* v_defValue_82_; lean_object* v_map_83_; lean_object* v___x_84_; 
v_name_81_ = lean_ctor_get(v_opt_80_, 0);
v_defValue_82_ = lean_ctor_get(v_opt_80_, 1);
v_map_83_ = lean_ctor_get(v_opts_79_, 0);
v___x_84_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_83_, v_name_81_);
if (lean_obj_tag(v___x_84_) == 0)
{
uint8_t v___x_85_; 
v___x_85_ = lean_unbox(v_defValue_82_);
return v___x_85_;
}
else
{
lean_object* v_val_86_; 
v_val_86_ = lean_ctor_get(v___x_84_, 0);
lean_inc(v_val_86_);
lean_dec_ref_known(v___x_84_, 1);
if (lean_obj_tag(v_val_86_) == 1)
{
uint8_t v_v_87_; 
v_v_87_ = lean_ctor_get_uint8(v_val_86_, 0);
lean_dec_ref_known(v_val_86_, 0);
return v_v_87_;
}
else
{
uint8_t v___x_88_; 
lean_dec(v_val_86_);
v___x_88_ = lean_unbox(v_defValue_82_);
return v___x_88_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1___boxed(lean_object* v_opts_89_, lean_object* v_opt_90_){
_start:
{
uint8_t v_res_91_; lean_object* v_r_92_; 
v_res_91_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_opts_89_, v_opt_90_);
lean_dec_ref(v_opt_90_);
lean_dec_ref(v_opts_89_);
v_r_92_ = lean_box(v_res_91_);
return v_r_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(lean_object* v_opts_93_, lean_object* v_opt_94_){
_start:
{
lean_object* v_name_95_; lean_object* v_defValue_96_; lean_object* v_map_97_; lean_object* v___x_98_; 
v_name_95_ = lean_ctor_get(v_opt_94_, 0);
v_defValue_96_ = lean_ctor_get(v_opt_94_, 1);
v_map_97_ = lean_ctor_get(v_opts_93_, 0);
v___x_98_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_97_, v_name_95_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_inc(v_defValue_96_);
return v_defValue_96_;
}
else
{
lean_object* v_val_99_; 
v_val_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_val_99_);
lean_dec_ref_known(v___x_98_, 1);
if (lean_obj_tag(v_val_99_) == 3)
{
lean_object* v_v_100_; 
v_v_100_ = lean_ctor_get(v_val_99_, 0);
lean_inc(v_v_100_);
lean_dec_ref_known(v_val_99_, 1);
return v_v_100_;
}
else
{
lean_dec(v_val_99_);
lean_inc(v_defValue_96_);
return v_defValue_96_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2___boxed(lean_object* v_opts_101_, lean_object* v_opt_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(v_opts_101_, v_opt_102_);
lean_dec_ref(v_opt_102_);
lean_dec_ref(v_opts_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(lean_object* v_o_107_, lean_object* v_k_108_, uint8_t v_v_109_){
_start:
{
lean_object* v_map_110_; uint8_t v_hasTrace_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_125_; 
v_map_110_ = lean_ctor_get(v_o_107_, 0);
v_hasTrace_111_ = lean_ctor_get_uint8(v_o_107_, sizeof(void*)*1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_o_107_);
if (v_isSharedCheck_125_ == 0)
{
v___x_113_ = v_o_107_;
v_isShared_114_ = v_isSharedCheck_125_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_map_110_);
lean_dec(v_o_107_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_125_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_115_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_115_, 0, v_v_109_);
lean_inc(v_k_108_);
v___x_116_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_108_, v___x_115_, v_map_110_);
if (v_hasTrace_111_ == 0)
{
lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_120_; 
v___x_117_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__1));
v___x_118_ = l_Lean_Name_isPrefixOf(v___x_117_, v_k_108_);
lean_dec(v_k_108_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_116_);
v___x_120_ = v___x_113_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_116_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
lean_ctor_set_uint8(v___x_120_, sizeof(void*)*1, v___x_118_);
return v___x_120_;
}
}
else
{
lean_object* v___x_123_; 
lean_dec(v_k_108_);
if (v_isShared_114_ == 0)
{
lean_ctor_set(v___x_113_, 0, v___x_116_);
v___x_123_ = v___x_113_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_116_);
lean_ctor_set_uint8(v_reuseFailAlloc_124_, sizeof(void*)*1, v_hasTrace_111_);
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
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___boxed(lean_object* v_o_126_, lean_object* v_k_127_, lean_object* v_v_128_){
_start:
{
uint8_t v_v_boxed_129_; lean_object* v_res_130_; 
v_v_boxed_129_ = lean_unbox(v_v_128_);
v_res_130_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(v_o_126_, v_k_127_, v_v_boxed_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(lean_object* v_opts_131_, lean_object* v_opt_132_, uint8_t v_val_133_){
_start:
{
lean_object* v_name_134_; lean_object* v___x_135_; 
v_name_134_ = lean_ctor_get(v_opt_132_, 0);
lean_inc(v_name_134_);
lean_dec_ref(v_opt_132_);
v___x_135_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(v_opts_131_, v_name_134_, v_val_133_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0___boxed(lean_object* v_opts_136_, lean_object* v_opt_137_, lean_object* v_val_138_){
_start:
{
uint8_t v_val_boxed_139_; lean_object* v_res_140_; 
v_val_boxed_139_ = lean_unbox(v_val_138_);
v_res_140_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(v_opts_136_, v_opt_137_, v_val_boxed_139_);
return v_res_140_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__0(void){
_start:
{
lean_object* v___x_141_; 
v___x_141_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__1(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__0, &l_Lean_Elab_Eqns_tryURefl___closed__0_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__0);
v___x_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__2(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__1, &l_Lean_Elab_Eqns_tryURefl___closed__1_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__1);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object* v_mvarId_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___y_153_; uint8_t v___y_154_; lean_object* v___x_158_; lean_object* v_fileName_159_; lean_object* v_fileMap_160_; lean_object* v_options_161_; lean_object* v_currRecDepth_162_; lean_object* v_ref_163_; lean_object* v_currNamespace_164_; lean_object* v_openDecls_165_; lean_object* v_initHeartbeats_166_; lean_object* v_maxHeartbeats_167_; lean_object* v_quotContext_168_; lean_object* v_currMacroScope_169_; lean_object* v_cancelTk_x3f_170_; uint8_t v_suppressElabErrors_171_; lean_object* v_inheritedTraceOptions_172_; lean_object* v_env_173_; uint8_t v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; uint8_t v___x_179_; lean_object* v_fileName_181_; lean_object* v_fileMap_182_; lean_object* v_currRecDepth_183_; lean_object* v_ref_184_; lean_object* v_currNamespace_185_; lean_object* v_openDecls_186_; lean_object* v_initHeartbeats_187_; lean_object* v_maxHeartbeats_188_; lean_object* v_quotContext_189_; lean_object* v_currMacroScope_190_; lean_object* v_cancelTk_x3f_191_; uint8_t v_suppressElabErrors_192_; lean_object* v_inheritedTraceOptions_193_; lean_object* v___y_194_; uint8_t v___y_212_; uint8_t v___x_234_; 
v___x_158_ = lean_st_ref_get(v_a_150_);
v_fileName_159_ = lean_ctor_get(v_a_149_, 0);
v_fileMap_160_ = lean_ctor_get(v_a_149_, 1);
v_options_161_ = lean_ctor_get(v_a_149_, 2);
v_currRecDepth_162_ = lean_ctor_get(v_a_149_, 3);
v_ref_163_ = lean_ctor_get(v_a_149_, 5);
v_currNamespace_164_ = lean_ctor_get(v_a_149_, 6);
v_openDecls_165_ = lean_ctor_get(v_a_149_, 7);
v_initHeartbeats_166_ = lean_ctor_get(v_a_149_, 8);
v_maxHeartbeats_167_ = lean_ctor_get(v_a_149_, 9);
v_quotContext_168_ = lean_ctor_get(v_a_149_, 10);
v_currMacroScope_169_ = lean_ctor_get(v_a_149_, 11);
v_cancelTk_x3f_170_ = lean_ctor_get(v_a_149_, 12);
v_suppressElabErrors_171_ = lean_ctor_get_uint8(v_a_149_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_172_ = lean_ctor_get(v_a_149_, 13);
v_env_173_ = lean_ctor_get(v___x_158_, 0);
lean_inc_ref(v_env_173_);
lean_dec(v___x_158_);
v___x_174_ = 1;
v___x_175_ = l_Lean_Meta_smartUnfolding;
v___x_176_ = 0;
lean_inc_ref(v_options_161_);
v___x_177_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(v_options_161_, v___x_175_, v___x_176_);
v___x_178_ = l_Lean_diagnostics;
v___x_179_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(v___x_177_, v___x_178_);
v___x_234_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_173_);
lean_dec_ref(v_env_173_);
if (v___x_234_ == 0)
{
if (v___x_179_ == 0)
{
v___y_212_ = v___x_174_;
goto v___jp_211_;
}
else
{
v___y_212_ = v___x_234_;
goto v___jp_211_;
}
}
else
{
v___y_212_ = v___x_179_;
goto v___jp_211_;
}
v___jp_152_:
{
if (v___y_154_ == 0)
{
lean_object* v___x_155_; lean_object* v___x_156_; 
lean_dec_ref(v___y_153_);
v___x_155_ = lean_box(v___y_154_);
v___x_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___y_153_);
return v___x_157_;
}
}
v___jp_180_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_195_ = l_Lean_maxRecDepth;
v___x_196_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(v___x_177_, v___x_195_);
lean_inc_ref(v_inheritedTraceOptions_193_);
lean_inc(v_cancelTk_x3f_191_);
lean_inc(v_currMacroScope_190_);
lean_inc(v_quotContext_189_);
lean_inc(v_maxHeartbeats_188_);
lean_inc(v_initHeartbeats_187_);
lean_inc(v_openDecls_186_);
lean_inc(v_currNamespace_185_);
lean_inc(v_ref_184_);
lean_inc(v_currRecDepth_183_);
lean_inc_ref(v_fileMap_182_);
lean_inc_ref(v_fileName_181_);
v___x_197_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_197_, 0, v_fileName_181_);
lean_ctor_set(v___x_197_, 1, v_fileMap_182_);
lean_ctor_set(v___x_197_, 2, v___x_177_);
lean_ctor_set(v___x_197_, 3, v_currRecDepth_183_);
lean_ctor_set(v___x_197_, 4, v___x_196_);
lean_ctor_set(v___x_197_, 5, v_ref_184_);
lean_ctor_set(v___x_197_, 6, v_currNamespace_185_);
lean_ctor_set(v___x_197_, 7, v_openDecls_186_);
lean_ctor_set(v___x_197_, 8, v_initHeartbeats_187_);
lean_ctor_set(v___x_197_, 9, v_maxHeartbeats_188_);
lean_ctor_set(v___x_197_, 10, v_quotContext_189_);
lean_ctor_set(v___x_197_, 11, v_currMacroScope_190_);
lean_ctor_set(v___x_197_, 12, v_cancelTk_x3f_191_);
lean_ctor_set(v___x_197_, 13, v_inheritedTraceOptions_193_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*14, v___x_179_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*14 + 1, v_suppressElabErrors_192_);
v___x_198_ = l_Lean_MVarId_refl(v_mvarId_146_, v___x_174_, v_a_147_, v_a_148_, v___x_197_, v___y_194_);
lean_dec_ref_known(v___x_197_, 14);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_206_; 
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_206_ == 0)
{
lean_object* v_unused_207_; 
v_unused_207_ = lean_ctor_get(v___x_198_, 0);
lean_dec(v_unused_207_);
v___x_200_ = v___x_198_;
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
else
{
lean_dec(v___x_198_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_206_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_box(v___x_174_);
if (v_isShared_201_ == 0)
{
lean_ctor_set(v___x_200_, 0, v___x_202_);
v___x_204_ = v___x_200_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
else
{
lean_object* v_a_208_; uint8_t v___x_209_; 
v_a_208_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_198_, 1);
v___x_209_ = l_Lean_Exception_isInterrupt(v_a_208_);
if (v___x_209_ == 0)
{
uint8_t v___x_210_; 
lean_inc(v_a_208_);
v___x_210_ = l_Lean_Exception_isRuntime(v_a_208_);
v___y_153_ = v_a_208_;
v___y_154_ = v___x_210_;
goto v___jp_152_;
}
else
{
v___y_153_ = v_a_208_;
v___y_154_ = v___x_209_;
goto v___jp_152_;
}
}
}
v___jp_211_:
{
uint8_t v___x_213_; 
v___x_213_ = lean_bool_not(v___y_212_);
if (v___x_213_ == 0)
{
v_fileName_181_ = v_fileName_159_;
v_fileMap_182_ = v_fileMap_160_;
v_currRecDepth_183_ = v_currRecDepth_162_;
v_ref_184_ = v_ref_163_;
v_currNamespace_185_ = v_currNamespace_164_;
v_openDecls_186_ = v_openDecls_165_;
v_initHeartbeats_187_ = v_initHeartbeats_166_;
v_maxHeartbeats_188_ = v_maxHeartbeats_167_;
v_quotContext_189_ = v_quotContext_168_;
v_currMacroScope_190_ = v_currMacroScope_169_;
v_cancelTk_x3f_191_ = v_cancelTk_x3f_170_;
v_suppressElabErrors_192_ = v_suppressElabErrors_171_;
v_inheritedTraceOptions_193_ = v_inheritedTraceOptions_172_;
v___y_194_ = v_a_150_;
goto v___jp_180_;
}
else
{
lean_object* v___x_214_; lean_object* v_env_215_; lean_object* v_nextMacroScope_216_; lean_object* v_ngen_217_; lean_object* v_auxDeclNGen_218_; lean_object* v_traceState_219_; lean_object* v_messages_220_; lean_object* v_infoState_221_; lean_object* v_snapshotTasks_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_232_; 
v___x_214_ = lean_st_ref_take(v_a_150_);
v_env_215_ = lean_ctor_get(v___x_214_, 0);
v_nextMacroScope_216_ = lean_ctor_get(v___x_214_, 1);
v_ngen_217_ = lean_ctor_get(v___x_214_, 2);
v_auxDeclNGen_218_ = lean_ctor_get(v___x_214_, 3);
v_traceState_219_ = lean_ctor_get(v___x_214_, 4);
v_messages_220_ = lean_ctor_get(v___x_214_, 6);
v_infoState_221_ = lean_ctor_get(v___x_214_, 7);
v_snapshotTasks_222_ = lean_ctor_get(v___x_214_, 8);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v___x_214_, 5);
lean_dec(v_unused_233_);
v___x_224_ = v___x_214_;
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_snapshotTasks_222_);
lean_inc(v_infoState_221_);
lean_inc(v_messages_220_);
lean_inc(v_traceState_219_);
lean_inc(v_auxDeclNGen_218_);
lean_inc(v_ngen_217_);
lean_inc(v_nextMacroScope_216_);
lean_inc(v_env_215_);
lean_dec(v___x_214_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_232_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_226_ = l_Lean_Kernel_enableDiag(v_env_215_, v___x_179_);
v___x_227_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__2, &l_Lean_Elab_Eqns_tryURefl___closed__2_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__2);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 5, v___x_227_);
lean_ctor_set(v___x_224_, 0, v___x_226_);
v___x_229_ = v___x_224_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_nextMacroScope_216_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_ngen_217_);
lean_ctor_set(v_reuseFailAlloc_231_, 3, v_auxDeclNGen_218_);
lean_ctor_set(v_reuseFailAlloc_231_, 4, v_traceState_219_);
lean_ctor_set(v_reuseFailAlloc_231_, 5, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_231_, 6, v_messages_220_);
lean_ctor_set(v_reuseFailAlloc_231_, 7, v_infoState_221_);
lean_ctor_set(v_reuseFailAlloc_231_, 8, v_snapshotTasks_222_);
v___x_229_ = v_reuseFailAlloc_231_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; 
v___x_230_ = lean_st_ref_set(v_a_150_, v___x_229_);
v_fileName_181_ = v_fileName_159_;
v_fileMap_182_ = v_fileMap_160_;
v_currRecDepth_183_ = v_currRecDepth_162_;
v_ref_184_ = v_ref_163_;
v_currNamespace_185_ = v_currNamespace_164_;
v_openDecls_186_ = v_openDecls_165_;
v_initHeartbeats_187_ = v_initHeartbeats_166_;
v_maxHeartbeats_188_ = v_maxHeartbeats_167_;
v_quotContext_189_ = v_quotContext_168_;
v_currMacroScope_190_ = v_currMacroScope_169_;
v_cancelTk_x3f_191_ = v_cancelTk_x3f_170_;
v_suppressElabErrors_192_ = v_suppressElabErrors_171_;
v_inheritedTraceOptions_193_ = v_inheritedTraceOptions_172_;
v___y_194_ = v_a_150_;
goto v___jp_180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object* v_mvarId_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(lean_object* v_mvarId_242_, lean_object* v_x_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_242_, v_x_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_);
if (lean_obj_tag(v___x_249_) == 0)
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_a_250_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_249_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_249_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
v_a_258_ = lean_ctor_get(v___x_249_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_249_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_249_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_249_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg___boxed(lean_object* v_mvarId_266_, lean_object* v_x_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_266_, v_x_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(lean_object* v_00_u03b1_274_, lean_object* v_mvarId_275_, lean_object* v_x_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_275_, v_x_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___boxed(lean_object* v_00_u03b1_283_, lean_object* v_mvarId_284_, lean_object* v_x_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(v_00_u03b1_283_, v_mvarId_284_, v_x_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
lean_dec(v___y_287_);
lean_dec_ref(v___y_286_);
return v_res_291_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t v___x_292_, lean_object* v_x_293_){
_start:
{
return v___x_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object* v___x_294_, lean_object* v_x_295_){
_start:
{
uint8_t v___x_1020__boxed_296_; uint8_t v_res_297_; lean_object* v_r_298_; 
v___x_1020__boxed_296_ = lean_unbox(v___x_294_);
v_res_297_ = l_Lean_Elab_Eqns_deltaLHS___lam__0(v___x_1020__boxed_296_, v_x_295_);
lean_dec(v_x_295_);
v_r_298_ = lean_box(v_res_297_);
return v_r_298_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5));
v___x_309_ = l_Lean_MessageData_ofFormat(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9));
v___x_316_ = l_Lean_MessageData_ofFormat(v___x_315_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10);
v___x_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object* v_mvarId_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_){
_start:
{
lean_object* v___x_325_; 
lean_inc(v_mvarId_319_);
v___x_325_ = l_Lean_MVarId_getType_x27(v_mvarId_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_a_326_ = lean_ctor_get(v___x_325_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v___x_325_, 1);
v___x_327_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_328_ = lean_unsigned_to_nat(3u);
v___x_329_ = l_Lean_Expr_isAppOfArity(v_a_326_, v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_a_326_);
v___x_330_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_331_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7);
v___x_332_ = l_Lean_Meta_throwTacticEx___redArg(v___x_330_, v_mvarId_319_, v___x_331_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v___f_334_; lean_object* v___x_335_; lean_object* v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; 
v___x_333_ = lean_box(v___x_329_);
v___f_334_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_334_, 0, v___x_333_);
v___x_335_ = l_Lean_Expr_appFn_x21(v_a_326_);
v___x_336_ = l_Lean_Expr_appArg_x21(v___x_335_);
lean_dec_ref(v___x_335_);
v___x_337_ = 0;
v___x_338_ = l_Lean_Meta_delta_x3f(v___x_336_, v___f_334_, v___x_337_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_a_339_);
lean_dec_ref_known(v___x_338_, 1);
if (lean_obj_tag(v_a_339_) == 1)
{
lean_object* v_val_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_val_340_ = lean_ctor_get(v_a_339_, 0);
lean_inc(v_val_340_);
lean_dec_ref_known(v_a_339_, 1);
v___x_341_ = l_Lean_Expr_appArg_x21(v_a_326_);
lean_dec(v_a_326_);
v___x_342_ = l_Lean_Meta_mkEq(v_val_340_, v___x_341_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_319_, v_a_343_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_344_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_mvarId_319_);
v_a_345_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_342_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_342_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_a_339_);
lean_dec(v_a_326_);
v___x_353_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_354_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11);
v___x_355_ = l_Lean_Meta_throwTacticEx___redArg(v___x_353_, v_mvarId_319_, v___x_354_, v___y_320_, v___y_321_, v___y_322_, v___y_323_);
return v___x_355_;
}
}
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec(v_a_326_);
lean_dec(v_mvarId_319_);
v_a_356_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_338_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_338_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec(v_mvarId_319_);
v_a_364_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_325_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_325_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(lean_object* v_mvarId_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Elab_Eqns_deltaLHS___lam__1(v_mvarId_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object* v_mvarId_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v___f_385_; lean_object* v___x_386_; 
lean_inc(v_mvarId_379_);
v___f_385_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed), 6, 1);
lean_closure_set(v___f_385_, 0, v_mvarId_379_);
v___x_386_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_379_, v___f_385_, v_a_380_, v_a_381_, v_a_382_, v_a_383_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object* v_mvarId_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Elab_Eqns_deltaLHS(v_mvarId_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object* v_mvarId_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = ((lean_object*)(l_Lean_Elab_Eqns_tryContradiction___closed__0));
v___x_404_ = l_Lean_MVarId_contradictionCore(v_mvarId_397_, v___x_403_, v_a_398_, v_a_399_, v_a_400_, v_a_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object* v_mvarId_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_);
lean_dec(v_a_409_);
lean_dec_ref(v_a_408_);
lean_dec(v_a_407_);
lean_dec_ref(v_a_406_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(lean_object* v_msg_412_){
_start:
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = l_Lean_instInhabitedExpr;
v___x_414_ = lean_panic_fn_borrowed(v___x_413_, v_msg_412_);
return v___x_414_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0(void){
_start:
{
lean_object* v___x_415_; lean_object* v_dummy_416_; 
v___x_415_ = lean_box(0);
v_dummy_416_ = l_Lean_Expr_sort___override(v___x_415_);
return v_dummy_416_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3));
v___x_421_ = lean_unsigned_to_nat(18u);
v___x_422_ = lean_unsigned_to_nat(1896u);
v___x_423_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2));
v___x_424_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1));
v___x_425_ = l_mkPanicMessageWithDecl(v___x_424_, v___x_423_, v___x_422_, v___x_421_, v___x_420_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(lean_object* v_e_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_whnfR(v_e_426_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_434_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
v___x_434_ = l_Lean_Expr_getAppFn(v_a_433_);
if (lean_obj_tag(v___x_434_) == 11)
{
lean_object* v_struct_435_; lean_object* v___x_436_; 
lean_dec_ref_known(v___x_432_, 1);
v_struct_435_ = lean_ctor_get(v___x_434_, 2);
lean_inc_ref(v_struct_435_);
v___x_436_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_struct_435_, v_a_427_, v_a_428_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_462_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_462_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_462_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_462_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___y_442_; 
if (lean_obj_tag(v___x_434_) == 11)
{
lean_object* v_typeName_453_; lean_object* v_idx_454_; lean_object* v_struct_455_; size_t v___x_456_; size_t v___x_457_; uint8_t v___x_458_; 
v_typeName_453_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_typeName_453_);
v_idx_454_ = lean_ctor_get(v___x_434_, 1);
lean_inc(v_idx_454_);
v_struct_455_ = lean_ctor_get(v___x_434_, 2);
lean_inc_ref(v_struct_455_);
v___x_456_ = lean_ptr_addr(v_struct_455_);
lean_dec_ref(v_struct_455_);
v___x_457_ = lean_ptr_addr(v_a_437_);
v___x_458_ = lean_usize_dec_eq(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec_ref_known(v___x_434_, 3);
v___x_459_ = l_Lean_Expr_proj___override(v_typeName_453_, v_idx_454_, v_a_437_);
v___y_442_ = v___x_459_;
goto v___jp_441_;
}
else
{
lean_dec(v_idx_454_);
lean_dec(v_typeName_453_);
lean_dec(v_a_437_);
v___y_442_ = v___x_434_;
goto v___jp_441_;
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v_a_437_);
lean_dec_ref_known(v___x_434_, 3);
v___x_460_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4);
v___x_461_ = l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(v___x_460_);
v___y_442_ = v___x_461_;
goto v___jp_441_;
}
v___jp_441_:
{
lean_object* v_dummy_443_; lean_object* v_nargs_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_451_; 
v_dummy_443_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0);
v_nargs_444_ = l_Lean_Expr_getAppNumArgs(v_a_433_);
lean_inc(v_nargs_444_);
v___x_445_ = lean_mk_array(v_nargs_444_, v_dummy_443_);
v___x_446_ = lean_unsigned_to_nat(1u);
v___x_447_ = lean_nat_sub(v_nargs_444_, v___x_446_);
lean_dec(v_nargs_444_);
v___x_448_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_433_, v___x_445_, v___x_447_);
v___x_449_ = l_Lean_mkAppN(v___y_442_, v___x_448_);
lean_dec_ref(v___x_448_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_449_);
v___x_451_ = v___x_439_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v___x_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_434_, 3);
lean_dec(v_a_433_);
return v___x_436_;
}
}
else
{
lean_dec_ref(v___x_434_);
lean_dec(v_a_433_);
return v___x_432_;
}
}
else
{
return v___x_432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object* v_e_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_e_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_);
lean_dec(v_a_467_);
lean_dec_ref(v_a_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object* v_mvarId_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
lean_object* v___x_476_; 
lean_inc(v_mvarId_470_);
v___x_476_ = l_Lean_MVarId_getType_x27(v_mvarId_470_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_539_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_539_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_539_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_539_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_481_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_482_ = lean_unsigned_to_nat(3u);
v___x_483_ = l_Lean_Expr_isAppOfArity(v_a_477_, v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_486_; 
lean_dec(v_a_477_);
lean_dec(v_mvarId_470_);
v___x_484_ = lean_box(0);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_484_);
v___x_486_ = v___x_479_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
lean_del_object(v___x_479_);
v___x_488_ = l_Lean_Expr_appFn_x21(v_a_477_);
v___x_489_ = l_Lean_Expr_appArg_x21(v___x_488_);
lean_dec_ref(v___x_488_);
lean_inc_ref(v___x_489_);
v___x_490_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v___x_489_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_530_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_530_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_530_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_530_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint8_t v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_expr_eqv(v_a_491_, v___x_489_);
lean_dec_ref(v___x_489_);
v___x_496_ = lean_bool_not(v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; lean_object* v___x_499_; 
lean_dec(v_a_491_);
lean_dec(v_a_477_);
lean_dec(v_mvarId_470_);
v___x_497_ = lean_box(0);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_497_);
v___x_499_ = v___x_493_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v___x_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_del_object(v___x_493_);
v___x_501_ = l_Lean_Expr_appArg_x21(v_a_477_);
lean_dec(v_a_477_);
v___x_502_ = l_Lean_Meta_mkEq(v_a_491_, v___x_501_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_470_, v_a_503_, v___y_471_, v___y_472_, v___y_473_, v___y_474_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v_a_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_513_; 
v_a_505_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_513_ == 0)
{
v___x_507_ = v___x_504_;
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_a_505_);
lean_dec(v___x_504_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_509_, 0, v_a_505_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
v_a_514_ = lean_ctor_get(v___x_504_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_504_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_504_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec(v_mvarId_470_);
v_a_522_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_502_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_502_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec_ref(v___x_489_);
lean_dec(v_a_477_);
lean_dec(v_mvarId_470_);
v_a_531_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_490_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_490_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_mvarId_470_);
v_a_540_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_476_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_476_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(lean_object* v_mvarId_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(v_mvarId_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object* v_mvarId_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___f_561_; lean_object* v___x_562_; 
lean_inc(v_mvarId_555_);
v___f_561_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_561_, 0, v_mvarId_555_);
v___x_562_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_555_, v___f_561_, v_a_556_, v_a_557_, v_a_558_, v_a_559_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object* v_mvarId_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
lean_dec(v_a_567_);
lean_dec_ref(v_a_566_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
return v_res_569_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Split(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Delta(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_SplitIf(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_PreDefinition_EqnsUtils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
