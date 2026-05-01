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
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpMatch_x3f___boxed(lean_object* v_mvarId_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Elab_Eqns_simpMatch_x3f(v_mvarId_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_);
lean_dec(v_a_34_);
lean_dec_ref(v_a_33_);
lean_dec(v_a_32_);
lean_dec_ref(v_a_31_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object* v_mvarId_37_, uint8_t v_useNewSemantics_38_, lean_object* v_a_39_, lean_object* v_a_40_, lean_object* v_a_41_, lean_object* v_a_42_){
_start:
{
uint8_t v___x_44_; lean_object* v___x_45_; 
v___x_44_ = 1;
lean_inc(v_mvarId_37_);
v___x_45_ = l_Lean_Meta_simpIfTarget(v_mvarId_37_, v___x_44_, v_useNewSemantics_38_, v_a_39_, v_a_40_, v_a_41_, v_a_42_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v_a_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_59_; 
v_a_46_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_59_ == 0)
{
v___x_48_ = v___x_45_;
v_isShared_49_ = v_isSharedCheck_59_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_a_46_);
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_59_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
uint8_t v___x_50_; 
v___x_50_ = l_Lean_instBEqMVarId_beq(v_mvarId_37_, v_a_46_);
lean_dec(v_mvarId_37_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v_a_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_51_);
v___x_53_ = v___x_48_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
else
{
lean_object* v___x_55_; lean_object* v___x_57_; 
lean_dec(v_a_46_);
v___x_55_ = lean_box(0);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_55_);
v___x_57_ = v___x_48_;
goto v_reusejp_56_;
}
else
{
lean_object* v_reuseFailAlloc_58_; 
v_reuseFailAlloc_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_58_, 0, v___x_55_);
v___x_57_ = v_reuseFailAlloc_58_;
goto v_reusejp_56_;
}
v_reusejp_56_:
{
return v___x_57_;
}
}
}
}
else
{
lean_object* v_a_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_67_; 
lean_dec(v_mvarId_37_);
v_a_60_ = lean_ctor_get(v___x_45_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_45_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_45_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_45_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_65_; 
if (v_isShared_63_ == 0)
{
v___x_65_ = v___x_62_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_a_60_);
v___x_65_ = v_reuseFailAlloc_66_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
return v___x_65_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_simpIf_x3f___boxed(lean_object* v_mvarId_68_, lean_object* v_useNewSemantics_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
uint8_t v_useNewSemantics_boxed_75_; lean_object* v_res_76_; 
v_useNewSemantics_boxed_75_ = lean_unbox(v_useNewSemantics_69_);
v_res_76_ = l_Lean_Elab_Eqns_simpIf_x3f(v_mvarId_68_, v_useNewSemantics_boxed_75_, v_a_70_, v_a_71_, v_a_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_a_72_);
lean_dec(v_a_71_);
lean_dec_ref(v_a_70_);
return v_res_76_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(lean_object* v_opts_77_, lean_object* v_opt_78_){
_start:
{
lean_object* v_name_79_; lean_object* v_defValue_80_; lean_object* v_map_81_; lean_object* v___x_82_; 
v_name_79_ = lean_ctor_get(v_opt_78_, 0);
v_defValue_80_ = lean_ctor_get(v_opt_78_, 1);
v_map_81_ = lean_ctor_get(v_opts_77_, 0);
v___x_82_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_81_, v_name_79_);
if (lean_obj_tag(v___x_82_) == 0)
{
uint8_t v___x_83_; 
v___x_83_ = lean_unbox(v_defValue_80_);
return v___x_83_;
}
else
{
lean_object* v_val_84_; 
v_val_84_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_val_84_);
lean_dec_ref(v___x_82_);
if (lean_obj_tag(v_val_84_) == 1)
{
uint8_t v_v_85_; 
v_v_85_ = lean_ctor_get_uint8(v_val_84_, 0);
lean_dec_ref(v_val_84_);
return v_v_85_;
}
else
{
uint8_t v___x_86_; 
lean_dec(v_val_84_);
v___x_86_ = lean_unbox(v_defValue_80_);
return v___x_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1___boxed(lean_object* v_opts_87_, lean_object* v_opt_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_opts_87_, v_opt_88_);
lean_dec_ref(v_opt_88_);
lean_dec_ref(v_opts_87_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(lean_object* v_opts_91_, lean_object* v_opt_92_){
_start:
{
lean_object* v_name_93_; lean_object* v_defValue_94_; lean_object* v_map_95_; lean_object* v___x_96_; 
v_name_93_ = lean_ctor_get(v_opt_92_, 0);
v_defValue_94_ = lean_ctor_get(v_opt_92_, 1);
v_map_95_ = lean_ctor_get(v_opts_91_, 0);
v___x_96_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_95_, v_name_93_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_inc(v_defValue_94_);
return v_defValue_94_;
}
else
{
lean_object* v_val_97_; 
v_val_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_val_97_);
lean_dec_ref(v___x_96_);
if (lean_obj_tag(v_val_97_) == 3)
{
lean_object* v_v_98_; 
v_v_98_ = lean_ctor_get(v_val_97_, 0);
lean_inc(v_v_98_);
lean_dec_ref(v_val_97_);
return v_v_98_;
}
else
{
lean_dec(v_val_97_);
lean_inc(v_defValue_94_);
return v_defValue_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2___boxed(lean_object* v_opts_99_, lean_object* v_opt_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(v_opts_99_, v_opt_100_);
lean_dec_ref(v_opt_100_);
lean_dec_ref(v_opts_99_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(lean_object* v_o_105_, lean_object* v_k_106_, uint8_t v_v_107_){
_start:
{
lean_object* v_map_108_; uint8_t v_hasTrace_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_123_; 
v_map_108_ = lean_ctor_get(v_o_105_, 0);
v_hasTrace_109_ = lean_ctor_get_uint8(v_o_105_, sizeof(void*)*1);
v_isSharedCheck_123_ = !lean_is_exclusive(v_o_105_);
if (v_isSharedCheck_123_ == 0)
{
v___x_111_ = v_o_105_;
v_isShared_112_ = v_isSharedCheck_123_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_map_108_);
lean_dec(v_o_105_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_123_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_113_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_113_, 0, v_v_107_);
lean_inc(v_k_106_);
v___x_114_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_106_, v___x_113_, v_map_108_);
if (v_hasTrace_109_ == 0)
{
lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_118_; 
v___x_115_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___closed__1));
v___x_116_ = l_Lean_Name_isPrefixOf(v___x_115_, v_k_106_);
lean_dec(v_k_106_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_114_);
v___x_118_ = v___x_111_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_114_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
lean_ctor_set_uint8(v___x_118_, sizeof(void*)*1, v___x_116_);
return v___x_118_;
}
}
else
{
lean_object* v___x_121_; 
lean_dec(v_k_106_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_114_);
v___x_121_ = v___x_111_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_114_);
lean_ctor_set_uint8(v_reuseFailAlloc_122_, sizeof(void*)*1, v_hasTrace_109_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0___boxed(lean_object* v_o_124_, lean_object* v_k_125_, lean_object* v_v_126_){
_start:
{
uint8_t v_v_boxed_127_; lean_object* v_res_128_; 
v_v_boxed_127_ = lean_unbox(v_v_126_);
v_res_128_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(v_o_124_, v_k_125_, v_v_boxed_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(lean_object* v_opts_129_, lean_object* v_opt_130_, uint8_t v_val_131_){
_start:
{
lean_object* v_name_132_; lean_object* v___x_133_; 
v_name_132_ = lean_ctor_get(v_opt_130_, 0);
lean_inc(v_name_132_);
lean_dec_ref(v_opt_130_);
v___x_133_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0_spec__0(v_opts_129_, v_name_132_, v_val_131_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0___boxed(lean_object* v_opts_134_, lean_object* v_opt_135_, lean_object* v_val_136_){
_start:
{
uint8_t v_val_boxed_137_; lean_object* v_res_138_; 
v_val_boxed_137_ = lean_unbox(v_val_136_);
v_res_138_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(v_opts_134_, v_opt_135_, v_val_boxed_137_);
return v_res_138_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__0(void){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__1(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__0, &l_Lean_Elab_Eqns_tryURefl___closed__0_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__0);
v___x_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__2(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__1, &l_Lean_Elab_Eqns_tryURefl___closed__1_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__1);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object* v_mvarId_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___y_151_; uint8_t v___y_152_; lean_object* v___x_156_; lean_object* v_fileName_157_; lean_object* v_fileMap_158_; lean_object* v_options_159_; lean_object* v_currRecDepth_160_; lean_object* v_ref_161_; lean_object* v_currNamespace_162_; lean_object* v_openDecls_163_; lean_object* v_initHeartbeats_164_; lean_object* v_maxHeartbeats_165_; lean_object* v_quotContext_166_; lean_object* v_currMacroScope_167_; lean_object* v_cancelTk_x3f_168_; uint8_t v_suppressElabErrors_169_; lean_object* v_inheritedTraceOptions_170_; lean_object* v_env_171_; uint8_t v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v_fileName_179_; lean_object* v_fileMap_180_; lean_object* v_currRecDepth_181_; lean_object* v_ref_182_; lean_object* v_currNamespace_183_; lean_object* v_openDecls_184_; lean_object* v_initHeartbeats_185_; lean_object* v_maxHeartbeats_186_; lean_object* v_quotContext_187_; lean_object* v_currMacroScope_188_; lean_object* v_cancelTk_x3f_189_; uint8_t v_suppressElabErrors_190_; lean_object* v_inheritedTraceOptions_191_; lean_object* v___y_192_; uint8_t v___y_210_; uint8_t v___x_231_; 
v___x_156_ = lean_st_ref_get(v_a_148_);
v_fileName_157_ = lean_ctor_get(v_a_147_, 0);
v_fileMap_158_ = lean_ctor_get(v_a_147_, 1);
v_options_159_ = lean_ctor_get(v_a_147_, 2);
v_currRecDepth_160_ = lean_ctor_get(v_a_147_, 3);
v_ref_161_ = lean_ctor_get(v_a_147_, 5);
v_currNamespace_162_ = lean_ctor_get(v_a_147_, 6);
v_openDecls_163_ = lean_ctor_get(v_a_147_, 7);
v_initHeartbeats_164_ = lean_ctor_get(v_a_147_, 8);
v_maxHeartbeats_165_ = lean_ctor_get(v_a_147_, 9);
v_quotContext_166_ = lean_ctor_get(v_a_147_, 10);
v_currMacroScope_167_ = lean_ctor_get(v_a_147_, 11);
v_cancelTk_x3f_168_ = lean_ctor_get(v_a_147_, 12);
v_suppressElabErrors_169_ = lean_ctor_get_uint8(v_a_147_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_170_ = lean_ctor_get(v_a_147_, 13);
v_env_171_ = lean_ctor_get(v___x_156_, 0);
lean_inc_ref(v_env_171_);
lean_dec(v___x_156_);
v___x_172_ = 1;
v___x_173_ = l_Lean_Meta_smartUnfolding;
v___x_174_ = 0;
lean_inc_ref(v_options_159_);
v___x_175_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(v_options_159_, v___x_173_, v___x_174_);
v___x_176_ = l_Lean_diagnostics;
v___x_177_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(v___x_175_, v___x_176_);
v___x_231_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_171_);
lean_dec_ref(v_env_171_);
if (v___x_231_ == 0)
{
if (v___x_177_ == 0)
{
v_fileName_179_ = v_fileName_157_;
v_fileMap_180_ = v_fileMap_158_;
v_currRecDepth_181_ = v_currRecDepth_160_;
v_ref_182_ = v_ref_161_;
v_currNamespace_183_ = v_currNamespace_162_;
v_openDecls_184_ = v_openDecls_163_;
v_initHeartbeats_185_ = v_initHeartbeats_164_;
v_maxHeartbeats_186_ = v_maxHeartbeats_165_;
v_quotContext_187_ = v_quotContext_166_;
v_currMacroScope_188_ = v_currMacroScope_167_;
v_cancelTk_x3f_189_ = v_cancelTk_x3f_168_;
v_suppressElabErrors_190_ = v_suppressElabErrors_169_;
v_inheritedTraceOptions_191_ = v_inheritedTraceOptions_170_;
v___y_192_ = v_a_148_;
goto v___jp_178_;
}
else
{
v___y_210_ = v___x_231_;
goto v___jp_209_;
}
}
else
{
v___y_210_ = v___x_177_;
goto v___jp_209_;
}
v___jp_150_:
{
if (v___y_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec_ref(v___y_151_);
v___x_153_ = lean_box(v___y_152_);
v___x_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
return v___x_154_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_155_, 0, v___y_151_);
return v___x_155_;
}
}
v___jp_178_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_193_ = l_Lean_maxRecDepth;
v___x_194_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(v___x_175_, v___x_193_);
lean_inc_ref(v_inheritedTraceOptions_191_);
lean_inc(v_cancelTk_x3f_189_);
lean_inc(v_currMacroScope_188_);
lean_inc(v_quotContext_187_);
lean_inc(v_maxHeartbeats_186_);
lean_inc(v_initHeartbeats_185_);
lean_inc(v_openDecls_184_);
lean_inc(v_currNamespace_183_);
lean_inc(v_ref_182_);
lean_inc(v_currRecDepth_181_);
lean_inc_ref(v_fileMap_180_);
lean_inc_ref(v_fileName_179_);
v___x_195_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_195_, 0, v_fileName_179_);
lean_ctor_set(v___x_195_, 1, v_fileMap_180_);
lean_ctor_set(v___x_195_, 2, v___x_175_);
lean_ctor_set(v___x_195_, 3, v_currRecDepth_181_);
lean_ctor_set(v___x_195_, 4, v___x_194_);
lean_ctor_set(v___x_195_, 5, v_ref_182_);
lean_ctor_set(v___x_195_, 6, v_currNamespace_183_);
lean_ctor_set(v___x_195_, 7, v_openDecls_184_);
lean_ctor_set(v___x_195_, 8, v_initHeartbeats_185_);
lean_ctor_set(v___x_195_, 9, v_maxHeartbeats_186_);
lean_ctor_set(v___x_195_, 10, v_quotContext_187_);
lean_ctor_set(v___x_195_, 11, v_currMacroScope_188_);
lean_ctor_set(v___x_195_, 12, v_cancelTk_x3f_189_);
lean_ctor_set(v___x_195_, 13, v_inheritedTraceOptions_191_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*14, v___x_177_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*14 + 1, v_suppressElabErrors_190_);
v___x_196_ = l_Lean_MVarId_refl(v_mvarId_144_, v___x_172_, v_a_145_, v_a_146_, v___x_195_, v___y_192_);
lean_dec_ref(v___x_195_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_204_; 
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_204_ == 0)
{
lean_object* v_unused_205_; 
v_unused_205_ = lean_ctor_get(v___x_196_, 0);
lean_dec(v_unused_205_);
v___x_198_ = v___x_196_;
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
else
{
lean_dec(v___x_196_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_204_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_box(v___x_172_);
if (v_isShared_199_ == 0)
{
lean_ctor_set(v___x_198_, 0, v___x_200_);
v___x_202_ = v___x_198_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
else
{
lean_object* v_a_206_; uint8_t v___x_207_; 
v_a_206_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_206_);
lean_dec_ref(v___x_196_);
v___x_207_ = l_Lean_Exception_isInterrupt(v_a_206_);
if (v___x_207_ == 0)
{
uint8_t v___x_208_; 
lean_inc(v_a_206_);
v___x_208_ = l_Lean_Exception_isRuntime(v_a_206_);
v___y_151_ = v_a_206_;
v___y_152_ = v___x_208_;
goto v___jp_150_;
}
else
{
v___y_151_ = v_a_206_;
v___y_152_ = v___x_207_;
goto v___jp_150_;
}
}
}
v___jp_209_:
{
if (v___y_210_ == 0)
{
lean_object* v___x_211_; lean_object* v_env_212_; lean_object* v_nextMacroScope_213_; lean_object* v_ngen_214_; lean_object* v_auxDeclNGen_215_; lean_object* v_traceState_216_; lean_object* v_messages_217_; lean_object* v_infoState_218_; lean_object* v_snapshotTasks_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_229_; 
v___x_211_ = lean_st_ref_take(v_a_148_);
v_env_212_ = lean_ctor_get(v___x_211_, 0);
v_nextMacroScope_213_ = lean_ctor_get(v___x_211_, 1);
v_ngen_214_ = lean_ctor_get(v___x_211_, 2);
v_auxDeclNGen_215_ = lean_ctor_get(v___x_211_, 3);
v_traceState_216_ = lean_ctor_get(v___x_211_, 4);
v_messages_217_ = lean_ctor_get(v___x_211_, 6);
v_infoState_218_ = lean_ctor_get(v___x_211_, 7);
v_snapshotTasks_219_ = lean_ctor_get(v___x_211_, 8);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___x_211_, 5);
lean_dec(v_unused_230_);
v___x_221_ = v___x_211_;
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_snapshotTasks_219_);
lean_inc(v_infoState_218_);
lean_inc(v_messages_217_);
lean_inc(v_traceState_216_);
lean_inc(v_auxDeclNGen_215_);
lean_inc(v_ngen_214_);
lean_inc(v_nextMacroScope_213_);
lean_inc(v_env_212_);
lean_dec(v___x_211_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_229_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_223_ = l_Lean_Kernel_enableDiag(v_env_212_, v___x_177_);
v___x_224_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__2, &l_Lean_Elab_Eqns_tryURefl___closed__2_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__2);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 5, v___x_224_);
lean_ctor_set(v___x_221_, 0, v___x_223_);
v___x_226_ = v___x_221_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_nextMacroScope_213_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_ngen_214_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_auxDeclNGen_215_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_traceState_216_);
lean_ctor_set(v_reuseFailAlloc_228_, 5, v___x_224_);
lean_ctor_set(v_reuseFailAlloc_228_, 6, v_messages_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 7, v_infoState_218_);
lean_ctor_set(v_reuseFailAlloc_228_, 8, v_snapshotTasks_219_);
v___x_226_ = v_reuseFailAlloc_228_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
lean_object* v___x_227_; 
v___x_227_ = lean_st_ref_set(v_a_148_, v___x_226_);
v_fileName_179_ = v_fileName_157_;
v_fileMap_180_ = v_fileMap_158_;
v_currRecDepth_181_ = v_currRecDepth_160_;
v_ref_182_ = v_ref_161_;
v_currNamespace_183_ = v_currNamespace_162_;
v_openDecls_184_ = v_openDecls_163_;
v_initHeartbeats_185_ = v_initHeartbeats_164_;
v_maxHeartbeats_186_ = v_maxHeartbeats_165_;
v_quotContext_187_ = v_quotContext_166_;
v_currMacroScope_188_ = v_currMacroScope_167_;
v_cancelTk_x3f_189_ = v_cancelTk_x3f_168_;
v_suppressElabErrors_190_ = v_suppressElabErrors_169_;
v_inheritedTraceOptions_191_ = v_inheritedTraceOptions_170_;
v___y_192_ = v_a_148_;
goto v___jp_178_;
}
}
}
else
{
v_fileName_179_ = v_fileName_157_;
v_fileMap_180_ = v_fileMap_158_;
v_currRecDepth_181_ = v_currRecDepth_160_;
v_ref_182_ = v_ref_161_;
v_currNamespace_183_ = v_currNamespace_162_;
v_openDecls_184_ = v_openDecls_163_;
v_initHeartbeats_185_ = v_initHeartbeats_164_;
v_maxHeartbeats_186_ = v_maxHeartbeats_165_;
v_quotContext_187_ = v_quotContext_166_;
v_currMacroScope_188_ = v_currMacroScope_167_;
v_cancelTk_x3f_189_ = v_cancelTk_x3f_168_;
v_suppressElabErrors_190_ = v_suppressElabErrors_169_;
v_inheritedTraceOptions_191_ = v_inheritedTraceOptions_170_;
v___y_192_ = v_a_148_;
goto v___jp_178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object* v_mvarId_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(lean_object* v_mvarId_239_, lean_object* v_x_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_239_, v_x_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_246_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
v_a_255_ = lean_ctor_get(v___x_246_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_246_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_246_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_246_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg___boxed(lean_object* v_mvarId_263_, lean_object* v_x_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_263_, v_x_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(lean_object* v_00_u03b1_271_, lean_object* v_mvarId_272_, lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_272_, v_x_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___boxed(lean_object* v_00_u03b1_280_, lean_object* v_mvarId_281_, lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(v_00_u03b1_280_, v_mvarId_281_, v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec_ref(v___y_283_);
return v_res_288_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t v___x_289_, lean_object* v_x_290_){
_start:
{
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object* v___x_291_, lean_object* v_x_292_){
_start:
{
uint8_t v___x_1020__boxed_293_; uint8_t v_res_294_; lean_object* v_r_295_; 
v___x_1020__boxed_293_ = lean_unbox(v___x_291_);
v_res_294_ = l_Lean_Elab_Eqns_deltaLHS___lam__0(v___x_1020__boxed_293_, v_x_292_);
lean_dec(v_x_292_);
v_r_295_ = lean_box(v_res_294_);
return v_r_295_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5));
v___x_306_ = l_Lean_MessageData_ofFormat(v___x_305_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6);
v___x_308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_308_, 0, v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9));
v___x_313_ = l_Lean_MessageData_ofFormat(v___x_312_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10);
v___x_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object* v_mvarId_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v___x_322_; 
lean_inc(v_mvarId_316_);
v___x_322_ = l_Lean_MVarId_getType_x27(v_mvarId_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref(v___x_322_);
v___x_324_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_325_ = lean_unsigned_to_nat(3u);
v___x_326_ = l_Lean_Expr_isAppOfArity(v_a_323_, v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v_a_323_);
v___x_327_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_328_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7);
v___x_329_ = l_Lean_Meta_throwTacticEx___redArg(v___x_327_, v_mvarId_316_, v___x_328_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; 
v___x_330_ = lean_box(v___x_326_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_331_, 0, v___x_330_);
v___x_332_ = l_Lean_Expr_appFn_x21(v_a_323_);
v___x_333_ = l_Lean_Expr_appArg_x21(v___x_332_);
lean_dec_ref(v___x_332_);
v___x_334_ = 0;
v___x_335_ = l_Lean_Meta_delta_x3f(v___x_333_, v___f_331_, v___x_334_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref(v___x_335_);
if (lean_obj_tag(v_a_336_) == 1)
{
lean_object* v_val_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_val_337_ = lean_ctor_get(v_a_336_, 0);
lean_inc(v_val_337_);
lean_dec_ref(v_a_336_);
v___x_338_ = l_Lean_Expr_appArg_x21(v_a_323_);
lean_dec(v_a_323_);
v___x_339_ = l_Lean_Meta_mkEq(v_val_337_, v___x_338_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref(v___x_339_);
v___x_341_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_316_, v_a_340_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
return v___x_341_;
}
else
{
lean_object* v_a_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_349_; 
lean_dec(v_mvarId_316_);
v_a_342_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_349_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_349_ == 0)
{
v___x_344_ = v___x_339_;
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_a_342_);
lean_dec(v___x_339_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_349_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
return v___x_347_;
}
}
}
}
else
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v_a_336_);
lean_dec(v_a_323_);
v___x_350_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_351_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11);
v___x_352_ = l_Lean_Meta_throwTacticEx___redArg(v___x_350_, v_mvarId_316_, v___x_351_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
return v___x_352_;
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec(v_a_323_);
lean_dec(v_mvarId_316_);
v_a_353_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_335_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_335_);
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
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec(v_mvarId_316_);
v_a_361_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_322_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_322_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(lean_object* v_mvarId_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Elab_Eqns_deltaLHS___lam__1(v_mvarId_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object* v_mvarId_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___f_382_; lean_object* v___x_383_; 
lean_inc(v_mvarId_376_);
v___f_382_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed), 6, 1);
lean_closure_set(v___f_382_, 0, v_mvarId_376_);
v___x_383_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_376_, v___f_382_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object* v_mvarId_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Elab_Eqns_deltaLHS(v_mvarId_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object* v_mvarId_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_Elab_Eqns_tryContradiction___closed__0));
v___x_401_ = l_Lean_MVarId_contradictionCore(v_mvarId_394_, v___x_400_, v_a_395_, v_a_396_, v_a_397_, v_a_398_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object* v_mvarId_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(lean_object* v_msg_409_){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_410_ = l_Lean_instInhabitedExpr;
v___x_411_ = lean_panic_fn_borrowed(v___x_410_, v_msg_409_);
return v___x_411_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0(void){
_start:
{
lean_object* v___x_412_; lean_object* v_dummy_413_; 
v___x_412_ = lean_box(0);
v_dummy_413_ = l_Lean_Expr_sort___override(v___x_412_);
return v_dummy_413_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4(void){
_start:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_417_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3));
v___x_418_ = lean_unsigned_to_nat(18u);
v___x_419_ = lean_unsigned_to_nat(1878u);
v___x_420_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2));
v___x_421_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1));
v___x_422_ = l_mkPanicMessageWithDecl(v___x_421_, v___x_420_, v___x_419_, v___x_418_, v___x_417_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(lean_object* v_e_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Meta_whnfR(v_e_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
v___x_431_ = l_Lean_Expr_getAppFn(v_a_430_);
if (lean_obj_tag(v___x_431_) == 11)
{
lean_object* v_struct_432_; lean_object* v___x_433_; 
lean_dec_ref(v___x_429_);
v_struct_432_ = lean_ctor_get(v___x_431_, 2);
lean_inc_ref(v_struct_432_);
v___x_433_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_struct_432_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_459_; 
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_459_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_459_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_459_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___y_439_; 
if (lean_obj_tag(v___x_431_) == 11)
{
lean_object* v_typeName_450_; lean_object* v_idx_451_; lean_object* v_struct_452_; size_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v_typeName_450_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_typeName_450_);
v_idx_451_ = lean_ctor_get(v___x_431_, 1);
lean_inc(v_idx_451_);
v_struct_452_ = lean_ctor_get(v___x_431_, 2);
lean_inc_ref(v_struct_452_);
v___x_453_ = lean_ptr_addr(v_struct_452_);
lean_dec_ref(v_struct_452_);
v___x_454_ = lean_ptr_addr(v_a_434_);
v___x_455_ = lean_usize_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; 
lean_dec_ref(v___x_431_);
v___x_456_ = l_Lean_Expr_proj___override(v_typeName_450_, v_idx_451_, v_a_434_);
v___y_439_ = v___x_456_;
goto v___jp_438_;
}
else
{
lean_dec(v_idx_451_);
lean_dec(v_typeName_450_);
lean_dec(v_a_434_);
v___y_439_ = v___x_431_;
goto v___jp_438_;
}
}
else
{
lean_object* v___x_457_; lean_object* v___x_458_; 
lean_dec(v_a_434_);
lean_dec_ref(v___x_431_);
v___x_457_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4);
v___x_458_ = l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(v___x_457_);
v___y_439_ = v___x_458_;
goto v___jp_438_;
}
v___jp_438_:
{
lean_object* v_dummy_440_; lean_object* v_nargs_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v_dummy_440_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0);
v_nargs_441_ = l_Lean_Expr_getAppNumArgs(v_a_430_);
lean_inc(v_nargs_441_);
v___x_442_ = lean_mk_array(v_nargs_441_, v_dummy_440_);
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_sub(v_nargs_441_, v___x_443_);
lean_dec(v_nargs_441_);
v___x_445_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_430_, v___x_442_, v___x_444_);
v___x_446_ = l_Lean_mkAppN(v___y_439_, v___x_445_);
lean_dec_ref(v___x_445_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 0, v___x_446_);
v___x_448_ = v___x_436_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_446_);
v___x_448_ = v_reuseFailAlloc_449_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
return v___x_448_;
}
}
}
}
else
{
lean_dec_ref(v___x_431_);
lean_dec(v_a_430_);
return v___x_433_;
}
}
else
{
lean_dec_ref(v___x_431_);
lean_dec(v_a_430_);
return v___x_429_;
}
}
else
{
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object* v_e_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_e_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object* v_mvarId_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___x_473_; 
lean_inc(v_mvarId_467_);
v___x_473_ = l_Lean_MVarId_getType_x27(v_mvarId_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_535_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_535_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_535_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_535_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_478_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_479_ = lean_unsigned_to_nat(3u);
v___x_480_ = l_Lean_Expr_isAppOfArity(v_a_474_, v___x_478_, v___x_479_);
if (v___x_480_ == 0)
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_dec(v_a_474_);
lean_dec(v_mvarId_467_);
v___x_481_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 0, v___x_481_);
v___x_483_ = v___x_476_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v___x_481_);
v___x_483_ = v_reuseFailAlloc_484_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
return v___x_483_;
}
}
else
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
lean_del_object(v___x_476_);
v___x_485_ = l_Lean_Expr_appFn_x21(v_a_474_);
v___x_486_ = l_Lean_Expr_appArg_x21(v___x_485_);
lean_dec_ref(v___x_485_);
lean_inc_ref(v___x_486_);
v___x_487_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v___x_486_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_526_; 
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_526_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_526_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_526_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
uint8_t v___x_492_; 
v___x_492_ = lean_expr_eqv(v_a_488_, v___x_486_);
lean_dec_ref(v___x_486_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_del_object(v___x_490_);
v___x_493_ = l_Lean_Expr_appArg_x21(v_a_474_);
lean_dec(v_a_474_);
v___x_494_ = l_Lean_Meta_mkEq(v_a_488_, v___x_493_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_494_) == 0)
{
lean_object* v_a_495_; lean_object* v___x_496_; 
v_a_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v___x_494_);
v___x_496_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_467_, v_a_495_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_505_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_505_ == 0)
{
v___x_499_ = v___x_496_;
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_496_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_505_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v_a_497_);
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_501_);
v___x_503_ = v___x_499_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
else
{
lean_object* v_a_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_a_506_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_513_ == 0)
{
v___x_508_ = v___x_496_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_a_506_);
lean_dec(v___x_496_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_506_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec(v_mvarId_467_);
v_a_514_ = lean_ctor_get(v___x_494_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_494_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_494_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_494_);
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
lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec(v_a_488_);
lean_dec(v_a_474_);
lean_dec(v_mvarId_467_);
v___x_522_ = lean_box(0);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_522_);
v___x_524_ = v___x_490_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
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
lean_dec_ref(v___x_486_);
lean_dec(v_a_474_);
lean_dec(v_mvarId_467_);
v_a_527_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_487_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_487_);
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
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_mvarId_467_);
v_a_536_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_473_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_473_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
return v___x_541_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(lean_object* v_mvarId_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(v_mvarId_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object* v_mvarId_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v___f_557_; lean_object* v___x_558_; 
lean_inc(v_mvarId_551_);
v___f_557_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_557_, 0, v_mvarId_551_);
v___x_558_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_551_, v___f_557_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object* v_mvarId_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_565_;
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
