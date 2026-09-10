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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_dec_ref_known(v___x_82_, 1);
if (lean_obj_tag(v_val_84_) == 1)
{
uint8_t v_v_85_; 
v_v_85_ = lean_ctor_get_uint8(v_val_84_, 0);
lean_dec_ref_known(v_val_84_, 0);
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
lean_dec_ref_known(v___x_96_, 1);
if (lean_obj_tag(v_val_97_) == 3)
{
lean_object* v_v_98_; 
v_v_98_ = lean_ctor_get(v_val_97_, 0);
lean_inc(v_v_98_);
lean_dec_ref_known(v_val_97_, 1);
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
lean_object* v___y_151_; uint8_t v___y_152_; lean_object* v___x_156_; lean_object* v_toCold_157_; lean_object* v_currRecDepth_158_; lean_object* v_ref_159_; uint8_t v_suppressElabErrors_160_; lean_object* v_fileName_161_; lean_object* v_fileMap_162_; lean_object* v_options_163_; lean_object* v_currNamespace_164_; lean_object* v_openDecls_165_; lean_object* v_initHeartbeats_166_; lean_object* v_maxHeartbeats_167_; lean_object* v_quotContext_168_; lean_object* v_currMacroScope_169_; lean_object* v_cancelTk_x3f_170_; lean_object* v_inheritedTraceOptions_171_; lean_object* v_env_172_; uint8_t v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; lean_object* v_fileName_180_; lean_object* v_fileMap_181_; lean_object* v_currNamespace_182_; lean_object* v_openDecls_183_; lean_object* v_initHeartbeats_184_; lean_object* v_maxHeartbeats_185_; lean_object* v_quotContext_186_; lean_object* v_currMacroScope_187_; lean_object* v_cancelTk_x3f_188_; lean_object* v_inheritedTraceOptions_189_; lean_object* v_currRecDepth_190_; lean_object* v_ref_191_; uint8_t v_suppressElabErrors_192_; lean_object* v___y_193_; uint8_t v___y_212_; uint8_t v___x_233_; 
v___x_156_ = lean_st_ref_get(v_a_148_);
v_toCold_157_ = lean_ctor_get(v_a_147_, 0);
v_currRecDepth_158_ = lean_ctor_get(v_a_147_, 1);
v_ref_159_ = lean_ctor_get(v_a_147_, 2);
v_suppressElabErrors_160_ = lean_ctor_get_uint8(v_a_147_, sizeof(void*)*3 + 1);
v_fileName_161_ = lean_ctor_get(v_toCold_157_, 0);
v_fileMap_162_ = lean_ctor_get(v_toCold_157_, 1);
v_options_163_ = lean_ctor_get(v_toCold_157_, 2);
v_currNamespace_164_ = lean_ctor_get(v_toCold_157_, 4);
v_openDecls_165_ = lean_ctor_get(v_toCold_157_, 5);
v_initHeartbeats_166_ = lean_ctor_get(v_toCold_157_, 6);
v_maxHeartbeats_167_ = lean_ctor_get(v_toCold_157_, 7);
v_quotContext_168_ = lean_ctor_get(v_toCold_157_, 8);
v_currMacroScope_169_ = lean_ctor_get(v_toCold_157_, 9);
v_cancelTk_x3f_170_ = lean_ctor_get(v_toCold_157_, 10);
v_inheritedTraceOptions_171_ = lean_ctor_get(v_toCold_157_, 11);
v_env_172_ = lean_ctor_get(v___x_156_, 0);
lean_inc_ref(v_env_172_);
lean_dec(v___x_156_);
v___x_173_ = 1;
v___x_174_ = l_Lean_Meta_smartUnfolding;
v___x_175_ = 0;
lean_inc_ref(v_options_163_);
v___x_176_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__0(v_options_163_, v___x_174_, v___x_175_);
v___x_177_ = l_Lean_diagnostics;
v___x_178_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__1(v___x_176_, v___x_177_);
v___x_233_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_172_);
lean_dec_ref(v_env_172_);
if (v___x_178_ == 0)
{
if (v___x_233_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_171_);
lean_inc(v_cancelTk_x3f_170_);
lean_inc(v_currMacroScope_169_);
lean_inc(v_quotContext_168_);
lean_inc(v_maxHeartbeats_167_);
lean_inc(v_initHeartbeats_166_);
lean_inc(v_openDecls_165_);
lean_inc(v_currNamespace_164_);
lean_inc_ref(v_fileMap_162_);
lean_inc_ref(v_fileName_161_);
v_fileName_180_ = v_fileName_161_;
v_fileMap_181_ = v_fileMap_162_;
v_currNamespace_182_ = v_currNamespace_164_;
v_openDecls_183_ = v_openDecls_165_;
v_initHeartbeats_184_ = v_initHeartbeats_166_;
v_maxHeartbeats_185_ = v_maxHeartbeats_167_;
v_quotContext_186_ = v_quotContext_168_;
v_currMacroScope_187_ = v_currMacroScope_169_;
v_cancelTk_x3f_188_ = v_cancelTk_x3f_170_;
v_inheritedTraceOptions_189_ = v_inheritedTraceOptions_171_;
v_currRecDepth_190_ = v_currRecDepth_158_;
v_ref_191_ = v_ref_159_;
v_suppressElabErrors_192_ = v_suppressElabErrors_160_;
v___y_193_ = v_a_148_;
goto v___jp_179_;
}
else
{
v___y_212_ = v___x_178_;
goto v___jp_211_;
}
}
else
{
v___y_212_ = v___x_233_;
goto v___jp_211_;
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
v___jp_179_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_194_ = l_Lean_maxRecDepth;
v___x_195_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__2(v___x_176_, v___x_194_);
v___x_196_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_196_, 0, v_fileName_180_);
lean_ctor_set(v___x_196_, 1, v_fileMap_181_);
lean_ctor_set(v___x_196_, 2, v___x_176_);
lean_ctor_set(v___x_196_, 3, v___x_195_);
lean_ctor_set(v___x_196_, 4, v_currNamespace_182_);
lean_ctor_set(v___x_196_, 5, v_openDecls_183_);
lean_ctor_set(v___x_196_, 6, v_initHeartbeats_184_);
lean_ctor_set(v___x_196_, 7, v_maxHeartbeats_185_);
lean_ctor_set(v___x_196_, 8, v_quotContext_186_);
lean_ctor_set(v___x_196_, 9, v_currMacroScope_187_);
lean_ctor_set(v___x_196_, 10, v_cancelTk_x3f_188_);
lean_ctor_set(v___x_196_, 11, v_inheritedTraceOptions_189_);
lean_inc(v_ref_191_);
lean_inc(v_currRecDepth_190_);
v___x_197_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v_currRecDepth_190_);
lean_ctor_set(v___x_197_, 2, v_ref_191_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*3, v___x_178_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*3 + 1, v_suppressElabErrors_192_);
v___x_198_ = l_Lean_MVarId_refl(v_mvarId_144_, v___x_173_, v_a_145_, v_a_146_, v___x_197_, v___y_193_);
lean_dec_ref_known(v___x_197_, 3);
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
v___x_202_ = lean_box(v___x_173_);
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
v___y_151_ = v_a_208_;
v___y_152_ = v___x_210_;
goto v___jp_150_;
}
else
{
v___y_151_ = v_a_208_;
v___y_152_ = v___x_209_;
goto v___jp_150_;
}
}
}
v___jp_211_:
{
if (v___y_212_ == 0)
{
lean_object* v___x_213_; lean_object* v_env_214_; lean_object* v_nextMacroScope_215_; lean_object* v_ngen_216_; lean_object* v_auxDeclNGen_217_; lean_object* v_traceState_218_; lean_object* v_messages_219_; lean_object* v_infoState_220_; lean_object* v_snapshotTasks_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_231_; 
v___x_213_ = lean_st_ref_take(v_a_148_);
v_env_214_ = lean_ctor_get(v___x_213_, 0);
v_nextMacroScope_215_ = lean_ctor_get(v___x_213_, 1);
v_ngen_216_ = lean_ctor_get(v___x_213_, 2);
v_auxDeclNGen_217_ = lean_ctor_get(v___x_213_, 3);
v_traceState_218_ = lean_ctor_get(v___x_213_, 4);
v_messages_219_ = lean_ctor_get(v___x_213_, 6);
v_infoState_220_ = lean_ctor_get(v___x_213_, 7);
v_snapshotTasks_221_ = lean_ctor_get(v___x_213_, 8);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_231_ == 0)
{
lean_object* v_unused_232_; 
v_unused_232_ = lean_ctor_get(v___x_213_, 5);
lean_dec(v_unused_232_);
v___x_223_ = v___x_213_;
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_snapshotTasks_221_);
lean_inc(v_infoState_220_);
lean_inc(v_messages_219_);
lean_inc(v_traceState_218_);
lean_inc(v_auxDeclNGen_217_);
lean_inc(v_ngen_216_);
lean_inc(v_nextMacroScope_215_);
lean_inc(v_env_214_);
lean_dec(v___x_213_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_225_ = l_Lean_Kernel_enableDiag(v_env_214_, v___x_178_);
v___x_226_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__2, &l_Lean_Elab_Eqns_tryURefl___closed__2_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__2);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 5, v___x_226_);
lean_ctor_set(v___x_223_, 0, v___x_225_);
v___x_228_ = v___x_223_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_nextMacroScope_215_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_ngen_216_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_auxDeclNGen_217_);
lean_ctor_set(v_reuseFailAlloc_230_, 4, v_traceState_218_);
lean_ctor_set(v_reuseFailAlloc_230_, 5, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_230_, 6, v_messages_219_);
lean_ctor_set(v_reuseFailAlloc_230_, 7, v_infoState_220_);
lean_ctor_set(v_reuseFailAlloc_230_, 8, v_snapshotTasks_221_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_st_ref_put(v_a_148_, v___x_228_);
lean_inc_ref(v_inheritedTraceOptions_171_);
lean_inc(v_cancelTk_x3f_170_);
lean_inc(v_currMacroScope_169_);
lean_inc(v_quotContext_168_);
lean_inc(v_maxHeartbeats_167_);
lean_inc(v_initHeartbeats_166_);
lean_inc(v_openDecls_165_);
lean_inc(v_currNamespace_164_);
lean_inc_ref(v_fileMap_162_);
lean_inc_ref(v_fileName_161_);
v_fileName_180_ = v_fileName_161_;
v_fileMap_181_ = v_fileMap_162_;
v_currNamespace_182_ = v_currNamespace_164_;
v_openDecls_183_ = v_openDecls_165_;
v_initHeartbeats_184_ = v_initHeartbeats_166_;
v_maxHeartbeats_185_ = v_maxHeartbeats_167_;
v_quotContext_186_ = v_quotContext_168_;
v_currMacroScope_187_ = v_currMacroScope_169_;
v_cancelTk_x3f_188_ = v_cancelTk_x3f_170_;
v_inheritedTraceOptions_189_ = v_inheritedTraceOptions_171_;
v_currRecDepth_190_ = v_currRecDepth_158_;
v_ref_191_ = v_ref_159_;
v_suppressElabErrors_192_ = v_suppressElabErrors_160_;
v___y_193_ = v_a_148_;
goto v___jp_179_;
}
}
}
else
{
lean_inc_ref(v_inheritedTraceOptions_171_);
lean_inc(v_cancelTk_x3f_170_);
lean_inc(v_currMacroScope_169_);
lean_inc(v_quotContext_168_);
lean_inc(v_maxHeartbeats_167_);
lean_inc(v_initHeartbeats_166_);
lean_inc(v_openDecls_165_);
lean_inc(v_currNamespace_164_);
lean_inc_ref(v_fileMap_162_);
lean_inc_ref(v_fileName_161_);
v_fileName_180_ = v_fileName_161_;
v_fileMap_181_ = v_fileMap_162_;
v_currNamespace_182_ = v_currNamespace_164_;
v_openDecls_183_ = v_openDecls_165_;
v_initHeartbeats_184_ = v_initHeartbeats_166_;
v_maxHeartbeats_185_ = v_maxHeartbeats_167_;
v_quotContext_186_ = v_quotContext_168_;
v_currMacroScope_187_ = v_currMacroScope_169_;
v_cancelTk_x3f_188_ = v_cancelTk_x3f_170_;
v_inheritedTraceOptions_189_ = v_inheritedTraceOptions_171_;
v_currRecDepth_190_ = v_currRecDepth_158_;
v_ref_191_ = v_ref_159_;
v_suppressElabErrors_192_ = v_suppressElabErrors_160_;
v___y_193_ = v_a_148_;
goto v___jp_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object* v_mvarId_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(lean_object* v_mvarId_241_, lean_object* v_x_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_241_, v_x_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_a_257_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_248_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_248_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg___boxed(lean_object* v_mvarId_265_, lean_object* v_x_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_265_, v_x_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(lean_object* v_00_u03b1_273_, lean_object* v_mvarId_274_, lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_274_, v_x_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___boxed(lean_object* v_00_u03b1_282_, lean_object* v_mvarId_283_, lean_object* v_x_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(v_00_u03b1_282_, v_mvarId_283_, v_x_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_290_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t v___x_291_, lean_object* v_x_292_){
_start:
{
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object* v___x_293_, lean_object* v_x_294_){
_start:
{
uint8_t v___x_991__boxed_295_; uint8_t v_res_296_; lean_object* v_r_297_; 
v___x_991__boxed_295_ = lean_unbox(v___x_293_);
v_res_296_ = l_Lean_Elab_Eqns_deltaLHS___lam__0(v___x_991__boxed_295_, v_x_294_);
lean_dec(v_x_294_);
v_r_297_ = lean_box(v_res_296_);
return v_r_297_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_307_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__5));
v___x_308_ = l_Lean_MessageData_ofFormat(v___x_307_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_309_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__6);
v___x_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__9));
v___x_315_ = l_Lean_MessageData_ofFormat(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__10);
v___x_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object* v_mvarId_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v___x_324_; 
lean_inc(v_mvarId_318_);
v___x_324_ = l_Lean_MVarId_getType_x27(v_mvarId_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
if (lean_obj_tag(v___x_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc(v_a_325_);
lean_dec_ref_known(v___x_324_, 1);
v___x_326_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_327_ = lean_unsigned_to_nat(3u);
v___x_328_ = l_Lean_Expr_isAppOfArity(v_a_325_, v___x_326_, v___x_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_a_325_);
v___x_329_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_330_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__7);
v___x_331_ = l_Lean_Meta_throwTacticEx___redArg(v___x_329_, v_mvarId_318_, v___x_330_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; lean_object* v___f_333_; lean_object* v___x_334_; lean_object* v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; 
v___x_332_ = lean_box(v___x_328_);
v___f_333_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed), 2, 1);
lean_closure_set(v___f_333_, 0, v___x_332_);
v___x_334_ = l_Lean_Expr_appFn_x21(v_a_325_);
v___x_335_ = l_Lean_Expr_appArg_x21(v___x_334_);
lean_dec_ref(v___x_334_);
v___x_336_ = 0;
v___x_337_ = l_Lean_Meta_delta_x3f(v___x_335_, v___f_333_, v___x_336_, v___y_321_, v___y_322_);
if (lean_obj_tag(v___x_337_) == 0)
{
lean_object* v_a_338_; 
v_a_338_ = lean_ctor_get(v___x_337_, 0);
lean_inc(v_a_338_);
lean_dec_ref_known(v___x_337_, 1);
if (lean_obj_tag(v_a_338_) == 1)
{
lean_object* v_val_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_val_339_ = lean_ctor_get(v_a_338_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v_a_338_, 1);
v___x_340_ = l_Lean_Expr_appArg_x21(v_a_325_);
lean_dec(v_a_325_);
v___x_341_ = l_Lean_Meta_mkEq(v_val_339_, v___x_340_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
if (lean_obj_tag(v___x_341_) == 0)
{
lean_object* v_a_342_; lean_object* v___x_343_; 
v_a_342_ = lean_ctor_get(v___x_341_, 0);
lean_inc(v_a_342_);
lean_dec_ref_known(v___x_341_, 1);
v___x_343_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_318_, v_a_342_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
return v___x_343_;
}
else
{
lean_object* v_a_344_; lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_351_; 
lean_dec(v_mvarId_318_);
v_a_344_ = lean_ctor_get(v___x_341_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_351_ == 0)
{
v___x_346_ = v___x_341_;
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
else
{
lean_inc(v_a_344_);
lean_dec(v___x_341_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_351_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v___x_349_; 
if (v_isShared_347_ == 0)
{
v___x_349_ = v___x_346_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_a_344_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_dec(v_a_338_);
lean_dec(v_a_325_);
v___x_352_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__3));
v___x_353_ = lean_obj_once(&l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11, &l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11_once, _init_l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__11);
v___x_354_ = l_Lean_Meta_throwTacticEx___redArg(v___x_352_, v_mvarId_318_, v___x_353_, v___y_319_, v___y_320_, v___y_321_, v___y_322_);
return v___x_354_;
}
}
else
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_362_; 
lean_dec(v_a_325_);
lean_dec(v_mvarId_318_);
v_a_355_ = lean_ctor_get(v___x_337_, 0);
v_isSharedCheck_362_ = !lean_is_exclusive(v___x_337_);
if (v_isSharedCheck_362_ == 0)
{
v___x_357_ = v___x_337_;
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_337_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_362_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_360_; 
if (v_isShared_358_ == 0)
{
v___x_360_ = v___x_357_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_a_355_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
return v___x_360_;
}
}
}
}
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
lean_dec(v_mvarId_318_);
v_a_363_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_324_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_324_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(lean_object* v_mvarId_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Elab_Eqns_deltaLHS___lam__1(v_mvarId_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object* v_mvarId_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___f_384_; lean_object* v___x_385_; 
lean_inc(v_mvarId_378_);
v___f_384_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed), 6, 1);
lean_closure_set(v___f_384_, 0, v_mvarId_378_);
v___x_385_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_378_, v___f_384_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object* v_mvarId_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Elab_Eqns_deltaLHS(v_mvarId_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object* v_mvarId_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = ((lean_object*)(l_Lean_Elab_Eqns_tryContradiction___closed__0));
v___x_403_ = l_Lean_MVarId_contradictionCore(v_mvarId_396_, v___x_402_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object* v_mvarId_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(lean_object* v_msg_411_){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = l_Lean_instInhabitedExpr;
v___x_413_ = lean_panic_fn_borrowed(v___x_412_, v_msg_411_);
return v___x_413_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0(void){
_start:
{
lean_object* v___x_414_; lean_object* v_dummy_415_; 
v___x_414_ = lean_box(0);
v_dummy_415_ = l_Lean_Expr_sort___override(v___x_414_);
return v_dummy_415_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_419_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__3));
v___x_420_ = lean_unsigned_to_nat(18u);
v___x_421_ = lean_unsigned_to_nat(1896u);
v___x_422_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__2));
v___x_423_ = ((lean_object*)(l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__1));
v___x_424_ = l_mkPanicMessageWithDecl(v___x_423_, v___x_422_, v___x_421_, v___x_420_, v___x_419_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(lean_object* v_e_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Lean_Meta_whnfR(v_e_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
if (lean_obj_tag(v___x_431_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_433_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_a_432_);
v___x_433_ = l_Lean_Expr_getAppFn(v_a_432_);
if (lean_obj_tag(v___x_433_) == 11)
{
lean_object* v_struct_434_; lean_object* v___x_435_; 
lean_dec_ref_known(v___x_431_, 1);
v_struct_434_ = lean_ctor_get(v___x_433_, 2);
lean_inc_ref(v_struct_434_);
v___x_435_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_struct_434_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
if (lean_obj_tag(v___x_435_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_461_; 
v_a_436_ = lean_ctor_get(v___x_435_, 0);
v_isSharedCheck_461_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_461_ == 0)
{
v___x_438_ = v___x_435_;
v_isShared_439_ = v_isSharedCheck_461_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_461_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___y_441_; 
if (lean_obj_tag(v___x_433_) == 11)
{
lean_object* v_typeName_452_; lean_object* v_idx_453_; lean_object* v_struct_454_; size_t v___x_455_; size_t v___x_456_; uint8_t v___x_457_; 
v_typeName_452_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_typeName_452_);
v_idx_453_ = lean_ctor_get(v___x_433_, 1);
lean_inc(v_idx_453_);
v_struct_454_ = lean_ctor_get(v___x_433_, 2);
lean_inc_ref(v_struct_454_);
v___x_455_ = lean_ptr_addr(v_struct_454_);
lean_dec_ref(v_struct_454_);
v___x_456_ = lean_ptr_addr(v_a_436_);
v___x_457_ = lean_usize_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; 
lean_dec_ref_known(v___x_433_, 3);
v___x_458_ = l_Lean_Expr_proj___override(v_typeName_452_, v_idx_453_, v_a_436_);
v___y_441_ = v___x_458_;
goto v___jp_440_;
}
else
{
lean_dec(v_idx_453_);
lean_dec(v_typeName_452_);
lean_dec(v_a_436_);
v___y_441_ = v___x_433_;
goto v___jp_440_;
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; 
lean_dec(v_a_436_);
lean_dec_ref_known(v___x_433_, 3);
v___x_459_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__4);
v___x_460_ = l_panic___at___00__private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux_spec__0(v___x_459_);
v___y_441_ = v___x_460_;
goto v___jp_440_;
}
v___jp_440_:
{
lean_object* v_dummy_442_; lean_object* v_nargs_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v_dummy_442_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0);
v_nargs_443_ = l_Lean_Expr_getAppNumArgs(v_a_432_);
lean_inc(v_nargs_443_);
v___x_444_ = lean_mk_array(v_nargs_443_, v_dummy_442_);
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_sub(v_nargs_443_, v___x_445_);
lean_dec(v_nargs_443_);
v___x_447_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_432_, v___x_444_, v___x_446_);
v___x_448_ = l_Lean_mkAppN(v___y_441_, v___x_447_);
lean_dec_ref(v___x_447_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 0, v___x_448_);
v___x_450_ = v___x_438_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_433_, 3);
lean_dec(v_a_432_);
return v___x_435_;
}
}
else
{
lean_dec_ref(v___x_433_);
lean_dec(v_a_432_);
return v___x_431_;
}
}
else
{
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object* v_e_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_e_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
lean_dec(v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec_ref(v_a_463_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object* v_mvarId_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v___x_475_; 
lean_inc(v_mvarId_469_);
v___x_475_ = l_Lean_MVarId_getType_x27(v_mvarId_469_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_537_; 
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_537_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_537_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_537_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_480_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_481_ = lean_unsigned_to_nat(3u);
v___x_482_ = l_Lean_Expr_isAppOfArity(v_a_476_, v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_dec(v_a_476_);
lean_dec(v_mvarId_469_);
v___x_483_ = lean_box(0);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_483_);
v___x_485_ = v___x_478_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
v___x_485_ = v_reuseFailAlloc_486_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
return v___x_485_;
}
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
lean_del_object(v___x_478_);
v___x_487_ = l_Lean_Expr_appFn_x21(v_a_476_);
v___x_488_ = l_Lean_Expr_appArg_x21(v___x_487_);
lean_dec_ref(v___x_487_);
lean_inc_ref(v___x_488_);
v___x_489_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v___x_488_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_528_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_528_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_528_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_528_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
uint8_t v___x_494_; 
v___x_494_ = lean_expr_eqv(v_a_490_, v___x_488_);
lean_dec_ref(v___x_488_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_del_object(v___x_492_);
v___x_495_ = l_Lean_Expr_appArg_x21(v_a_476_);
lean_dec(v_a_476_);
v___x_496_ = l_Lean_Meta_mkEq(v_a_490_, v___x_495_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_469_, v_a_497_, v___y_470_, v___y_471_, v___y_472_, v___y_473_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_507_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_507_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_507_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v_a_499_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_503_);
v___x_505_ = v___x_501_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_a_508_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_498_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_a_508_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec(v_mvarId_469_);
v_a_516_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_496_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_496_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec(v_a_490_);
lean_dec(v_a_476_);
lean_dec(v_mvarId_469_);
v___x_524_ = lean_box(0);
if (v_isShared_493_ == 0)
{
lean_ctor_set(v___x_492_, 0, v___x_524_);
v___x_526_ = v___x_492_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
else
{
lean_object* v_a_529_; lean_object* v___x_531_; uint8_t v_isShared_532_; uint8_t v_isSharedCheck_536_; 
lean_dec_ref(v___x_488_);
lean_dec(v_a_476_);
lean_dec(v_mvarId_469_);
v_a_529_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_536_ == 0)
{
v___x_531_ = v___x_489_;
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
else
{
lean_inc(v_a_529_);
lean_dec(v___x_489_);
v___x_531_ = lean_box(0);
v_isShared_532_ = v_isSharedCheck_536_;
goto v_resetjp_530_;
}
v_resetjp_530_:
{
lean_object* v___x_534_; 
if (v_isShared_532_ == 0)
{
v___x_534_ = v___x_531_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_529_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
}
}
else
{
lean_object* v_a_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_545_; 
lean_dec(v_mvarId_469_);
v_a_538_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_545_ == 0)
{
v___x_540_ = v___x_475_;
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_a_538_);
lean_dec(v___x_475_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_545_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_543_; 
if (v_isShared_541_ == 0)
{
v___x_543_ = v___x_540_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_544_; 
v_reuseFailAlloc_544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_544_, 0, v_a_538_);
v___x_543_ = v_reuseFailAlloc_544_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
return v___x_543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(lean_object* v_mvarId_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(v_mvarId_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object* v_mvarId_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___f_559_; lean_object* v___x_560_; 
lean_inc(v_mvarId_553_);
v___f_559_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_559_, 0, v_mvarId_553_);
v___x_560_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_553_, v___f_559_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object* v_mvarId_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec(v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec_ref(v_a_562_);
return v_res_567_;
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
