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
static lean_once_cell_t l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0;
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0(lean_object* v_opts_77_, lean_object* v_opt_78_){
_start:
{
lean_object* v_name_79_; lean_object* v_defValue_80_; lean_object* v_map_81_; lean_object* v___x_82_; 
v_name_79_ = lean_ctor_get(v_opt_78_, 0);
v_defValue_80_ = lean_ctor_get(v_opt_78_, 1);
v_map_81_ = lean_ctor_get(v_opts_77_, 0);
v___x_82_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_81_, v_name_79_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_inc(v_defValue_80_);
return v_defValue_80_;
}
else
{
lean_object* v_val_83_; 
v_val_83_ = lean_ctor_get(v___x_82_, 0);
lean_inc(v_val_83_);
lean_dec_ref_known(v___x_82_, 1);
if (lean_obj_tag(v_val_83_) == 3)
{
lean_object* v_v_84_; 
v_v_84_ = lean_ctor_get(v_val_83_, 0);
lean_inc(v_v_84_);
lean_dec_ref_known(v_val_83_, 1);
return v_v_84_;
}
else
{
lean_dec(v_val_83_);
lean_inc(v_defValue_80_);
return v_defValue_80_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0___boxed(lean_object* v_opts_85_, lean_object* v_opt_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0(v_opts_85_, v_opt_86_);
lean_dec_ref(v_opt_86_);
lean_dec_ref(v_opts_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(lean_object* v_o_91_, lean_object* v_k_92_, uint8_t v_v_93_){
_start:
{
lean_object* v_map_94_; uint8_t v_hasTrace_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_109_; 
v_map_94_ = lean_ctor_get(v_o_91_, 0);
v_hasTrace_95_ = lean_ctor_get_uint8(v_o_91_, sizeof(void*)*1);
v_isSharedCheck_109_ = !lean_is_exclusive(v_o_91_);
if (v_isSharedCheck_109_ == 0)
{
v___x_97_ = v_o_91_;
v_isShared_98_ = v_isSharedCheck_109_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_map_94_);
lean_dec(v_o_91_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_109_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_99_ = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(v___x_99_, 0, v_v_93_);
lean_inc(v_k_92_);
v___x_100_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_92_, v___x_99_, v_map_94_);
if (v_hasTrace_95_ == 0)
{
lean_object* v___x_101_; uint8_t v___x_102_; lean_object* v___x_104_; 
v___x_101_ = ((lean_object*)(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___closed__1));
v___x_102_ = l_Lean_Name_isPrefixOf(v___x_101_, v_k_92_);
lean_dec(v_k_92_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_100_);
v___x_104_ = v___x_97_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_100_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1, v___x_102_);
return v___x_104_;
}
}
else
{
lean_object* v___x_107_; 
lean_dec(v_k_92_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_100_);
v___x_107_ = v___x_97_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_100_);
lean_ctor_set_uint8(v_reuseFailAlloc_108_, sizeof(void*)*1, v_hasTrace_95_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1___boxed(lean_object* v_o_110_, lean_object* v_k_111_, lean_object* v_v_112_){
_start:
{
uint8_t v_v_boxed_113_; lean_object* v_res_114_; 
v_v_boxed_113_ = lean_unbox(v_v_112_);
v_res_114_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(v_o_110_, v_k_111_, v_v_boxed_113_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1(lean_object* v_opts_115_, lean_object* v_opt_116_, uint8_t v_val_117_){
_start:
{
lean_object* v_name_118_; lean_object* v___x_119_; 
v_name_118_ = lean_ctor_get(v_opt_116_, 0);
lean_inc(v_name_118_);
lean_dec_ref(v_opt_116_);
v___x_119_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1_spec__1(v_opts_115_, v_name_118_, v_val_117_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1___boxed(lean_object* v_opts_120_, lean_object* v_opt_121_, lean_object* v_val_122_){
_start:
{
uint8_t v_val_boxed_123_; lean_object* v_res_124_; 
v_val_boxed_123_ = lean_unbox(v_val_122_);
v_res_124_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_opts_120_, v_opt_121_, v_val_boxed_123_);
return v_res_124_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__0(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__1(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__0, &l_Lean_Elab_Eqns_tryURefl___closed__0_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__0);
v___x_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Elab_Eqns_tryURefl___closed__2(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__1, &l_Lean_Elab_Eqns_tryURefl___closed__1_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__1);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object* v_mvarId_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_toCold_136_; lean_object* v_currRecDepth_137_; lean_object* v_ref_138_; uint8_t v_suppressElabErrors_139_; uint8_t v_isRecordingDeps_140_; lean_object* v_fileName_141_; lean_object* v_fileMap_142_; lean_object* v_options_143_; lean_object* v_currNamespace_144_; lean_object* v_openDecls_145_; lean_object* v_initHeartbeats_146_; lean_object* v_maxHeartbeats_147_; lean_object* v_quotContext_148_; lean_object* v_currMacroScope_149_; lean_object* v_cancelTk_x3f_150_; lean_object* v_inheritedTraceOptions_151_; uint8_t v___x_152_; uint16_t v___y_154_; lean_object* v___y_155_; lean_object* v_fileName_156_; lean_object* v_fileMap_157_; lean_object* v_currNamespace_158_; lean_object* v_openDecls_159_; lean_object* v_initHeartbeats_160_; lean_object* v_maxHeartbeats_161_; lean_object* v_quotContext_162_; lean_object* v_currMacroScope_163_; lean_object* v_cancelTk_x3f_164_; lean_object* v_inheritedTraceOptions_165_; lean_object* v_currRecDepth_166_; lean_object* v_ref_167_; uint8_t v_suppressElabErrors_168_; uint8_t v_isRecordingDeps_169_; lean_object* v___y_170_; uint8_t v___y_203_; uint16_t v___y_204_; lean_object* v___y_205_; lean_object* v___y_228_; 
v_toCold_136_ = lean_ctor_get(v_a_133_, 0);
v_currRecDepth_137_ = lean_ctor_get(v_a_133_, 1);
v_ref_138_ = lean_ctor_get(v_a_133_, 2);
v_suppressElabErrors_139_ = lean_ctor_get_uint8(v_a_133_, sizeof(void*)*3 + 2);
v_isRecordingDeps_140_ = lean_ctor_get_uint8(v_a_133_, sizeof(void*)*3 + 3);
v_fileName_141_ = lean_ctor_get(v_toCold_136_, 0);
v_fileMap_142_ = lean_ctor_get(v_toCold_136_, 1);
v_options_143_ = lean_ctor_get(v_toCold_136_, 2);
v_currNamespace_144_ = lean_ctor_get(v_toCold_136_, 4);
v_openDecls_145_ = lean_ctor_get(v_toCold_136_, 5);
v_initHeartbeats_146_ = lean_ctor_get(v_toCold_136_, 6);
v_maxHeartbeats_147_ = lean_ctor_get(v_toCold_136_, 7);
v_quotContext_148_ = lean_ctor_get(v_toCold_136_, 8);
v_currMacroScope_149_ = lean_ctor_get(v_toCold_136_, 9);
v_cancelTk_x3f_150_ = lean_ctor_get(v_toCold_136_, 10);
v_inheritedTraceOptions_151_ = lean_ctor_get(v_toCold_136_, 11);
v___x_152_ = 1;
if (v_isRecordingDeps_140_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = l_Lean_Meta_smartUnfolding;
lean_inc_ref(v_options_143_);
v___x_239_ = l_Lean_Option_set___at___00Lean_Elab_Eqns_tryURefl_spec__1(v_options_143_, v___x_238_, v_isRecordingDeps_140_);
v___y_228_ = v___x_239_;
goto v___jp_227_;
}
else
{
lean_object* v___x_240_; 
lean_inc_ref(v_options_143_);
v___x_240_ = l_Lean_Core_instMonadWithOptionsCoreM_reportViolation(v_options_143_);
v___y_228_ = v___x_240_;
goto v___jp_227_;
}
v___jp_153_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_171_ = l_Lean_maxRecDepth;
v___x_172_ = l_Lean_Option_get___at___00Lean_Elab_Eqns_tryURefl_spec__0(v___y_155_, v___x_171_);
v___x_173_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_173_, 0, v_fileName_156_);
lean_ctor_set(v___x_173_, 1, v_fileMap_157_);
lean_ctor_set(v___x_173_, 2, v___y_155_);
lean_ctor_set(v___x_173_, 3, v___x_172_);
lean_ctor_set(v___x_173_, 4, v_currNamespace_158_);
lean_ctor_set(v___x_173_, 5, v_openDecls_159_);
lean_ctor_set(v___x_173_, 6, v_initHeartbeats_160_);
lean_ctor_set(v___x_173_, 7, v_maxHeartbeats_161_);
lean_ctor_set(v___x_173_, 8, v_quotContext_162_);
lean_ctor_set(v___x_173_, 9, v_currMacroScope_163_);
lean_ctor_set(v___x_173_, 10, v_cancelTk_x3f_164_);
lean_ctor_set(v___x_173_, 11, v_inheritedTraceOptions_165_);
lean_inc(v_ref_167_);
lean_inc(v_currRecDepth_166_);
v___x_174_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_currRecDepth_166_);
lean_ctor_set(v___x_174_, 2, v_ref_167_);
lean_ctor_set_uint16(v___x_174_, sizeof(void*)*3, v___y_154_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*3 + 2, v_suppressElabErrors_168_);
lean_ctor_set_uint8(v___x_174_, sizeof(void*)*3 + 3, v_isRecordingDeps_169_);
v___x_175_ = l_Lean_MVarId_refl(v_mvarId_130_, v___x_152_, v_a_131_, v_a_132_, v___x_174_, v___y_170_);
lean_dec_ref_known(v___x_174_, 3);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_183_; 
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_175_, 0);
lean_dec(v_unused_184_);
v___x_177_ = v___x_175_;
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
else
{
lean_dec(v___x_175_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_183_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_box(v___x_152_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_179_);
v___x_181_ = v___x_177_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_201_; 
v_a_185_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_201_ == 0)
{
v___x_187_ = v___x_175_;
v_isShared_188_ = v_isSharedCheck_201_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_175_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_201_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
uint8_t v___x_189_; 
v___x_189_ = l_Lean_Exception_isInterrupt(v_a_185_);
if (v___x_189_ == 0)
{
uint8_t v___x_190_; 
lean_inc(v_a_185_);
v___x_190_ = l_Lean_Exception_isRuntime(v_a_185_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_193_; 
lean_dec(v_a_185_);
v___x_191_ = lean_box(v___x_190_);
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 0);
lean_ctor_set(v___x_187_, 0, v___x_191_);
v___x_193_ = v___x_187_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
else
{
lean_object* v___x_196_; 
if (v_isShared_188_ == 0)
{
v___x_196_ = v___x_187_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_185_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
else
{
lean_object* v___x_199_; 
if (v_isShared_188_ == 0)
{
v___x_199_ = v___x_187_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_185_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
}
v___jp_202_:
{
lean_object* v___x_206_; lean_object* v_env_207_; lean_object* v_nextMacroScope_208_; lean_object* v_ngen_209_; lean_object* v_auxDeclNGen_210_; lean_object* v_traceState_211_; lean_object* v_recordedDeps_212_; lean_object* v_messages_213_; lean_object* v_infoState_214_; lean_object* v_snapshotTasks_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_225_; 
v___x_206_ = lean_st_ref_take(v_a_134_);
v_env_207_ = lean_ctor_get(v___x_206_, 0);
v_nextMacroScope_208_ = lean_ctor_get(v___x_206_, 1);
v_ngen_209_ = lean_ctor_get(v___x_206_, 2);
v_auxDeclNGen_210_ = lean_ctor_get(v___x_206_, 3);
v_traceState_211_ = lean_ctor_get(v___x_206_, 4);
v_recordedDeps_212_ = lean_ctor_get(v___x_206_, 6);
v_messages_213_ = lean_ctor_get(v___x_206_, 7);
v_infoState_214_ = lean_ctor_get(v___x_206_, 8);
v_snapshotTasks_215_ = lean_ctor_get(v___x_206_, 9);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_225_ == 0)
{
lean_object* v_unused_226_; 
v_unused_226_ = lean_ctor_get(v___x_206_, 5);
lean_dec(v_unused_226_);
v___x_217_ = v___x_206_;
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_snapshotTasks_215_);
lean_inc(v_infoState_214_);
lean_inc(v_messages_213_);
lean_inc(v_recordedDeps_212_);
lean_inc(v_traceState_211_);
lean_inc(v_auxDeclNGen_210_);
lean_inc(v_ngen_209_);
lean_inc(v_nextMacroScope_208_);
lean_inc(v_env_207_);
lean_dec(v___x_206_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_225_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_222_; 
v___x_219_ = l_Lean_Kernel_enableDiag(v_env_207_, v___y_203_);
v___x_220_ = lean_obj_once(&l_Lean_Elab_Eqns_tryURefl___closed__2, &l_Lean_Elab_Eqns_tryURefl___closed__2_once, _init_l_Lean_Elab_Eqns_tryURefl___closed__2);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 5, v___x_220_);
lean_ctor_set(v___x_217_, 0, v___x_219_);
v___x_222_ = v___x_217_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v___x_219_);
lean_ctor_set(v_reuseFailAlloc_224_, 1, v_nextMacroScope_208_);
lean_ctor_set(v_reuseFailAlloc_224_, 2, v_ngen_209_);
lean_ctor_set(v_reuseFailAlloc_224_, 3, v_auxDeclNGen_210_);
lean_ctor_set(v_reuseFailAlloc_224_, 4, v_traceState_211_);
lean_ctor_set(v_reuseFailAlloc_224_, 5, v___x_220_);
lean_ctor_set(v_reuseFailAlloc_224_, 6, v_recordedDeps_212_);
lean_ctor_set(v_reuseFailAlloc_224_, 7, v_messages_213_);
lean_ctor_set(v_reuseFailAlloc_224_, 8, v_infoState_214_);
lean_ctor_set(v_reuseFailAlloc_224_, 9, v_snapshotTasks_215_);
v___x_222_ = v_reuseFailAlloc_224_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
lean_object* v___x_223_; 
v___x_223_ = lean_st_ref_put(v_a_134_, v___x_222_);
lean_inc_ref(v_inheritedTraceOptions_151_);
lean_inc(v_cancelTk_x3f_150_);
lean_inc(v_currMacroScope_149_);
lean_inc(v_quotContext_148_);
lean_inc(v_maxHeartbeats_147_);
lean_inc(v_initHeartbeats_146_);
lean_inc(v_openDecls_145_);
lean_inc(v_currNamespace_144_);
lean_inc_ref(v_fileMap_142_);
lean_inc_ref(v_fileName_141_);
v___y_154_ = v___y_204_;
v___y_155_ = v___y_205_;
v_fileName_156_ = v_fileName_141_;
v_fileMap_157_ = v_fileMap_142_;
v_currNamespace_158_ = v_currNamespace_144_;
v_openDecls_159_ = v_openDecls_145_;
v_initHeartbeats_160_ = v_initHeartbeats_146_;
v_maxHeartbeats_161_ = v_maxHeartbeats_147_;
v_quotContext_162_ = v_quotContext_148_;
v_currMacroScope_163_ = v_currMacroScope_149_;
v_cancelTk_x3f_164_ = v_cancelTk_x3f_150_;
v_inheritedTraceOptions_165_ = v_inheritedTraceOptions_151_;
v_currRecDepth_166_ = v_currRecDepth_137_;
v_ref_167_ = v_ref_138_;
v_suppressElabErrors_168_ = v_suppressElabErrors_139_;
v_isRecordingDeps_169_ = v_isRecordingDeps_140_;
v___y_170_ = v_a_134_;
goto v___jp_153_;
}
}
}
v___jp_227_:
{
uint16_t v___x_229_; lean_object* v___x_230_; lean_object* v_env_231_; uint8_t v___x_232_; uint16_t v___x_233_; uint16_t v___x_234_; uint16_t v___x_235_; uint8_t v___x_236_; 
v___x_229_ = l_Lean_OptionFlags_ofOptions(v___y_228_);
v___x_230_ = lean_st_ref_get(v_a_134_);
v_env_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc_ref(v_env_231_);
lean_dec(v___x_230_);
v___x_232_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_231_);
lean_dec_ref(v_env_231_);
v___x_233_ = 512;
v___x_234_ = lean_uint16_land(v___x_229_, v___x_233_);
v___x_235_ = 0;
v___x_236_ = lean_uint16_dec_eq(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
if (v___x_232_ == 0)
{
v___y_203_ = v___x_152_;
v___y_204_ = v___x_229_;
v___y_205_ = v___y_228_;
goto v___jp_202_;
}
else
{
lean_inc_ref(v_inheritedTraceOptions_151_);
lean_inc(v_cancelTk_x3f_150_);
lean_inc(v_currMacroScope_149_);
lean_inc(v_quotContext_148_);
lean_inc(v_maxHeartbeats_147_);
lean_inc(v_initHeartbeats_146_);
lean_inc(v_openDecls_145_);
lean_inc(v_currNamespace_144_);
lean_inc_ref(v_fileMap_142_);
lean_inc_ref(v_fileName_141_);
v___y_154_ = v___x_229_;
v___y_155_ = v___y_228_;
v_fileName_156_ = v_fileName_141_;
v_fileMap_157_ = v_fileMap_142_;
v_currNamespace_158_ = v_currNamespace_144_;
v_openDecls_159_ = v_openDecls_145_;
v_initHeartbeats_160_ = v_initHeartbeats_146_;
v_maxHeartbeats_161_ = v_maxHeartbeats_147_;
v_quotContext_162_ = v_quotContext_148_;
v_currMacroScope_163_ = v_currMacroScope_149_;
v_cancelTk_x3f_164_ = v_cancelTk_x3f_150_;
v_inheritedTraceOptions_165_ = v_inheritedTraceOptions_151_;
v_currRecDepth_166_ = v_currRecDepth_137_;
v_ref_167_ = v_ref_138_;
v_suppressElabErrors_168_ = v_suppressElabErrors_139_;
v_isRecordingDeps_169_ = v_isRecordingDeps_140_;
v___y_170_ = v_a_134_;
goto v___jp_153_;
}
}
else
{
if (v___x_232_ == 0)
{
lean_inc_ref(v_inheritedTraceOptions_151_);
lean_inc(v_cancelTk_x3f_150_);
lean_inc(v_currMacroScope_149_);
lean_inc(v_quotContext_148_);
lean_inc(v_maxHeartbeats_147_);
lean_inc(v_initHeartbeats_146_);
lean_inc(v_openDecls_145_);
lean_inc(v_currNamespace_144_);
lean_inc_ref(v_fileMap_142_);
lean_inc_ref(v_fileName_141_);
v___y_154_ = v___x_229_;
v___y_155_ = v___y_228_;
v_fileName_156_ = v_fileName_141_;
v_fileMap_157_ = v_fileMap_142_;
v_currNamespace_158_ = v_currNamespace_144_;
v_openDecls_159_ = v_openDecls_145_;
v_initHeartbeats_160_ = v_initHeartbeats_146_;
v_maxHeartbeats_161_ = v_maxHeartbeats_147_;
v_quotContext_162_ = v_quotContext_148_;
v_currMacroScope_163_ = v_currMacroScope_149_;
v_cancelTk_x3f_164_ = v_cancelTk_x3f_150_;
v_inheritedTraceOptions_165_ = v_inheritedTraceOptions_151_;
v_currRecDepth_166_ = v_currRecDepth_137_;
v_ref_167_ = v_ref_138_;
v_suppressElabErrors_168_ = v_suppressElabErrors_139_;
v_isRecordingDeps_169_ = v_isRecordingDeps_140_;
v___y_170_ = v_a_134_;
goto v___jp_153_;
}
else
{
uint8_t v___x_237_; 
v___x_237_ = 0;
v___y_203_ = v___x_237_;
v___y_204_ = v___x_229_;
v___y_205_ = v___y_228_;
goto v___jp_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryURefl___boxed(lean_object* v_mvarId_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Elab_Eqns_tryURefl(v_mvarId_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(lean_object* v_mvarId_248_, lean_object* v_x_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_248_, v_x_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
v_a_256_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_255_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
v_a_264_ = lean_ctor_get(v___x_255_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_255_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_255_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg___boxed(lean_object* v_mvarId_272_, lean_object* v_x_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_272_, v_x_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
lean_dec(v___y_277_);
lean_dec_ref(v___y_276_);
lean_dec(v___y_275_);
lean_dec_ref(v___y_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(lean_object* v_00_u03b1_280_, lean_object* v_mvarId_281_, lean_object* v_x_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_281_, v_x_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___boxed(lean_object* v_00_u03b1_289_, lean_object* v_mvarId_290_, lean_object* v_x_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0(v_00_u03b1_289_, v_mvarId_290_, v_x_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v___y_293_);
lean_dec_ref(v___y_292_);
return v_res_297_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Eqns_deltaLHS___lam__0(uint8_t v___x_298_, lean_object* v_x_299_){
_start:
{
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__0___boxed(lean_object* v___x_300_, lean_object* v_x_301_){
_start:
{
uint8_t v___x_993__boxed_302_; uint8_t v_res_303_; lean_object* v_r_304_; 
v___x_993__boxed_302_ = lean_unbox(v___x_300_);
v_res_303_ = l_Lean_Elab_Eqns_deltaLHS___lam__0(v___x_993__boxed_302_, v_x_301_);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1(lean_object* v_mvarId_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed(lean_object* v_mvarId_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Elab_Eqns_deltaLHS___lam__1(v_mvarId_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec(v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec_ref(v___y_379_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object* v_mvarId_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_){
_start:
{
lean_object* v___f_391_; lean_object* v___x_392_; 
lean_inc(v_mvarId_385_);
v___f_391_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___boxed), 6, 1);
lean_closure_set(v___f_391_, 0, v_mvarId_385_);
v___x_392_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_385_, v___f_391_, v_a_386_, v_a_387_, v_a_388_, v_a_389_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_deltaLHS___boxed(lean_object* v_mvarId_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Elab_Eqns_deltaLHS(v_mvarId_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object* v_mvarId_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_409_ = ((lean_object*)(l_Lean_Elab_Eqns_tryContradiction___closed__0));
v___x_410_ = l_Lean_MVarId_contradictionCore(v_mvarId_403_, v___x_409_, v_a_404_, v_a_405_, v_a_406_, v_a_407_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_tryContradiction___boxed(lean_object* v_mvarId_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Elab_Eqns_tryContradiction(v_mvarId_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_417_;
}
}
static lean_object* _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0(void){
_start:
{
lean_object* v___x_418_; lean_object* v_dummy_419_; 
v___x_418_ = lean_box(0);
v_dummy_419_ = l_Lean_Expr_sort___override(v___x_418_);
return v_dummy_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(lean_object* v_e_420_, lean_object* v_a_421_, lean_object* v_a_422_, lean_object* v_a_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = l_Lean_Meta_whnfR(v_e_420_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_426_) == 0)
{
lean_object* v_a_427_; lean_object* v___x_428_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
v___x_428_ = l_Lean_Expr_getAppFn(v_a_427_);
if (lean_obj_tag(v___x_428_) == 11)
{
lean_object* v_typeName_429_; lean_object* v_idx_430_; lean_object* v_struct_431_; lean_object* v___x_432_; 
lean_inc(v_a_427_);
lean_dec_ref_known(v___x_426_, 1);
v_typeName_429_ = lean_ctor_get(v___x_428_, 0);
v_idx_430_ = lean_ctor_get(v___x_428_, 1);
v_struct_431_ = lean_ctor_get(v___x_428_, 2);
lean_inc_ref(v_struct_431_);
v___x_432_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_struct_431_, v_a_421_, v_a_422_, v_a_423_, v_a_424_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_453_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_453_ == 0)
{
v___x_435_ = v___x_432_;
v_isShared_436_ = v_isSharedCheck_453_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_a_433_);
lean_dec(v___x_432_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_453_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___y_438_; size_t v___x_449_; size_t v___x_450_; uint8_t v___x_451_; 
v___x_449_ = lean_ptr_addr(v_struct_431_);
v___x_450_ = lean_ptr_addr(v_a_433_);
v___x_451_ = lean_usize_dec_eq(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_inc(v_idx_430_);
lean_inc(v_typeName_429_);
lean_dec_ref_known(v___x_428_, 3);
v___x_452_ = l_Lean_Expr_proj___override(v_typeName_429_, v_idx_430_, v_a_433_);
v___y_438_ = v___x_452_;
goto v___jp_437_;
}
else
{
lean_dec(v_a_433_);
v___y_438_ = v___x_428_;
goto v___jp_437_;
}
v___jp_437_:
{
lean_object* v_dummy_439_; lean_object* v_nargs_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_447_; 
v_dummy_439_ = lean_obj_once(&l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0, &l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0_once, _init_l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___closed__0);
v_nargs_440_ = l_Lean_Expr_getAppNumArgs(v_a_427_);
lean_inc(v_nargs_440_);
v___x_441_ = lean_mk_array(v_nargs_440_, v_dummy_439_);
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_sub(v_nargs_440_, v___x_442_);
lean_dec(v_nargs_440_);
v___x_444_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_427_, v___x_441_, v___x_443_);
v___x_445_ = l_Lean_mkAppN(v___y_438_, v___x_444_);
lean_dec_ref(v___x_444_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 0, v___x_445_);
v___x_447_ = v___x_435_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v___x_445_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_dec_ref_known(v___x_428_, 3);
lean_dec(v_a_427_);
return v___x_432_;
}
}
else
{
lean_dec_ref(v___x_428_);
return v___x_426_;
}
}
else
{
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux___boxed(lean_object* v_e_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v_e_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_);
lean_dec(v_a_458_);
lean_dec_ref(v_a_457_);
lean_dec(v_a_456_);
lean_dec_ref(v_a_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(lean_object* v_mvarId_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___x_467_; 
lean_inc(v_mvarId_461_);
v___x_467_ = l_Lean_MVarId_getType_x27(v_mvarId_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_467_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_529_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_529_ == 0)
{
v___x_470_ = v___x_467_;
v_isShared_471_ = v_isSharedCheck_529_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_a_468_);
lean_dec(v___x_467_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_529_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_472_ = ((lean_object*)(l_Lean_Elab_Eqns_deltaLHS___lam__1___closed__1));
v___x_473_ = lean_unsigned_to_nat(3u);
v___x_474_ = l_Lean_Expr_isAppOfArity(v_a_468_, v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_477_; 
lean_dec(v_a_468_);
lean_dec(v_mvarId_461_);
v___x_475_ = lean_box(0);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 0, v___x_475_);
v___x_477_ = v___x_470_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
return v___x_477_;
}
}
else
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
lean_del_object(v___x_470_);
v___x_479_ = l_Lean_Expr_appFn_x21(v_a_468_);
v___x_480_ = l_Lean_Expr_appArg_x21(v___x_479_);
lean_dec_ref(v___x_479_);
v___x_481_ = l_Lean_Expr_appArg_x21(v_a_468_);
lean_dec(v_a_468_);
lean_inc_ref(v___x_480_);
v___x_482_ = l___private_Lean_Elab_PreDefinition_EqnsUtils_0__Lean_Elab_Eqns_whnfAux(v___x_480_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_520_; 
v_a_483_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_520_ == 0)
{
v___x_485_ = v___x_482_;
v_isShared_486_ = v_isSharedCheck_520_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_482_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_520_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint8_t v___x_487_; 
v___x_487_ = lean_expr_eqv(v_a_483_, v___x_480_);
lean_dec_ref(v___x_480_);
if (v___x_487_ == 0)
{
lean_object* v___x_488_; 
lean_del_object(v___x_485_);
v___x_488_ = l_Lean_Meta_mkEq(v_a_483_, v___x_481_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v___x_488_, 1);
v___x_490_ = l_Lean_MVarId_replaceTargetDefEq(v_mvarId_461_, v_a_489_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_499_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_499_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_499_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_495_, 0, v_a_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
else
{
lean_object* v_a_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_507_; 
v_a_500_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_507_ == 0)
{
v___x_502_ = v___x_490_;
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_a_500_);
lean_dec(v___x_490_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_507_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v___x_505_; 
if (v_isShared_503_ == 0)
{
v___x_505_ = v___x_502_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_a_500_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
else
{
lean_object* v_a_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
lean_dec(v_mvarId_461_);
v_a_508_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_515_ == 0)
{
v___x_510_ = v___x_488_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_a_508_);
lean_dec(v___x_488_);
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
lean_object* v___x_516_; lean_object* v___x_518_; 
lean_dec(v_a_483_);
lean_dec_ref(v___x_481_);
lean_dec(v_mvarId_461_);
v___x_516_ = lean_box(0);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 0, v___x_516_);
v___x_518_ = v___x_485_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec_ref(v___x_481_);
lean_dec_ref(v___x_480_);
lean_dec(v_mvarId_461_);
v_a_521_ = lean_ctor_get(v___x_482_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_482_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___x_482_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___x_482_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
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
}
}
else
{
lean_object* v_a_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_mvarId_461_);
v_a_530_ = lean_ctor_get(v___x_467_, 0);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_467_);
if (v_isSharedCheck_537_ == 0)
{
v___x_532_ = v___x_467_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_a_530_);
lean_dec(v___x_467_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
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
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed(lean_object* v_mvarId_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0(v_mvarId_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object* v_mvarId_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_){
_start:
{
lean_object* v___f_551_; lean_object* v___x_552_; 
lean_inc(v_mvarId_545_);
v___f_551_ = lean_alloc_closure((void*)(l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_551_, 0, v_mvarId_545_);
v___x_552_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Eqns_deltaLHS_spec__0___redArg(v_mvarId_545_, v___f_551_, v_a_546_, v_a_547_, v_a_548_, v_a_549_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f___boxed(lean_object* v_mvarId_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(v_mvarId_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_);
lean_dec(v_a_557_);
lean_dec_ref(v_a_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
return v_res_559_;
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
