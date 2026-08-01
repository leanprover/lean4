// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.DiscrM
// Imports: public import Lean.Compiler.LCNF.InferType public import Lean.Compiler.LCNF.Simp.Basic
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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_getConstInfoCtorOverride(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(uint8_t, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_eqvTypes(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isCtorOverride_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0___redArg(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__0;
static const lean_array_object l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(lean_object* v_t_1_, lean_object* v_k_2_){
_start:
{
if (lean_obj_tag(v_t_1_) == 0)
{
lean_object* v_k_3_; lean_object* v_v_4_; lean_object* v_l_5_; lean_object* v_r_6_; uint8_t v___x_7_; 
v_k_3_ = lean_ctor_get(v_t_1_, 1);
v_v_4_ = lean_ctor_get(v_t_1_, 2);
v_l_5_ = lean_ctor_get(v_t_1_, 3);
v_r_6_ = lean_ctor_get(v_t_1_, 4);
v___x_7_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2_, v_k_3_);
switch(v___x_7_)
{
case 0:
{
v_t_1_ = v_l_5_;
goto _start;
}
case 1:
{
lean_object* v___x_9_; 
lean_inc(v_v_4_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_v_4_);
return v___x_9_;
}
default: 
{
v_t_1_ = v_r_6_;
goto _start;
}
}
}
else
{
lean_object* v___x_11_; 
v___x_11_ = lean_box(0);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg___boxed(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(v_t_12_, v_k_13_);
lean_dec(v_k_13_);
lean_dec(v_t_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object* v_fvarId_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_, lean_object* v_a_19_){
_start:
{
uint8_t v___x_21_; lean_object* v___x_22_; 
v___x_21_ = 0;
v___x_22_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(v___x_21_, v_fvarId_15_, v_a_17_);
if (lean_obj_tag(v___x_22_) == 0)
{
lean_object* v_a_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_68_; 
v_a_23_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_68_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_68_ == 0)
{
v___x_25_ = v___x_22_;
v_isShared_26_ = v_isSharedCheck_68_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_a_23_);
lean_dec(v___x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_68_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___y_28_; 
if (lean_obj_tag(v_a_23_) == 1)
{
lean_object* v_val_34_; lean_object* v_value_35_; 
v_val_34_ = lean_ctor_get(v_a_23_, 0);
lean_inc(v_val_34_);
lean_dec_ref_known(v_a_23_, 1);
v_value_35_ = lean_ctor_get(v_val_34_, 3);
lean_inc(v_value_35_);
lean_dec(v_val_34_);
if (lean_obj_tag(v_value_35_) == 3)
{
lean_object* v_declName_36_; lean_object* v_args_37_; lean_object* v___x_38_; 
lean_del_object(v___x_25_);
v_declName_36_ = lean_ctor_get(v_value_35_, 0);
lean_inc(v_declName_36_);
v_args_37_ = lean_ctor_get(v_value_35_, 2);
lean_inc_ref(v_args_37_);
lean_dec_ref_known(v_value_35_, 3);
v___x_38_ = l_Lean_Compiler_isCtorOverride_x3f(v_declName_36_, v_a_18_, v_a_19_);
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_59_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_59_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_59_ == 0)
{
v___x_41_ = v___x_38_;
v_isShared_42_ = v_isSharedCheck_59_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_59_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
if (lean_obj_tag(v_a_39_) == 1)
{
lean_object* v_val_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_54_; 
v_val_43_ = lean_ctor_get(v_a_39_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v_a_39_);
if (v_isSharedCheck_54_ == 0)
{
v___x_45_ = v_a_39_;
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_val_43_);
lean_dec(v_a_39_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_54_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_val_43_);
lean_ctor_set(v___x_47_, 1, v_args_37_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_53_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
lean_object* v___x_51_; 
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 0, v___x_49_);
v___x_51_ = v___x_41_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v___x_49_);
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
else
{
lean_object* v___x_55_; lean_object* v___x_57_; 
lean_dec(v_a_39_);
lean_dec_ref(v_args_37_);
v___x_55_ = lean_box(0);
if (v_isShared_42_ == 0)
{
lean_ctor_set(v___x_41_, 0, v___x_55_);
v___x_57_ = v___x_41_;
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
lean_dec_ref(v_args_37_);
v_a_60_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_67_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_67_ == 0)
{
v___x_62_ = v___x_38_;
v_isShared_63_ = v_isSharedCheck_67_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_a_60_);
lean_dec(v___x_38_);
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
else
{
lean_dec(v_value_35_);
v___y_28_ = v_a_16_;
goto v___jp_27_;
}
}
else
{
lean_dec(v_a_23_);
v___y_28_ = v_a_16_;
goto v___jp_27_;
}
v___jp_27_:
{
lean_object* v_discrCtorMap_29_; lean_object* v___x_30_; lean_object* v___x_32_; 
v_discrCtorMap_29_ = lean_ctor_get(v___y_28_, 0);
v___x_30_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(v_discrCtorMap_29_, v_fvarId_15_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v___x_30_);
v___x_32_ = v___x_25_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_33_; 
v_reuseFailAlloc_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_33_, 0, v___x_30_);
v___x_32_ = v_reuseFailAlloc_33_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
return v___x_32_;
}
}
}
}
else
{
lean_object* v_a_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
v_a_69_ = lean_ctor_get(v___x_22_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v___x_22_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v___x_22_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_a_69_);
lean_dec(v___x_22_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_a_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg___boxed(lean_object* v_fvarId_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_fvarId_77_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f(lean_object* v_fvarId_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_84_, v_a_85_, v_a_87_, v_a_88_, v_a_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___boxed(lean_object* v_fvarId_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f(v_fvarId_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
lean_dec(v_a_95_);
lean_dec_ref(v_a_94_);
lean_dec_ref(v_a_93_);
lean_dec(v_fvarId_92_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0(lean_object* v_00_u03b4_100_, lean_object* v_t_101_, lean_object* v_k_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___redArg(v_t_101_, v_k_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0___boxed(lean_object* v_00_u03b4_104_, lean_object* v_t_105_, lean_object* v_k_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_Simp_findCtor_x3f_spec__0(v_00_u03b4_104_, v_t_105_, v_k_106_);
lean_dec(v_k_106_);
lean_dec(v_t_105_);
return v_res_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(lean_object* v_fvarId_108_, lean_object* v_a_109_, lean_object* v_a_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(v_fvarId_108_, v_a_109_, v_a_110_, v_a_111_, v_a_112_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_137_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_137_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_137_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
if (lean_obj_tag(v_a_115_) == 1)
{
lean_object* v_val_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_132_; 
v_val_119_ = lean_ctor_get(v_a_115_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_a_115_);
if (v_isSharedCheck_132_ == 0)
{
v___x_121_ = v_a_115_;
v_isShared_122_ = v_isSharedCheck_132_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_val_119_);
lean_dec(v_a_115_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_132_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v_val_123_; lean_object* v_toConstantVal_124_; lean_object* v_name_125_; lean_object* v___x_127_; 
v_val_123_ = lean_ctor_get(v_val_119_, 0);
lean_inc_ref(v_val_123_);
lean_dec(v_val_119_);
v_toConstantVal_124_ = lean_ctor_get(v_val_123_, 0);
lean_inc_ref(v_toConstantVal_124_);
lean_dec_ref(v_val_123_);
v_name_125_ = lean_ctor_get(v_toConstantVal_124_, 0);
lean_inc(v_name_125_);
lean_dec_ref(v_toConstantVal_124_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v_name_125_);
v___x_127_ = v___x_121_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_name_125_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_129_; 
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_127_);
v___x_129_ = v___x_117_;
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
else
{
lean_object* v___x_133_; lean_object* v___x_135_; 
lean_dec(v_a_115_);
v___x_133_ = lean_box(0);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_133_);
v___x_135_ = v___x_117_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
v_a_138_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_114_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_114_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg___boxed(lean_object* v_fvarId_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(v_fvarId_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_fvarId_146_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f(lean_object* v_fvarId_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(v_fvarId_153_, v_a_154_, v_a_156_, v_a_157_, v_a_158_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___boxed(lean_object* v_fvarId_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f(v_fvarId_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_);
lean_dec(v_a_166_);
lean_dec_ref(v_a_165_);
lean_dec(v_a_164_);
lean_dec_ref(v_a_163_);
lean_dec_ref(v_a_162_);
lean_dec(v_fvarId_161_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1(size_t v_sz_169_, size_t v_i_170_, lean_object* v_bs_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lean_usize_dec_lt(v_i_170_, v_sz_169_);
if (v___x_172_ == 0)
{
return v_bs_171_;
}
else
{
lean_object* v_v_173_; lean_object* v___x_174_; lean_object* v_bs_x27_175_; lean_object* v___y_177_; 
v_v_173_ = lean_array_uget(v_bs_171_, v_i_170_);
v___x_174_ = lean_unsigned_to_nat(0u);
v_bs_x27_175_ = lean_array_uset(v_bs_171_, v_i_170_, v___x_174_);
if (lean_obj_tag(v_v_173_) == 1)
{
lean_object* v_fvarId_182_; lean_object* v___x_183_; 
v_fvarId_182_ = lean_ctor_get(v_v_173_, 0);
lean_inc(v_fvarId_182_);
lean_dec_ref_known(v_v_173_, 1);
v___x_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_183_, 0, v_fvarId_182_);
v___y_177_ = v___x_183_;
goto v___jp_176_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = l_Lean_Expr_isErased(v_v_173_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; 
v___x_185_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_185_, 0, v_v_173_);
v___y_177_ = v___x_185_;
goto v___jp_176_;
}
else
{
lean_object* v___x_186_; 
lean_dec(v_v_173_);
v___x_186_ = lean_box(0);
v___y_177_ = v___x_186_;
goto v___jp_176_;
}
}
v___jp_176_:
{
size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((size_t)1ULL);
v___x_179_ = lean_usize_add(v_i_170_, v___x_178_);
v___x_180_ = lean_array_uset(v_bs_x27_175_, v_i_170_, v___y_177_);
v_i_170_ = v___x_179_;
v_bs_171_ = v___x_180_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1___boxed(lean_object* v_sz_187_, lean_object* v_i_188_, lean_object* v_bs_189_){
_start:
{
size_t v_sz_boxed_190_; size_t v_i_boxed_191_; lean_object* v_res_192_; 
v_sz_boxed_190_ = lean_unbox_usize(v_sz_187_);
lean_dec(v_sz_187_);
v_i_boxed_191_ = lean_unbox_usize(v_i_188_);
lean_dec(v_i_188_);
v_res_192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1(v_sz_boxed_190_, v_i_boxed_191_, v_bs_189_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0___redArg(lean_object* v_a_193_, lean_object* v_b_194_){
_start:
{
lean_object* v_array_195_; lean_object* v_start_196_; lean_object* v_stop_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_210_; 
v_array_195_ = lean_ctor_get(v_a_193_, 0);
v_start_196_ = lean_ctor_get(v_a_193_, 1);
v_stop_197_ = lean_ctor_get(v_a_193_, 2);
v_isSharedCheck_210_ = !lean_is_exclusive(v_a_193_);
if (v_isSharedCheck_210_ == 0)
{
v___x_199_ = v_a_193_;
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_stop_197_);
lean_inc(v_start_196_);
lean_inc(v_array_195_);
lean_dec(v_a_193_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_210_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
uint8_t v___x_201_; 
v___x_201_ = lean_nat_dec_lt(v_start_196_, v_stop_197_);
if (v___x_201_ == 0)
{
lean_del_object(v___x_199_);
lean_dec(v_stop_197_);
lean_dec(v_start_196_);
lean_dec_ref(v_array_195_);
return v_b_194_;
}
else
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_205_; 
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_add(v_start_196_, v___x_202_);
lean_inc_ref(v_array_195_);
if (v_isShared_200_ == 0)
{
lean_ctor_set(v___x_199_, 1, v___x_203_);
v___x_205_ = v___x_199_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_array_195_);
lean_ctor_set(v_reuseFailAlloc_209_, 1, v___x_203_);
lean_ctor_set(v_reuseFailAlloc_209_, 2, v_stop_197_);
v___x_205_ = v_reuseFailAlloc_209_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_206_ = lean_array_fget(v_array_195_, v_start_196_);
lean_dec(v_start_196_);
lean_dec_ref(v_array_195_);
v___x_207_ = lean_array_push(v_b_194_, v___x_206_);
v_a_193_ = v___x_205_;
v_b_194_ = v___x_207_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__0(void){
_start:
{
lean_object* v___x_211_; lean_object* v_dummy_212_; 
v___x_211_ = lean_box(0);
v_dummy_212_ = l_Lean_Expr_sort___override(v___x_211_);
return v_dummy_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg(lean_object* v_type_215_, lean_object* v_ind_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_type_219_; lean_object* v___x_220_; 
v_type_219_ = l_Lean_Expr_headBeta(v_type_215_);
v___x_220_ = l_Lean_Expr_getAppFn(v_type_219_);
if (lean_obj_tag(v___x_220_) == 4)
{
lean_object* v_declName_221_; lean_object* v_us_222_; uint8_t v___x_223_; 
v_declName_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_declName_221_);
v_us_222_ = lean_ctor_get(v___x_220_, 1);
lean_inc(v_us_222_);
lean_dec_ref_known(v___x_220_, 2);
v___x_223_ = lean_name_eq(v_declName_221_, v_ind_216_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec(v_us_222_);
lean_dec(v_declName_221_);
lean_dec_ref(v_type_219_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
else
{
lean_object* v___x_226_; lean_object* v_env_227_; lean_object* v___x_228_; 
v___x_226_ = lean_st_ref_get(v_a_217_);
v_env_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc_ref(v_env_227_);
lean_dec(v___x_226_);
v___x_228_ = l_Lean_Compiler_isInductiveOverrideSimpleCore_x3f(v_env_227_, v_declName_221_);
if (lean_obj_tag(v___x_228_) == 1)
{
lean_object* v_val_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_255_; 
v_val_229_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_255_ == 0)
{
v___x_231_ = v___x_228_;
v_isShared_232_ = v_isSharedCheck_255_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_val_229_);
lean_dec(v___x_228_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_255_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v_numParams_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_numParams_233_ = lean_ctor_get(v_val_229_, 0);
lean_inc(v_numParams_233_);
lean_dec(v_val_229_);
v___x_234_ = l_Lean_Expr_getAppNumArgs(v_type_219_);
v___x_235_ = lean_nat_dec_le(v_numParams_233_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v___x_234_);
lean_dec(v_numParams_233_);
lean_del_object(v___x_231_);
lean_dec(v_us_222_);
lean_dec_ref(v_type_219_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
return v___x_237_;
}
else
{
lean_object* v_dummy_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; size_t v_sz_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v_dummy_238_ = lean_obj_once(&l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__0, &l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__0);
lean_inc(v___x_234_);
v___x_239_ = lean_mk_array(v___x_234_, v_dummy_238_);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_sub(v___x_234_, v___x_240_);
lean_dec(v___x_234_);
v___x_242_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_219_, v___x_239_, v___x_241_);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = l_Array_toSubarray___redArg(v___x_242_, v___x_243_, v_numParams_233_);
v___x_245_ = ((lean_object*)(l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___closed__1));
v___x_246_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0___redArg(v___x_244_, v___x_245_);
v_sz_247_ = lean_array_size(v___x_246_);
v___x_248_ = ((size_t)0ULL);
v___x_249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__1(v_sz_247_, v___x_248_, v___x_246_);
v___x_250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_250_, 0, v_us_222_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_250_);
v___x_252_ = v___x_231_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_250_);
v___x_252_ = v_reuseFailAlloc_254_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_253_; 
v___x_253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_253_, 0, v___x_252_);
return v___x_253_;
}
}
}
}
else
{
lean_object* v___x_256_; lean_object* v___x_257_; 
lean_dec(v___x_228_);
lean_dec(v_us_222_);
lean_dec_ref(v_type_219_);
v___x_256_ = lean_box(0);
v___x_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
return v___x_257_;
}
}
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec_ref(v___x_220_);
lean_dec_ref(v_type_219_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg___boxed(lean_object* v_type_260_, lean_object* v_ind_261_, lean_object* v_a_262_, lean_object* v_a_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg(v_type_260_, v_ind_261_, v_a_262_);
lean_dec(v_a_262_);
lean_dec(v_ind_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f(lean_object* v_type_265_, lean_object* v_ind_266_, lean_object* v_a_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg(v_type_265_, v_ind_266_, v_a_268_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___boxed(lean_object* v_type_271_, lean_object* v_ind_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f(v_type_271_, v_ind_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_ind_272_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0(lean_object* v_inst_277_, lean_object* v_R_278_, lean_object* v_a_279_, lean_object* v_b_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_getIndInfo_x3f_spec__0___redArg(v_a_279_, v_b_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0(size_t v_sz_282_, size_t v_i_283_, lean_object* v_bs_284_){
_start:
{
uint8_t v___x_285_; 
v___x_285_ = lean_usize_dec_lt(v_i_283_, v_sz_282_);
if (v___x_285_ == 0)
{
return v_bs_284_;
}
else
{
lean_object* v_v_286_; lean_object* v_fvarId_287_; lean_object* v___x_288_; lean_object* v_bs_x27_289_; lean_object* v___x_290_; size_t v___x_291_; size_t v___x_292_; lean_object* v___x_293_; 
v_v_286_ = lean_array_uget_borrowed(v_bs_284_, v_i_283_);
v_fvarId_287_ = lean_ctor_get(v_v_286_, 0);
lean_inc(v_fvarId_287_);
v___x_288_ = lean_unsigned_to_nat(0u);
v_bs_x27_289_ = lean_array_uset(v_bs_284_, v_i_283_, v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v_fvarId_287_);
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_add(v_i_283_, v___x_291_);
v___x_293_ = lean_array_uset(v_bs_x27_289_, v_i_283_, v___x_290_);
v_i_283_ = v___x_292_;
v_bs_284_ = v___x_293_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0___boxed(lean_object* v_sz_295_, lean_object* v_i_296_, lean_object* v_bs_297_){
_start:
{
size_t v_sz_boxed_298_; size_t v_i_boxed_299_; lean_object* v_res_300_; 
v_sz_boxed_298_ = lean_unbox_usize(v_sz_295_);
lean_dec(v_sz_295_);
v_i_boxed_299_ = lean_unbox_usize(v_i_296_);
lean_dec(v_i_296_);
v_res_300_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0(v_sz_boxed_298_, v_i_boxed_299_, v_bs_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2_spec__3___redArg(lean_object* v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
lean_object* v_ks_305_; lean_object* v_vs_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_330_; 
v_ks_305_ = lean_ctor_get(v_x_301_, 0);
v_vs_306_ = lean_ctor_get(v_x_301_, 1);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_330_ == 0)
{
v___x_308_ = v_x_301_;
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_vs_306_);
lean_inc(v_ks_305_);
lean_dec(v_x_301_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_330_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; uint8_t v___x_311_; 
v___x_310_ = lean_array_get_size(v_ks_305_);
v___x_311_ = lean_nat_dec_lt(v_x_302_, v___x_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_315_; 
lean_dec(v_x_302_);
v___x_312_ = lean_array_push(v_ks_305_, v_x_303_);
v___x_313_ = lean_array_push(v_vs_306_, v_x_304_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_313_);
lean_ctor_set(v___x_308_, 0, v___x_312_);
v___x_315_ = v___x_308_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v___x_312_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v___x_313_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
else
{
lean_object* v_k_x27_317_; uint8_t v___x_318_; 
v_k_x27_317_ = lean_array_fget_borrowed(v_ks_305_, v_x_302_);
v___x_318_ = lean_expr_eqv(v_x_303_, v_k_x27_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_320_; 
if (v_isShared_309_ == 0)
{
v___x_320_ = v___x_308_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_ks_305_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_vs_306_);
v___x_320_ = v_reuseFailAlloc_324_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_add(v_x_302_, v___x_321_);
lean_dec(v_x_302_);
v_x_301_ = v___x_320_;
v_x_302_ = v___x_322_;
goto _start;
}
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_325_ = lean_array_fset(v_ks_305_, v_x_302_, v_x_303_);
v___x_326_ = lean_array_fset(v_vs_306_, v_x_302_, v_x_304_);
lean_dec(v_x_302_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v___x_326_);
lean_ctor_set(v___x_308_, 0, v___x_325_);
v___x_328_ = v___x_308_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_325_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
return v___x_328_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2___redArg(lean_object* v_n_331_, lean_object* v_k_332_, lean_object* v_v_333_){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_334_ = lean_unsigned_to_nat(0u);
v___x_335_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2_spec__3___redArg(v_n_331_, v___x_334_, v_k_332_, v_v_333_);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg(lean_object* v_x_337_, size_t v_x_338_, size_t v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v_es_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v_j_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v_es_342_ = lean_ctor_get(v_x_337_, 0);
v___x_343_ = ((size_t)31ULL);
v___x_344_ = lean_usize_land(v_x_338_, v___x_343_);
v_j_345_ = lean_usize_to_nat(v___x_344_);
v___x_346_ = lean_array_get_size(v_es_342_);
v___x_347_ = lean_nat_dec_lt(v_j_345_, v___x_346_);
if (v___x_347_ == 0)
{
lean_dec(v_j_345_);
lean_dec(v_x_341_);
lean_dec_ref(v_x_340_);
return v_x_337_;
}
else
{
lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_386_; 
lean_inc_ref(v_es_342_);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v_x_337_, 0);
lean_dec(v_unused_387_);
v___x_349_ = v_x_337_;
v_isShared_350_ = v_isSharedCheck_386_;
goto v_resetjp_348_;
}
else
{
lean_dec(v_x_337_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_386_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v_v_351_; lean_object* v___x_352_; lean_object* v_xs_x27_353_; lean_object* v___y_355_; 
v_v_351_ = lean_array_fget(v_es_342_, v_j_345_);
v___x_352_ = lean_box(0);
v_xs_x27_353_ = lean_array_fset(v_es_342_, v_j_345_, v___x_352_);
switch(lean_obj_tag(v_v_351_))
{
case 0:
{
lean_object* v_key_360_; lean_object* v_val_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_key_360_ = lean_ctor_get(v_v_351_, 0);
v_val_361_ = lean_ctor_get(v_v_351_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v_v_351_);
if (v_isSharedCheck_371_ == 0)
{
v___x_363_ = v_v_351_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_val_361_);
lean_inc(v_key_360_);
lean_dec(v_v_351_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
uint8_t v___x_365_; 
v___x_365_ = lean_expr_eqv(v_x_340_, v_key_360_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_del_object(v___x_363_);
v___x_366_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_360_, v_val_361_, v_x_340_, v_x_341_);
v___x_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
v___y_355_ = v___x_367_;
goto v___jp_354_;
}
else
{
lean_object* v___x_369_; 
lean_dec(v_val_361_);
lean_dec(v_key_360_);
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v_x_341_);
lean_ctor_set(v___x_363_, 0, v_x_340_);
v___x_369_ = v___x_363_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_x_340_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_x_341_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
v___y_355_ = v___x_369_;
goto v___jp_354_;
}
}
}
}
case 1:
{
lean_object* v_node_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_384_; 
v_node_372_ = lean_ctor_get(v_v_351_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v_v_351_);
if (v_isSharedCheck_384_ == 0)
{
v___x_374_ = v_v_351_;
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_node_372_);
lean_dec(v_v_351_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_376_ = ((size_t)5ULL);
v___x_377_ = lean_usize_shift_right(v_x_338_, v___x_376_);
v___x_378_ = ((size_t)1ULL);
v___x_379_ = lean_usize_add(v_x_339_, v___x_378_);
v___x_380_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg(v_node_372_, v___x_377_, v___x_379_, v_x_340_, v_x_341_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_380_);
v___x_382_ = v___x_374_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
v___y_355_ = v___x_382_;
goto v___jp_354_;
}
}
}
default: 
{
lean_object* v___x_385_; 
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_x_340_);
lean_ctor_set(v___x_385_, 1, v_x_341_);
v___y_355_ = v___x_385_;
goto v___jp_354_;
}
}
v___jp_354_:
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = lean_array_fset(v_xs_x27_353_, v_j_345_, v___y_355_);
lean_dec(v_j_345_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v___x_356_);
v___x_358_ = v___x_349_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
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
lean_object* v_ks_388_; lean_object* v_vs_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_409_; 
v_ks_388_ = lean_ctor_get(v_x_337_, 0);
v_vs_389_ = lean_ctor_get(v_x_337_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v_x_337_);
if (v_isSharedCheck_409_ == 0)
{
v___x_391_ = v_x_337_;
v_isShared_392_ = v_isSharedCheck_409_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_vs_389_);
lean_inc(v_ks_388_);
lean_dec(v_x_337_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_409_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_ks_388_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_vs_389_);
v___x_394_ = v_reuseFailAlloc_408_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
lean_object* v_newNode_395_; uint8_t v___y_397_; size_t v___x_403_; uint8_t v___x_404_; 
v_newNode_395_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2___redArg(v___x_394_, v_x_340_, v_x_341_);
v___x_403_ = ((size_t)7ULL);
v___x_404_ = lean_usize_dec_le(v___x_403_, v_x_339_);
if (v___x_404_ == 0)
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_395_);
v___x_406_ = lean_unsigned_to_nat(4u);
v___x_407_ = lean_nat_dec_lt(v___x_405_, v___x_406_);
lean_dec(v___x_405_);
v___y_397_ = v___x_407_;
goto v___jp_396_;
}
else
{
v___y_397_ = v___x_404_;
goto v___jp_396_;
}
v___jp_396_:
{
if (v___y_397_ == 0)
{
lean_object* v_ks_398_; lean_object* v_vs_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_ks_398_ = lean_ctor_get(v_newNode_395_, 0);
lean_inc_ref(v_ks_398_);
v_vs_399_ = lean_ctor_get(v_newNode_395_, 1);
lean_inc_ref(v_vs_399_);
lean_dec_ref(v_newNode_395_);
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg___closed__0);
v___x_402_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3___redArg(v_x_339_, v_ks_398_, v_vs_399_, v___x_400_, v___x_401_);
lean_dec_ref(v_vs_399_);
lean_dec_ref(v_ks_398_);
return v___x_402_;
}
else
{
return v_newNode_395_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3___redArg(size_t v_depth_410_, lean_object* v_keys_411_, lean_object* v_vals_412_, lean_object* v_i_413_, lean_object* v_entries_414_){
_start:
{
lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_415_ = lean_array_get_size(v_keys_411_);
v___x_416_ = lean_nat_dec_lt(v_i_413_, v___x_415_);
if (v___x_416_ == 0)
{
lean_dec(v_i_413_);
return v_entries_414_;
}
else
{
lean_object* v_k_417_; lean_object* v_v_418_; uint64_t v___x_419_; size_t v_h_420_; size_t v___x_421_; lean_object* v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v_h_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v_k_417_ = lean_array_fget_borrowed(v_keys_411_, v_i_413_);
v_v_418_ = lean_array_fget_borrowed(v_vals_412_, v_i_413_);
v___x_419_ = l_Lean_Expr_hash(v_k_417_);
v_h_420_ = lean_uint64_to_usize(v___x_419_);
v___x_421_ = ((size_t)5ULL);
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = ((size_t)1ULL);
v___x_424_ = lean_usize_sub(v_depth_410_, v___x_423_);
v___x_425_ = lean_usize_mul(v___x_421_, v___x_424_);
v_h_426_ = lean_usize_shift_right(v_h_420_, v___x_425_);
v___x_427_ = lean_nat_add(v_i_413_, v___x_422_);
lean_dec(v_i_413_);
lean_inc(v_v_418_);
lean_inc(v_k_417_);
v___x_428_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg(v_entries_414_, v_h_426_, v_depth_410_, v_k_417_, v_v_418_);
v_i_413_ = v___x_427_;
v_entries_414_ = v___x_428_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_depth_430_, lean_object* v_keys_431_, lean_object* v_vals_432_, lean_object* v_i_433_, lean_object* v_entries_434_){
_start:
{
size_t v_depth_boxed_435_; lean_object* v_res_436_; 
v_depth_boxed_435_ = lean_unbox_usize(v_depth_430_);
lean_dec(v_depth_430_);
v_res_436_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3___redArg(v_depth_boxed_435_, v_keys_431_, v_vals_432_, v_i_433_, v_entries_434_);
lean_dec_ref(v_vals_432_);
lean_dec_ref(v_keys_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg___boxed(lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_, lean_object* v_x_441_){
_start:
{
size_t v_x_2139__boxed_442_; size_t v_x_2140__boxed_443_; lean_object* v_res_444_; 
v_x_2139__boxed_442_ = lean_unbox_usize(v_x_438_);
lean_dec(v_x_438_);
v_x_2140__boxed_443_ = lean_unbox_usize(v_x_439_);
lean_dec(v_x_439_);
v_res_444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg(v_x_437_, v_x_2139__boxed_442_, v_x_2140__boxed_443_, v_x_440_, v_x_441_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1___redArg(lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
uint64_t v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v___x_448_ = l_Lean_Expr_hash(v_x_446_);
v___x_449_ = lean_uint64_to_usize(v___x_448_);
v___x_450_ = ((size_t)1ULL);
v___x_451_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg(v_x_445_, v___x_449_, v___x_450_, v_x_446_, v_x_447_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object* v_discr_452_, lean_object* v_ctorName_453_, lean_object* v_ctorFields_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_461_; 
v___x_461_ = l_Lean_Compiler_getConstInfoCtorOverride(v_ctorName_453_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_a_462_; lean_object* v___x_463_; 
v_a_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_a_462_);
lean_dec_ref_known(v___x_461_, 1);
lean_inc(v_discr_452_);
v___x_463_ = l_Lean_Compiler_LCNF_getType(v_discr_452_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v_a_464_; lean_object* v_toConstantVal_465_; lean_object* v_induct_466_; lean_object* v_numParams_467_; lean_object* v___x_468_; lean_object* v_a_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_518_; 
v_a_464_ = lean_ctor_get(v___x_463_, 0);
lean_inc(v_a_464_);
lean_dec_ref_known(v___x_463_, 1);
v_toConstantVal_465_ = lean_ctor_get(v_a_462_, 0);
lean_inc_ref(v_toConstantVal_465_);
v_induct_466_ = lean_ctor_get(v_a_462_, 1);
v_numParams_467_ = lean_ctor_get(v_a_462_, 3);
v___x_468_ = l_Lean_Compiler_LCNF_Simp_getIndInfo_x3f___redArg(v_a_464_, v_induct_466_, v_a_459_);
v_a_469_ = lean_ctor_get(v___x_468_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_468_);
if (v_isSharedCheck_518_ == 0)
{
v___x_471_ = v___x_468_;
v_isShared_472_ = v_isSharedCheck_518_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_a_469_);
lean_dec(v___x_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_518_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
size_t v_sz_473_; size_t v___x_474_; lean_object* v___x_475_; 
v_sz_473_ = lean_array_size(v_ctorFields_454_);
v___x_474_ = ((size_t)0ULL);
v___x_475_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__0(v_sz_473_, v___x_474_, v_ctorFields_454_);
if (lean_obj_tag(v_a_469_) == 1)
{
lean_object* v_val_476_; lean_object* v_fst_477_; lean_object* v_snd_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_506_; 
v_val_476_ = lean_ctor_get(v_a_469_, 0);
lean_inc(v_val_476_);
lean_dec_ref_known(v_a_469_, 1);
v_fst_477_ = lean_ctor_get(v_val_476_, 0);
v_snd_478_ = lean_ctor_get(v_val_476_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_val_476_);
if (v_isSharedCheck_506_ == 0)
{
v___x_480_ = v_val_476_;
v_isShared_481_ = v_isSharedCheck_506_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_snd_478_);
lean_inc(v_fst_477_);
lean_dec(v_val_476_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_506_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
lean_object* v_name_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_503_; 
v_name_482_ = lean_ctor_get(v_toConstantVal_465_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v_toConstantVal_465_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; lean_object* v_unused_505_; 
v_unused_504_ = lean_ctor_get(v_toConstantVal_465_, 2);
lean_dec(v_unused_504_);
v_unused_505_ = lean_ctor_get(v_toConstantVal_465_, 1);
lean_dec(v_unused_505_);
v___x_484_ = v_toConstantVal_465_;
v_isShared_485_ = v_isSharedCheck_503_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_name_482_);
lean_dec(v_toConstantVal_465_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_503_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v_discrCtorMap_486_; lean_object* v_ctorDiscrMap_487_; lean_object* v___x_488_; lean_object* v___x_490_; 
v_discrCtorMap_486_ = lean_ctor_get(v_a_455_, 0);
v_ctorDiscrMap_487_ = lean_ctor_get(v_a_455_, 1);
v___x_488_ = l_Array_append___redArg(v_snd_478_, v___x_475_);
lean_dec_ref(v___x_475_);
lean_inc_ref(v___x_488_);
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 1, v___x_488_);
lean_ctor_set(v___x_480_, 0, v_a_462_);
v___x_490_ = v___x_480_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_a_462_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_488_);
v___x_490_ = v_reuseFailAlloc_502_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
uint8_t v___x_491_; lean_object* v___x_493_; 
v___x_491_ = 0;
if (v_isShared_485_ == 0)
{
lean_ctor_set_tag(v___x_484_, 3);
lean_ctor_set(v___x_484_, 2, v___x_488_);
lean_ctor_set(v___x_484_, 1, v_fst_477_);
v___x_493_ = v___x_484_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_name_482_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_fst_477_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v___x_488_);
v___x_493_ = v_reuseFailAlloc_501_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
lean_inc(v_discrCtorMap_486_);
lean_inc(v_discr_452_);
v___x_494_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_452_, v___x_490_, v_discrCtorMap_486_);
v___x_495_ = l_Lean_Compiler_LCNF_LetValue_toExpr(v___x_491_, v___x_493_);
lean_inc_ref(v_ctorDiscrMap_487_);
v___x_496_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1___redArg(v_ctorDiscrMap_487_, v___x_495_, v_discr_452_);
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v___x_494_);
lean_ctor_set(v___x_497_, 1, v___x_496_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_497_);
v___x_499_ = v___x_471_;
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
}
}
}
}
else
{
lean_object* v_discrCtorMap_507_; lean_object* v_ctorDiscrMap_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_516_; 
lean_dec(v_a_469_);
lean_dec_ref(v_toConstantVal_465_);
v_discrCtorMap_507_ = lean_ctor_get(v_a_455_, 0);
v_ctorDiscrMap_508_ = lean_ctor_get(v_a_455_, 1);
v___x_509_ = lean_box(0);
lean_inc(v_numParams_467_);
v___x_510_ = lean_mk_array(v_numParams_467_, v___x_509_);
v___x_511_ = l_Array_append___redArg(v___x_510_, v___x_475_);
lean_dec_ref(v___x_475_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v_a_462_);
lean_ctor_set(v___x_512_, 1, v___x_511_);
lean_inc(v_discrCtorMap_507_);
v___x_513_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_discr_452_, v___x_512_, v_discrCtorMap_507_);
lean_inc_ref(v_ctorDiscrMap_508_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v_ctorDiscrMap_508_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 0, v___x_514_);
v___x_516_ = v___x_471_;
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
}
else
{
lean_object* v_a_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_526_; 
lean_dec(v_a_462_);
lean_dec_ref(v_ctorFields_454_);
lean_dec(v_discr_452_);
v_a_519_ = lean_ctor_get(v___x_463_, 0);
v_isSharedCheck_526_ = !lean_is_exclusive(v___x_463_);
if (v_isSharedCheck_526_ == 0)
{
v___x_521_ = v___x_463_;
v_isShared_522_ = v_isSharedCheck_526_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_a_519_);
lean_dec(v___x_463_);
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
lean_dec_ref(v_ctorFields_454_);
lean_dec(v_discr_452_);
v_a_527_ = lean_ctor_get(v___x_461_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_461_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___x_461_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_461_);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx___boxed(lean_object* v_discr_535_, lean_object* v_ctorName_536_, lean_object* v_ctorFields_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_535_, v_ctorName_536_, v_ctorFields_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec_ref(v_a_538_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1(lean_object* v_00_u03b2_545_, lean_object* v_x_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1___redArg(v_x_546_, v_x_547_, v_x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1(lean_object* v_00_u03b2_550_, lean_object* v_x_551_, size_t v_x_552_, size_t v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
lean_object* v___x_556_; 
v___x_556_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___redArg(v_x_551_, v_x_552_, v_x_553_, v_x_554_, v_x_555_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1___boxed(lean_object* v_00_u03b2_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
size_t v_x_2451__boxed_563_; size_t v_x_2452__boxed_564_; lean_object* v_res_565_; 
v_x_2451__boxed_563_ = lean_unbox_usize(v_x_559_);
lean_dec(v_x_559_);
v_x_2452__boxed_564_ = lean_unbox_usize(v_x_560_);
lean_dec(v_x_560_);
v_res_565_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1(v_00_u03b2_557_, v_x_558_, v_x_2451__boxed_563_, v_x_2452__boxed_564_, v_x_561_, v_x_562_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_566_, lean_object* v_n_567_, lean_object* v_k_568_, lean_object* v_v_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2___redArg(v_n_567_, v_k_568_, v_v_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3(lean_object* v_00_u03b2_571_, size_t v_depth_572_, lean_object* v_keys_573_, lean_object* v_vals_574_, lean_object* v_heq_575_, lean_object* v_i_576_, lean_object* v_entries_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3___redArg(v_depth_572_, v_keys_573_, v_vals_574_, v_i_576_, v_entries_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b2_579_, lean_object* v_depth_580_, lean_object* v_keys_581_, lean_object* v_vals_582_, lean_object* v_heq_583_, lean_object* v_i_584_, lean_object* v_entries_585_){
_start:
{
size_t v_depth_boxed_586_; lean_object* v_res_587_; 
v_depth_boxed_586_ = lean_unbox_usize(v_depth_580_);
lean_dec(v_depth_580_);
v_res_587_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__3(v_00_u03b2_579_, v_depth_boxed_586_, v_keys_581_, v_vals_582_, v_heq_583_, v_i_584_, v_entries_585_);
lean_dec_ref(v_vals_582_);
lean_dec_ref(v_keys_581_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__1_spec__1_spec__2_spec__3___redArg(v_x_589_, v_x_590_, v_x_591_, v_x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___redArg(lean_object* v_discr_594_, lean_object* v_ctorName_595_, lean_object* v_ctorFields_596_, lean_object* v_x_597_, lean_object* v_a_598_, lean_object* v_a_599_, lean_object* v_a_600_, lean_object* v_a_601_, lean_object* v_a_602_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_594_, v_ctorName_595_, v_ctorFields_596_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
if (lean_obj_tag(v___x_604_) == 0)
{
lean_object* v_a_605_; lean_object* v___x_606_; 
v_a_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_a_605_);
lean_dec_ref_known(v___x_604_, 1);
lean_inc(v_a_602_);
lean_inc_ref(v_a_601_);
lean_inc(v_a_600_);
lean_inc_ref(v_a_599_);
v___x_606_ = lean_apply_6(v_x_597_, v_a_605_, v_a_599_, v_a_600_, v_a_601_, v_a_602_, lean_box(0));
return v___x_606_;
}
else
{
lean_object* v_a_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_614_; 
lean_dec_ref(v_x_597_);
v_a_607_ = lean_ctor_get(v___x_604_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_614_ == 0)
{
v___x_609_ = v___x_604_;
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_a_607_);
lean_dec(v___x_604_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_614_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_612_; 
if (v_isShared_610_ == 0)
{
v___x_612_ = v___x_609_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_a_607_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___redArg___boxed(lean_object* v_discr_615_, lean_object* v_ctorName_616_, lean_object* v_ctorFields_617_, lean_object* v_x_618_, lean_object* v_a_619_, lean_object* v_a_620_, lean_object* v_a_621_, lean_object* v_a_622_, lean_object* v_a_623_, lean_object* v_a_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___redArg(v_discr_615_, v_ctorName_616_, v_ctorFields_617_, v_x_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_, v_a_623_);
lean_dec(v_a_623_);
lean_dec_ref(v_a_622_);
lean_dec(v_a_621_);
lean_dec_ref(v_a_620_);
lean_dec_ref(v_a_619_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp(lean_object* v_00_u03b1_626_, lean_object* v_discr_627_, lean_object* v_ctorName_628_, lean_object* v_ctorFields_629_, lean_object* v_x_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_, lean_object* v_a_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_627_, v_ctorName_628_, v_ctorFields_629_, v_a_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_639_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref_known(v___x_637_, 1);
lean_inc(v_a_635_);
lean_inc_ref(v_a_634_);
lean_inc(v_a_633_);
lean_inc_ref(v_a_632_);
v___x_639_ = lean_apply_6(v_x_630_, v_a_638_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, lean_box(0));
return v___x_639_;
}
else
{
lean_object* v_a_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_647_; 
lean_dec_ref(v_x_630_);
v_a_640_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_647_ == 0)
{
v___x_642_ = v___x_637_;
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_a_640_);
lean_dec(v___x_637_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_647_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_645_; 
if (v_isShared_643_ == 0)
{
v___x_645_ = v___x_642_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_a_640_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp___boxed(lean_object* v_00_u03b1_648_, lean_object* v_discr_649_, lean_object* v_ctorName_650_, lean_object* v_ctorFields_651_, lean_object* v_x_652_, lean_object* v_a_653_, lean_object* v_a_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp(v_00_u03b1_648_, v_discr_649_, v_ctorName_650_, v_ctorFields_651_, v_x_652_, v_a_653_, v_a_654_, v_a_655_, v_a_656_, v_a_657_);
lean_dec(v_a_657_);
lean_dec_ref(v_a_656_);
lean_dec(v_a_655_);
lean_dec_ref(v_a_654_);
lean_dec_ref(v_a_653_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0(lean_object* v_discr_660_, lean_object* v_ctorName_661_, lean_object* v_ctorFields_662_, lean_object* v_00_u03b2_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_660_, v_ctorName_661_, v_ctorFields_662_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
lean_inc(v___y_669_);
lean_inc_ref(v___y_668_);
lean_inc(v___y_667_);
lean_inc_ref(v___y_666_);
v___x_673_ = lean_apply_6(v___y_664_, v_a_672_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, lean_box(0));
return v___x_673_;
}
else
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_681_; 
lean_dec_ref(v___y_664_);
v_a_674_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_681_ == 0)
{
v___x_676_ = v___x_671_;
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_671_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_681_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_679_; 
if (v_isShared_677_ == 0)
{
v___x_679_ = v___x_676_;
goto v_reusejp_678_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
v___x_679_ = v_reuseFailAlloc_680_;
goto v_reusejp_678_;
}
v_reusejp_678_:
{
return v___x_679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0___boxed(lean_object* v_discr_682_, lean_object* v_ctorName_683_, lean_object* v_ctorFields_684_, lean_object* v_00_u03b2_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0(v_discr_682_, v_ctorName_683_, v_ctorFields_684_, v_00_u03b2_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg(lean_object* v_inst_694_, lean_object* v_discr_695_, lean_object* v_ctorName_696_, lean_object* v_ctorFields_697_, lean_object* v_a_698_){
_start:
{
lean_object* v___f_699_; lean_object* v___x_700_; 
v___f_699_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_699_, 0, v_discr_695_);
lean_closure_set(v___f_699_, 1, v_ctorName_696_);
lean_closure_set(v___f_699_, 2, v_ctorFields_697_);
v___x_700_ = lean_apply_3(v_inst_694_, lean_box(0), v___f_699_, v_a_698_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtor(lean_object* v_m_701_, lean_object* v_00_u03b1_702_, lean_object* v_inst_703_, lean_object* v_discr_704_, lean_object* v_ctorName_705_, lean_object* v_ctorFields_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___f_708_; lean_object* v___x_709_; 
v___f_708_ = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_withDiscrCtor___redArg___lam__0___boxed), 11, 3);
lean_closure_set(v___f_708_, 0, v_discr_704_);
lean_closure_set(v___f_708_, 1, v_ctorName_705_);
lean_closure_set(v___f_708_, 2, v_ctorFields_706_);
v___x_709_ = lean_apply_3(v_inst_703_, lean_box(0), v___f_708_, v_a_707_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_710_, lean_object* v_vals_711_, lean_object* v_i_712_, lean_object* v_k_713_){
_start:
{
lean_object* v___x_714_; uint8_t v___x_715_; 
v___x_714_ = lean_array_get_size(v_keys_710_);
v___x_715_ = lean_nat_dec_lt(v_i_712_, v___x_714_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; 
lean_dec(v_i_712_);
v___x_716_ = lean_box(0);
return v___x_716_;
}
else
{
lean_object* v_k_x27_717_; uint8_t v___x_718_; 
v_k_x27_717_ = lean_array_fget_borrowed(v_keys_710_, v_i_712_);
v___x_718_ = lean_expr_eqv(v_k_713_, v_k_x27_717_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = lean_unsigned_to_nat(1u);
v___x_720_ = lean_nat_add(v_i_712_, v___x_719_);
lean_dec(v_i_712_);
v_i_712_ = v___x_720_;
goto _start;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_array_fget_borrowed(v_vals_711_, v_i_712_);
lean_dec(v_i_712_);
lean_inc(v___x_722_);
v___x_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_724_, lean_object* v_vals_725_, lean_object* v_i_726_, lean_object* v_k_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_724_, v_vals_725_, v_i_726_, v_k_727_);
lean_dec_ref(v_k_727_);
lean_dec_ref(v_vals_725_);
lean_dec_ref(v_keys_724_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(lean_object* v_x_729_, size_t v_x_730_, lean_object* v_x_731_){
_start:
{
if (lean_obj_tag(v_x_729_) == 0)
{
lean_object* v_es_732_; lean_object* v___x_733_; size_t v___x_734_; size_t v___x_735_; lean_object* v_j_736_; lean_object* v___x_737_; 
v_es_732_ = lean_ctor_get(v_x_729_, 0);
v___x_733_ = lean_box(2);
v___x_734_ = ((size_t)31ULL);
v___x_735_ = lean_usize_land(v_x_730_, v___x_734_);
v_j_736_ = lean_usize_to_nat(v___x_735_);
v___x_737_ = lean_array_get_borrowed(v___x_733_, v_es_732_, v_j_736_);
lean_dec(v_j_736_);
switch(lean_obj_tag(v___x_737_))
{
case 0:
{
lean_object* v_key_738_; lean_object* v_val_739_; uint8_t v___x_740_; 
v_key_738_ = lean_ctor_get(v___x_737_, 0);
v_val_739_ = lean_ctor_get(v___x_737_, 1);
v___x_740_ = lean_expr_eqv(v_x_731_, v_key_738_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
v___x_741_ = lean_box(0);
return v___x_741_;
}
else
{
lean_object* v___x_742_; 
lean_inc(v_val_739_);
v___x_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_742_, 0, v_val_739_);
return v___x_742_;
}
}
case 1:
{
lean_object* v_node_743_; size_t v___x_744_; size_t v___x_745_; 
v_node_743_ = lean_ctor_get(v___x_737_, 0);
v___x_744_ = ((size_t)5ULL);
v___x_745_ = lean_usize_shift_right(v_x_730_, v___x_744_);
v_x_729_ = v_node_743_;
v_x_730_ = v___x_745_;
goto _start;
}
default: 
{
lean_object* v___x_747_; 
v___x_747_ = lean_box(0);
return v___x_747_;
}
}
}
else
{
lean_object* v_ks_748_; lean_object* v_vs_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v_ks_748_ = lean_ctor_get(v_x_729_, 0);
v_vs_749_ = lean_ctor_get(v_x_729_, 1);
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(v_ks_748_, v_vs_749_, v___x_750_, v_x_731_);
return v___x_751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_752_, lean_object* v_x_753_, lean_object* v_x_754_){
_start:
{
size_t v_x_1247__boxed_755_; lean_object* v_res_756_; 
v_x_1247__boxed_755_ = lean_unbox_usize(v_x_753_);
lean_dec(v_x_753_);
v_res_756_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(v_x_752_, v_x_1247__boxed_755_, v_x_754_);
lean_dec_ref(v_x_754_);
lean_dec_ref(v_x_752_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
uint64_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
v___x_759_ = l_Lean_Expr_hash(v_x_758_);
v___x_760_ = lean_uint64_to_usize(v___x_759_);
v___x_761_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(v_x_757_, v___x_760_, v_x_758_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg___boxed(lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(v_x_762_, v_x_763_);
lean_dec_ref(v_x_763_);
lean_dec_ref(v_x_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(lean_object* v_e_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_){
_start:
{
lean_object* v_ctorDiscrMap_772_; lean_object* v___x_773_; 
v_ctorDiscrMap_772_ = lean_ctor_get(v_a_766_, 1);
v___x_773_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(v_ctorDiscrMap_772_, v_e_765_);
if (lean_obj_tag(v___x_773_) == 1)
{
lean_object* v_val_774_; lean_object* v___x_775_; 
v_val_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_val_774_);
v___x_775_ = l_Lean_Compiler_LCNF_getType(v_val_774_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_777_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
lean_inc(v_a_776_);
lean_dec_ref_known(v___x_775_, 1);
v___x_777_ = l_Lean_Compiler_LCNF_inferType(v_e_765_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_790_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_790_ == 0)
{
v___x_780_ = v___x_777_;
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_777_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_790_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
uint8_t v___x_782_; 
v___x_782_ = l_Lean_Compiler_LCNF_eqvTypes(v_a_776_, v_a_778_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_785_; 
lean_dec_ref_known(v___x_773_, 1);
v___x_783_ = lean_box(0);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_783_);
v___x_785_ = v___x_780_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
else
{
lean_object* v___x_788_; 
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_773_);
v___x_788_ = v___x_780_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_773_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec(v_a_776_);
lean_dec_ref_known(v___x_773_, 1);
v_a_791_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_777_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_777_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref_known(v___x_773_, 1);
lean_dec_ref(v_e_765_);
v_a_799_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_775_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_775_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec(v___x_773_);
lean_dec_ref(v_e_765_);
v___x_807_ = lean_box(0);
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f___boxed(lean_object* v_e_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(v_e_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_);
lean_dec(v_a_814_);
lean_dec_ref(v_a_813_);
lean_dec(v_a_812_);
lean_dec_ref(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0(lean_object* v_00_u03b2_817_, lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___redArg(v_x_818_, v_x_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0___boxed(lean_object* v_00_u03b2_821_, lean_object* v_x_822_, lean_object* v_x_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0(v_00_u03b2_821_, v_x_822_, v_x_823_);
lean_dec_ref(v_x_823_);
lean_dec_ref(v_x_822_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0(lean_object* v_00_u03b2_825_, lean_object* v_x_826_, size_t v_x_827_, lean_object* v_x_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___redArg(v_x_826_, v_x_827_, v_x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_830_, lean_object* v_x_831_, lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
size_t v_x_1389__boxed_834_; lean_object* v_res_835_; 
v_x_1389__boxed_834_ = lean_unbox_usize(v_x_832_);
lean_dec(v_x_832_);
v_res_835_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0(v_00_u03b2_830_, v_x_831_, v_x_1389__boxed_834_, v_x_833_);
lean_dec_ref(v_x_833_);
lean_dec_ref(v_x_831_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_836_, lean_object* v_keys_837_, lean_object* v_vals_838_, lean_object* v_heq_839_, lean_object* v_i_840_, lean_object* v_k_841_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___redArg(v_keys_837_, v_vals_838_, v_i_840_, v_k_841_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_843_, lean_object* v_keys_844_, lean_object* v_vals_845_, lean_object* v_heq_846_, lean_object* v_i_847_, lean_object* v_k_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f_spec__0_spec__0_spec__1(v_00_u03b2_843_, v_keys_844_, v_vals_845_, v_heq_846_, v_i_847_, v_k_848_);
lean_dec_ref(v_k_848_);
lean_dec_ref(v_vals_845_);
lean_dec_ref(v_keys_844_);
return v_res_849_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_Simp_DiscrM(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_DiscrM(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
}
#ifdef __cplusplus
}
#endif
