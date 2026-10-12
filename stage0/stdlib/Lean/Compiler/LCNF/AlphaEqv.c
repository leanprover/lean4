// Lean compiler output
// Module: Lean.Compiler.LCNF.AlphaEqv
// Imports: public import Lean.Compiler.LCNF.Basic import Init.Omega
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
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_Compiler_LCNF_instBEqLitValue_beq(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvType(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvType___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqv(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(lean_object* v_t_1_, lean_object* v_k_2_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg___boxed(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(v_t_12_, v_k_13_);
lean_dec(v_k_13_);
lean_dec(v_t_12_);
return v_res_14_;
}
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(lean_object* v_fvarId_u2081_15_, lean_object* v_fvarId_u2082_16_, lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(v_a_17_, v_fvarId_u2082_16_);
if (lean_obj_tag(v___x_18_) == 0)
{
uint8_t v___x_19_; 
v___x_19_ = l_Lean_instBEqFVarId_beq(v_fvarId_u2081_15_, v_fvarId_u2082_16_);
return v___x_19_;
}
else
{
lean_object* v_val_20_; uint8_t v___x_21_; 
v_val_20_ = lean_ctor_get(v___x_18_, 0);
lean_inc(v_val_20_);
lean_dec_ref_known(v___x_18_, 1);
v___x_21_ = l_Lean_instBEqFVarId_beq(v_fvarId_u2081_15_, v_val_20_);
lean_dec(v_val_20_);
return v___x_21_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_u2081_15_ = stack[0].m_obj;
lean_object* v_fvarId_u2082_16_ = stack[1].m_obj;
lean_object* v_a_17_ = stack[2].m_obj;
uint8_t v_res_22_;
v_res_22_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_u2081_15_, v_fvarId_u2082_16_, v_a_17_);
stack->m_num = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar___boxed(lean_object* v_fvarId_u2081_23_, lean_object* v_fvarId_u2082_24_, lean_object* v_a_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_u2081_23_, v_fvarId_u2082_24_, v_a_25_);
lean_dec(v_a_25_);
lean_dec(v_fvarId_u2082_24_);
lean_dec(v_fvarId_u2081_23_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0(lean_object* v_00_u03b4_28_, lean_object* v_t_29_, lean_object* v_k_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(v_t_29_, v_k_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___boxed(lean_object* v_00_u03b4_32_, lean_object* v_t_33_, lean_object* v_k_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0(v_00_u03b4_32_, v_t_33_, v_k_34_);
lean_dec(v_k_34_);
lean_dec(v_t_33_);
return v_res_35_;
}
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvType(lean_object* v_e_u2081_36_, lean_object* v_e_u2082_37_, lean_object* v_a_38_){
_start:
{
switch(lean_obj_tag(v_e_u2081_36_))
{
case 5:
{
if (lean_obj_tag(v_e_u2082_37_) == 5)
{
lean_object* v_fn_39_; lean_object* v_arg_40_; lean_object* v_fn_41_; lean_object* v_arg_42_; uint8_t v___x_43_; 
v_fn_39_ = lean_ctor_get(v_e_u2081_36_, 0);
v_arg_40_ = lean_ctor_get(v_e_u2081_36_, 1);
v_fn_41_ = lean_ctor_get(v_e_u2082_37_, 0);
v_arg_42_ = lean_ctor_get(v_e_u2082_37_, 1);
v___x_43_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_arg_40_, v_arg_42_, v_a_38_);
if (v___x_43_ == 0)
{
return v___x_43_;
}
else
{
v_e_u2081_36_ = v_fn_39_;
v_e_u2082_37_ = v_fn_41_;
goto _start;
}
}
else
{
uint8_t v___x_45_; 
v___x_45_ = lean_expr_eqv(v_e_u2081_36_, v_e_u2082_37_);
return v___x_45_;
}
}
case 1:
{
if (lean_obj_tag(v_e_u2082_37_) == 1)
{
lean_object* v_fvarId_46_; lean_object* v_fvarId_47_; uint8_t v___x_48_; 
v_fvarId_46_ = lean_ctor_get(v_e_u2081_36_, 0);
v_fvarId_47_ = lean_ctor_get(v_e_u2082_37_, 0);
v___x_48_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_46_, v_fvarId_47_, v_a_38_);
return v___x_48_;
}
else
{
uint8_t v___x_49_; 
v___x_49_ = lean_expr_eqv(v_e_u2081_36_, v_e_u2082_37_);
return v___x_49_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_37_) == 7)
{
lean_object* v_binderType_50_; lean_object* v_body_51_; lean_object* v_binderType_52_; lean_object* v_body_53_; uint8_t v___x_54_; 
v_binderType_50_ = lean_ctor_get(v_e_u2081_36_, 1);
v_body_51_ = lean_ctor_get(v_e_u2081_36_, 2);
v_binderType_52_ = lean_ctor_get(v_e_u2082_37_, 1);
v_body_53_ = lean_ctor_get(v_e_u2082_37_, 2);
v___x_54_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_binderType_50_, v_binderType_52_, v_a_38_);
if (v___x_54_ == 0)
{
return v___x_54_;
}
else
{
v_e_u2081_36_ = v_body_51_;
v_e_u2082_37_ = v_body_53_;
goto _start;
}
}
else
{
uint8_t v___x_56_; 
v___x_56_ = lean_expr_eqv(v_e_u2081_36_, v_e_u2082_37_);
return v___x_56_;
}
}
default: 
{
uint8_t v___x_57_; 
v___x_57_ = lean_expr_eqv(v_e_u2081_36_, v_e_u2082_37_);
return v___x_57_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_eqvType_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_u2081_36_ = stack[0].m_obj;
lean_object* v_e_u2082_37_ = stack[1].m_obj;
lean_object* v_a_38_ = stack[2].m_obj;
uint8_t v_res_58_;
v_res_58_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_e_u2081_36_, v_e_u2082_37_, v_a_38_);
stack->m_num = v_res_58_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvType___boxed(lean_object* v_e_u2081_59_, lean_object* v_e_u2082_60_, lean_object* v_a_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_e_u2081_59_, v_e_u2082_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_e_u2082_60_);
lean_dec_ref(v_e_u2081_59_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(lean_object* v_as_64_, size_t v_sz_65_, size_t v_i_66_, lean_object* v_b_67_, lean_object* v___y_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_usize_dec_lt(v_i_66_, v_sz_65_);
if (v___x_69_ == 0)
{
return v_b_67_;
}
else
{
lean_object* v_snd_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_108_; 
v_snd_70_ = lean_ctor_get(v_b_67_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_b_67_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v_b_67_, 0);
lean_dec(v_unused_109_);
v___x_72_ = v_b_67_;
v_isShared_73_ = v_isSharedCheck_108_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_snd_70_);
lean_dec(v_b_67_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_108_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v_array_74_; lean_object* v_start_75_; lean_object* v_stop_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_array_74_ = lean_ctor_get(v_snd_70_, 0);
v_start_75_ = lean_ctor_get(v_snd_70_, 1);
v_stop_76_ = lean_ctor_get(v_snd_70_, 2);
v___x_77_ = lean_box(0);
v___x_78_ = lean_nat_dec_lt(v_start_75_, v_stop_76_);
if (v___x_78_ == 0)
{
lean_object* v___x_80_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_77_);
v___x_80_ = v___x_72_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_snd_70_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
else
{
lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_104_; 
lean_inc(v_stop_76_);
lean_inc(v_start_75_);
lean_inc_ref(v_array_74_);
v_isSharedCheck_104_ = !lean_is_exclusive(v_snd_70_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; lean_object* v_unused_106_; lean_object* v_unused_107_; 
v_unused_105_ = lean_ctor_get(v_snd_70_, 2);
lean_dec(v_unused_105_);
v_unused_106_ = lean_ctor_get(v_snd_70_, 1);
lean_dec(v_unused_106_);
v_unused_107_ = lean_ctor_get(v_snd_70_, 0);
lean_dec(v_unused_107_);
v___x_83_ = v_snd_70_;
v_isShared_84_ = v_isSharedCheck_104_;
goto v_resetjp_82_;
}
else
{
lean_dec(v_snd_70_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_104_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_a_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
v_a_85_ = lean_array_uget_borrowed(v_as_64_, v_i_66_);
v___x_86_ = lean_array_fget(v_array_74_, v_start_75_);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_start_75_, v___x_87_);
lean_dec(v_start_75_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v___x_88_);
v___x_90_ = v___x_83_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_array_74_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_stop_76_);
v___x_90_ = v_reuseFailAlloc_103_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
uint8_t v___x_91_; 
v___x_91_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_a_85_, v___x_86_, v___y_68_);
lean_dec(v___x_86_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_92_ = lean_box(v___x_91_);
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___x_90_);
lean_ctor_set(v___x_72_, 0, v___x_93_);
v___x_95_ = v___x_72_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v___x_90_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
else
{
lean_object* v___x_98_; 
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 1, v___x_90_);
lean_ctor_set(v___x_72_, 0, v___x_77_);
v___x_98_ = v___x_72_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___x_90_);
v___x_98_ = v_reuseFailAlloc_102_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
size_t v___x_99_; size_t v___x_100_; 
v___x_99_ = ((size_t)1ULL);
v___x_100_ = lean_usize_add(v_i_66_, v___x_99_);
v_i_66_ = v___x_100_;
v_b_67_ = v___x_98_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_64_ = stack[0].m_obj;
size_t v_sz_65_ = stack[1].m_num;
size_t v_i_66_ = stack[2].m_num;
lean_object* v_b_67_ = stack[3].m_obj;
lean_object* v___y_68_ = stack[4].m_obj;
lean_object* v_res_110_;
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(v_as_64_, v_sz_65_, v_i_66_, v_b_67_, v___y_68_);
stack->m_obj
 = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0___boxed(lean_object* v_as_111_, lean_object* v_sz_112_, lean_object* v_i_113_, lean_object* v_b_114_, lean_object* v___y_115_){
_start:
{
size_t v_sz_boxed_116_; size_t v_i_boxed_117_; lean_object* v_res_118_; 
v_sz_boxed_116_ = lean_unbox_usize(v_sz_112_);
lean_dec(v_sz_112_);
v_i_boxed_117_ = lean_unbox_usize(v_i_113_);
lean_dec(v_i_113_);
v_res_118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(v_as_111_, v_sz_boxed_116_, v_i_boxed_117_, v_b_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v_as_111_);
return v_res_118_;
}
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes(lean_object* v_es_u2081_119_, lean_object* v_es_u2082_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_122_ = lean_array_get_size(v_es_u2081_119_);
v___x_123_ = lean_array_get_size(v_es_u2082_120_);
v___x_124_ = lean_nat_dec_eq(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_dec_ref(v_es_u2082_120_);
return v___x_124_;
}
else
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; size_t v_sz_129_; size_t v___x_130_; lean_object* v___x_131_; lean_object* v_fst_132_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = l_Array_toSubarray___redArg(v_es_u2082_120_, v___x_125_, v___x_123_);
v___x_127_ = lean_box(0);
v___x_128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_126_);
v_sz_129_ = lean_array_size(v_es_u2081_119_);
v___x_130_ = ((size_t)0ULL);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(v_es_u2081_119_, v_sz_129_, v___x_130_, v___x_128_, v_a_121_);
v_fst_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_fst_132_);
lean_dec_ref(v___x_131_);
if (lean_obj_tag(v_fst_132_) == 0)
{
return v___x_124_;
}
else
{
lean_object* v_val_133_; uint8_t v___x_134_; 
v_val_133_ = lean_ctor_get(v_fst_132_, 0);
lean_inc(v_val_133_);
lean_dec_ref_known(v_fst_132_, 1);
v___x_134_ = lean_unbox(v_val_133_);
lean_dec(v_val_133_);
return v___x_134_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes_0interp(lean_interpreter_value* stack)
{
lean_object* v_es_u2081_119_ = stack[0].m_obj;
lean_object* v_es_u2082_120_ = stack[1].m_obj;
lean_object* v_a_121_ = stack[2].m_obj;
uint8_t v_res_135_;
v_res_135_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes(v_es_u2081_119_, v_es_u2082_120_, v_a_121_);
stack->m_num = v_res_135_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes___boxed(lean_object* v_es_u2081_136_, lean_object* v_es_u2082_137_, lean_object* v_a_138_){
_start:
{
uint8_t v_res_139_; lean_object* v_r_140_; 
v_res_139_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes(v_es_u2081_136_, v_es_u2082_137_, v_a_138_);
lean_dec(v_a_138_);
lean_dec_ref(v_es_u2081_136_);
v_r_140_ = lean_box(v_res_139_);
return v_r_140_;
}
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(lean_object* v_a_u2081_141_, lean_object* v_a_u2082_142_, lean_object* v_a_143_){
_start:
{
switch(lean_obj_tag(v_a_u2081_141_))
{
case 0:
{
if (lean_obj_tag(v_a_u2082_142_) == 0)
{
uint8_t v___x_144_; 
v___x_144_ = 1;
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
case 1:
{
if (lean_obj_tag(v_a_u2082_142_) == 1)
{
lean_object* v_fvarId_146_; lean_object* v_fvarId_147_; uint8_t v___x_148_; 
v_fvarId_146_ = lean_ctor_get(v_a_u2081_141_, 0);
v_fvarId_147_ = lean_ctor_get(v_a_u2082_142_, 0);
v___x_148_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_146_, v_fvarId_147_, v_a_143_);
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
default: 
{
if (lean_obj_tag(v_a_u2082_142_) == 2)
{
lean_object* v_expr_150_; lean_object* v_expr_151_; uint8_t v___x_152_; 
v_expr_150_ = lean_ctor_get(v_a_u2081_141_, 0);
v_expr_151_ = lean_ctor_get(v_a_u2082_142_, 0);
v___x_152_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_expr_150_, v_expr_151_, v_a_143_);
return v___x_152_;
}
else
{
uint8_t v___x_153_; 
v___x_153_ = 0;
return v___x_153_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_u2081_141_ = stack[0].m_obj;
lean_object* v_a_u2082_142_ = stack[1].m_obj;
lean_object* v_a_143_ = stack[2].m_obj;
uint8_t v_res_154_;
v_res_154_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_a_u2081_141_, v_a_u2082_142_, v_a_143_);
stack->m_num = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg___boxed(lean_object* v_a_u2081_155_, lean_object* v_a_u2082_156_, lean_object* v_a_157_){
_start:
{
uint8_t v_res_158_; lean_object* v_r_159_; 
v_res_158_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_a_u2081_155_, v_a_u2082_156_, v_a_157_);
lean_dec(v_a_157_);
lean_dec(v_a_u2082_156_);
lean_dec(v_a_u2081_155_);
v_r_159_ = lean_box(v_res_158_);
return v_r_159_;
}
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvArg(uint8_t v_pu_160_, lean_object* v_a_u2081_161_, lean_object* v_a_u2082_162_, lean_object* v_a_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_a_u2081_161_, v_a_u2082_162_, v_a_163_);
return v___x_164_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_eqvArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_160_ = stack[0].m_num;
lean_object* v_a_u2081_161_ = stack[1].m_obj;
lean_object* v_a_u2082_162_ = stack[2].m_obj;
lean_object* v_a_163_ = stack[3].m_obj;
uint8_t v_res_165_;
v_res_165_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg(v_pu_160_, v_a_u2081_161_, v_a_u2082_162_, v_a_163_);
stack->m_num = v_res_165_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___boxed(lean_object* v_pu_166_, lean_object* v_a_u2081_167_, lean_object* v_a_u2082_168_, lean_object* v_a_169_){
_start:
{
uint8_t v_pu_boxed_170_; uint8_t v_res_171_; lean_object* v_r_172_; 
v_pu_boxed_170_ = lean_unbox(v_pu_166_);
v_res_171_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg(v_pu_boxed_170_, v_a_u2081_167_, v_a_u2082_168_, v_a_169_);
lean_dec(v_a_169_);
lean_dec(v_a_u2082_168_);
lean_dec(v_a_u2081_167_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(lean_object* v_as_173_, size_t v_sz_174_, size_t v_i_175_, lean_object* v_b_176_, lean_object* v___y_177_){
_start:
{
uint8_t v___x_178_; 
v___x_178_ = lean_usize_dec_lt(v_i_175_, v_sz_174_);
if (v___x_178_ == 0)
{
return v_b_176_;
}
else
{
lean_object* v_snd_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_217_; 
v_snd_179_ = lean_ctor_get(v_b_176_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_b_176_);
if (v_isSharedCheck_217_ == 0)
{
lean_object* v_unused_218_; 
v_unused_218_ = lean_ctor_get(v_b_176_, 0);
lean_dec(v_unused_218_);
v___x_181_ = v_b_176_;
v_isShared_182_ = v_isSharedCheck_217_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snd_179_);
lean_dec(v_b_176_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_217_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v_array_183_; lean_object* v_start_184_; lean_object* v_stop_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v_array_183_ = lean_ctor_get(v_snd_179_, 0);
v_start_184_ = lean_ctor_get(v_snd_179_, 1);
v_stop_185_ = lean_ctor_get(v_snd_179_, 2);
v___x_186_ = lean_box(0);
v___x_187_ = lean_nat_dec_lt(v_start_184_, v_stop_185_);
if (v___x_187_ == 0)
{
lean_object* v___x_189_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 0, v___x_186_);
v___x_189_ = v___x_181_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_snd_179_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
else
{
lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_213_; 
lean_inc(v_stop_185_);
lean_inc(v_start_184_);
lean_inc_ref(v_array_183_);
v_isSharedCheck_213_ = !lean_is_exclusive(v_snd_179_);
if (v_isSharedCheck_213_ == 0)
{
lean_object* v_unused_214_; lean_object* v_unused_215_; lean_object* v_unused_216_; 
v_unused_214_ = lean_ctor_get(v_snd_179_, 2);
lean_dec(v_unused_214_);
v_unused_215_ = lean_ctor_get(v_snd_179_, 1);
lean_dec(v_unused_215_);
v_unused_216_ = lean_ctor_get(v_snd_179_, 0);
lean_dec(v_unused_216_);
v___x_192_ = v_snd_179_;
v_isShared_193_ = v_isSharedCheck_213_;
goto v_resetjp_191_;
}
else
{
lean_dec(v_snd_179_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_213_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v_a_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v_a_194_ = lean_array_uget_borrowed(v_as_173_, v_i_175_);
v___x_195_ = lean_array_fget(v_array_183_, v_start_184_);
v___x_196_ = lean_unsigned_to_nat(1u);
v___x_197_ = lean_nat_add(v_start_184_, v___x_196_);
lean_dec(v_start_184_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_197_);
v___x_199_ = v___x_192_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_array_183_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_197_);
lean_ctor_set(v_reuseFailAlloc_212_, 2, v_stop_185_);
v___x_199_ = v_reuseFailAlloc_212_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
uint8_t v___x_200_; 
v___x_200_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_a_194_, v___x_195_, v___y_177_);
lean_dec(v___x_195_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_201_ = lean_box(v___x_200_);
v___x_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_199_);
lean_ctor_set(v___x_181_, 0, v___x_202_);
v___x_204_ = v___x_181_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
else
{
lean_object* v___x_207_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_199_);
lean_ctor_set(v___x_181_, 0, v___x_186_);
v___x_207_ = v___x_181_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v___x_199_);
v___x_207_ = v_reuseFailAlloc_211_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
size_t v___x_208_; size_t v___x_209_; 
v___x_208_ = ((size_t)1ULL);
v___x_209_ = lean_usize_add(v_i_175_, v___x_208_);
v_i_175_ = v___x_209_;
v_b_176_ = v___x_207_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_173_ = stack[0].m_obj;
size_t v_sz_174_ = stack[1].m_num;
size_t v_i_175_ = stack[2].m_num;
lean_object* v_b_176_ = stack[3].m_obj;
lean_object* v___y_177_ = stack[4].m_obj;
lean_object* v_res_219_;
v_res_219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_173_, v_sz_174_, v_i_175_, v_b_176_, v___y_177_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg___boxed(lean_object* v_as_220_, lean_object* v_sz_221_, lean_object* v_i_222_, lean_object* v_b_223_, lean_object* v___y_224_){
_start:
{
size_t v_sz_boxed_225_; size_t v_i_boxed_226_; lean_object* v_res_227_; 
v_sz_boxed_225_ = lean_unbox_usize(v_sz_221_);
lean_dec(v_sz_221_);
v_i_boxed_226_ = lean_unbox_usize(v_i_222_);
lean_dec(v_i_222_);
v_res_227_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_220_, v_sz_boxed_225_, v_i_boxed_226_, v_b_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v_as_220_);
return v_res_227_;
}
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(uint8_t v_pu_228_, lean_object* v_as_u2081_229_, lean_object* v_as_u2082_230_, lean_object* v_a_231_){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = lean_array_get_size(v_as_u2081_229_);
v___x_233_ = lean_array_get_size(v_as_u2082_230_);
v___x_234_ = lean_nat_dec_eq(v___x_232_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec_ref(v_as_u2082_230_);
return v___x_234_;
}
else
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; size_t v_sz_239_; size_t v___x_240_; lean_object* v___x_241_; lean_object* v_fst_242_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = l_Array_toSubarray___redArg(v_as_u2082_230_, v___x_235_, v___x_233_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v___x_236_);
v_sz_239_ = lean_array_size(v_as_u2081_229_);
v___x_240_ = ((size_t)0ULL);
v___x_241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_u2081_229_, v_sz_239_, v___x_240_, v___x_238_, v_a_231_);
v_fst_242_ = lean_ctor_get(v___x_241_, 0);
lean_inc(v_fst_242_);
lean_dec_ref(v___x_241_);
if (lean_obj_tag(v_fst_242_) == 0)
{
return v___x_234_;
}
else
{
lean_object* v_val_243_; uint8_t v___x_244_; 
v_val_243_ = lean_ctor_get(v_fst_242_, 0);
lean_inc(v_val_243_);
lean_dec_ref_known(v_fst_242_, 1);
v___x_244_ = lean_unbox(v_val_243_);
lean_dec(v_val_243_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_228_ = stack[0].m_num;
lean_object* v_as_u2081_229_ = stack[1].m_obj;
lean_object* v_as_u2082_230_ = stack[2].m_obj;
lean_object* v_a_231_ = stack[3].m_obj;
uint8_t v_res_245_;
v_res_245_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_228_, v_as_u2081_229_, v_as_u2082_230_, v_a_231_);
stack->m_num = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs___boxed(lean_object* v_pu_246_, lean_object* v_as_u2081_247_, lean_object* v_as_u2082_248_, lean_object* v_a_249_){
_start:
{
uint8_t v_pu_boxed_250_; uint8_t v_res_251_; lean_object* v_r_252_; 
v_pu_boxed_250_ = lean_unbox(v_pu_246_);
v_res_251_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_boxed_250_, v_as_u2081_247_, v_as_u2082_248_, v_a_249_);
lean_dec(v_a_249_);
lean_dec_ref(v_as_u2081_247_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0(uint8_t v_pu_253_, lean_object* v_as_254_, size_t v_sz_255_, size_t v_i_256_, lean_object* v_b_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_254_, v_sz_255_, v_i_256_, v_b_257_, v___y_258_);
return v___x_259_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_253_ = stack[0].m_num;
lean_object* v_as_254_ = stack[1].m_obj;
size_t v_sz_255_ = stack[2].m_num;
size_t v_i_256_ = stack[3].m_num;
lean_object* v_b_257_ = stack[4].m_obj;
lean_object* v___y_258_ = stack[5].m_obj;
lean_object* v_res_260_;
v_res_260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0(v_pu_253_, v_as_254_, v_sz_255_, v_i_256_, v_b_257_, v___y_258_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___boxed(lean_object* v_pu_261_, lean_object* v_as_262_, lean_object* v_sz_263_, lean_object* v_i_264_, lean_object* v_b_265_, lean_object* v___y_266_){
_start:
{
uint8_t v_pu_boxed_267_; size_t v_sz_boxed_268_; size_t v_i_boxed_269_; lean_object* v_res_270_; 
v_pu_boxed_267_ = lean_unbox(v_pu_261_);
v_sz_boxed_268_ = lean_unbox_usize(v_sz_263_);
lean_dec(v_sz_263_);
v_i_boxed_269_ = lean_unbox_usize(v_i_264_);
lean_dec(v_i_264_);
v_res_270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0(v_pu_boxed_267_, v_as_262_, v_sz_boxed_268_, v_i_boxed_269_, v_b_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v_as_262_);
return v_res_270_;
}
}
uint8_t l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
if (lean_obj_tag(v_x_272_) == 0)
{
uint8_t v___x_273_; 
v___x_273_ = 1;
return v___x_273_;
}
else
{
uint8_t v___x_274_; 
v___x_274_ = 0;
return v___x_274_;
}
}
else
{
if (lean_obj_tag(v_x_272_) == 0)
{
uint8_t v___x_275_; 
v___x_275_ = 0;
return v___x_275_;
}
else
{
lean_object* v_head_276_; lean_object* v_tail_277_; lean_object* v_head_278_; lean_object* v_tail_279_; uint8_t v___x_280_; 
v_head_276_ = lean_ctor_get(v_x_271_, 0);
v_tail_277_ = lean_ctor_get(v_x_271_, 1);
v_head_278_ = lean_ctor_get(v_x_272_, 0);
v_tail_279_ = lean_ctor_get(v_x_272_, 1);
v___x_280_ = lean_level_eq(v_head_276_, v_head_278_);
if (v___x_280_ == 0)
{
return v___x_280_;
}
else
{
v_x_271_ = v_tail_277_;
v_x_272_ = v_tail_279_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_271_ = stack[0].m_obj;
lean_object* v_x_272_ = stack[1].m_obj;
uint8_t v_res_282_;
v_res_282_ = l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(v_x_271_, v_x_272_);
stack->m_num = v_res_282_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0___boxed(lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(v_x_283_, v_x_284_);
lean_dec(v_x_284_);
lean_dec(v_x_283_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(uint8_t v_pu_287_, lean_object* v_e_u2081_288_, lean_object* v_e_u2082_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_f_u2081_292_; lean_object* v_as_u2081_293_; lean_object* v_f_u2082_294_; lean_object* v_as_u2082_295_; lean_object* v___y_296_; lean_object* v_i_u2081_300_; lean_object* v_v_u2081_301_; lean_object* v_i_u2082_302_; lean_object* v_v_u2082_303_; lean_object* v___y_304_; 
switch(lean_obj_tag(v_e_u2081_288_))
{
case 0:
{
if (lean_obj_tag(v_e_u2082_289_) == 0)
{
lean_object* v_value_307_; lean_object* v_value_308_; uint8_t v___x_309_; 
v_value_307_ = lean_ctor_get(v_e_u2081_288_, 0);
v_value_308_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc_ref(v_value_308_);
lean_dec_ref_known(v_e_u2082_289_, 1);
v___x_309_ = l_Lean_Compiler_LCNF_instBEqLitValue_beq(v_value_307_, v_value_308_);
lean_dec_ref(v_value_308_);
return v___x_309_;
}
else
{
uint8_t v___x_310_; 
lean_dec(v_e_u2082_289_);
v___x_310_ = 0;
return v___x_310_;
}
}
case 1:
{
if (lean_obj_tag(v_e_u2082_289_) == 1)
{
uint8_t v___x_311_; 
v___x_311_ = 1;
return v___x_311_;
}
else
{
uint8_t v___x_312_; 
lean_dec(v_e_u2082_289_);
v___x_312_ = 0;
return v___x_312_;
}
}
case 2:
{
if (lean_obj_tag(v_e_u2082_289_) == 2)
{
lean_object* v_typeName_313_; lean_object* v_idx_314_; lean_object* v_struct_315_; lean_object* v_typeName_316_; lean_object* v_idx_317_; lean_object* v_struct_318_; uint8_t v___y_320_; uint8_t v___x_322_; 
v_typeName_313_ = lean_ctor_get(v_e_u2081_288_, 0);
v_idx_314_ = lean_ctor_get(v_e_u2081_288_, 1);
v_struct_315_ = lean_ctor_get(v_e_u2081_288_, 2);
v_typeName_316_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_typeName_316_);
v_idx_317_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc(v_idx_317_);
v_struct_318_ = lean_ctor_get(v_e_u2082_289_, 2);
lean_inc(v_struct_318_);
lean_dec_ref_known(v_e_u2082_289_, 3);
v___x_322_ = lean_name_eq(v_typeName_313_, v_typeName_316_);
lean_dec(v_typeName_316_);
if (v___x_322_ == 0)
{
lean_dec(v_idx_317_);
v___y_320_ = v___x_322_;
goto v___jp_319_;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = lean_nat_dec_eq(v_idx_314_, v_idx_317_);
lean_dec(v_idx_317_);
v___y_320_ = v___x_323_;
goto v___jp_319_;
}
v___jp_319_:
{
if (v___y_320_ == 0)
{
lean_dec(v_struct_318_);
return v___y_320_;
}
else
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_struct_315_, v_struct_318_, v_a_290_);
lean_dec(v_struct_318_);
return v___x_321_;
}
}
}
else
{
uint8_t v___x_324_; 
lean_dec(v_e_u2082_289_);
v___x_324_ = 0;
return v___x_324_;
}
}
case 3:
{
if (lean_obj_tag(v_e_u2082_289_) == 3)
{
lean_object* v_declName_325_; lean_object* v_us_326_; lean_object* v_args_327_; lean_object* v_declName_328_; lean_object* v_us_329_; lean_object* v_args_330_; uint8_t v___y_332_; uint8_t v___x_334_; 
v_declName_325_ = lean_ctor_get(v_e_u2081_288_, 0);
v_us_326_ = lean_ctor_get(v_e_u2081_288_, 1);
v_args_327_ = lean_ctor_get(v_e_u2081_288_, 2);
v_declName_328_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_declName_328_);
v_us_329_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc(v_us_329_);
v_args_330_ = lean_ctor_get(v_e_u2082_289_, 2);
lean_inc_ref(v_args_330_);
lean_dec_ref_known(v_e_u2082_289_, 3);
v___x_334_ = lean_name_eq(v_declName_325_, v_declName_328_);
lean_dec(v_declName_328_);
if (v___x_334_ == 0)
{
lean_dec(v_us_329_);
v___y_332_ = v___x_334_;
goto v___jp_331_;
}
else
{
uint8_t v___x_335_; 
v___x_335_ = l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(v_us_326_, v_us_329_);
lean_dec(v_us_329_);
v___y_332_ = v___x_335_;
goto v___jp_331_;
}
v___jp_331_:
{
if (v___y_332_ == 0)
{
lean_dec_ref(v_args_330_);
return v___y_332_;
}
else
{
uint8_t v___x_333_; 
v___x_333_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_287_, v_args_327_, v_args_330_, v_a_290_);
return v___x_333_;
}
}
}
else
{
uint8_t v___x_336_; 
lean_dec(v_e_u2082_289_);
v___x_336_ = 0;
return v___x_336_;
}
}
case 4:
{
if (lean_obj_tag(v_e_u2082_289_) == 4)
{
lean_object* v_fvarId_337_; lean_object* v_args_338_; lean_object* v_fvarId_339_; lean_object* v_args_340_; uint8_t v___x_341_; 
v_fvarId_337_ = lean_ctor_get(v_e_u2081_288_, 0);
v_args_338_ = lean_ctor_get(v_e_u2081_288_, 1);
v_fvarId_339_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_fvarId_339_);
v_args_340_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc_ref(v_args_340_);
lean_dec_ref_known(v_e_u2082_289_, 2);
v___x_341_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_337_, v_fvarId_339_, v_a_290_);
lean_dec(v_fvarId_339_);
if (v___x_341_ == 0)
{
lean_dec_ref(v_args_340_);
return v___x_341_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_287_, v_args_338_, v_args_340_, v_a_290_);
return v___x_342_;
}
}
else
{
uint8_t v___x_343_; 
lean_dec(v_e_u2082_289_);
v___x_343_ = 0;
return v___x_343_;
}
}
case 5:
{
if (lean_obj_tag(v_e_u2082_289_) == 5)
{
lean_object* v_i_344_; lean_object* v_args_345_; lean_object* v_i_346_; lean_object* v_args_347_; uint8_t v___x_348_; 
v_i_344_ = lean_ctor_get(v_e_u2081_288_, 0);
v_args_345_ = lean_ctor_get(v_e_u2081_288_, 1);
v_i_346_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc_ref(v_i_346_);
v_args_347_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc_ref(v_args_347_);
lean_dec_ref_known(v_e_u2082_289_, 2);
v___x_348_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_i_344_, v_i_346_);
lean_dec_ref(v_i_346_);
if (v___x_348_ == 0)
{
lean_dec_ref(v_args_347_);
return v___x_348_;
}
else
{
uint8_t v___x_349_; 
v___x_349_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_287_, v_args_345_, v_args_347_, v_a_290_);
return v___x_349_;
}
}
else
{
uint8_t v___x_350_; 
lean_dec(v_e_u2082_289_);
v___x_350_ = 0;
return v___x_350_;
}
}
case 6:
{
if (lean_obj_tag(v_e_u2082_289_) == 6)
{
lean_object* v_i_351_; lean_object* v_var_352_; lean_object* v_i_353_; lean_object* v_var_354_; 
v_i_351_ = lean_ctor_get(v_e_u2081_288_, 0);
v_var_352_ = lean_ctor_get(v_e_u2081_288_, 1);
v_i_353_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_i_353_);
v_var_354_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc(v_var_354_);
lean_dec_ref_known(v_e_u2082_289_, 2);
v_i_u2081_300_ = v_i_351_;
v_v_u2081_301_ = v_var_352_;
v_i_u2082_302_ = v_i_353_;
v_v_u2082_303_ = v_var_354_;
v___y_304_ = v_a_290_;
goto v___jp_299_;
}
else
{
uint8_t v___x_355_; 
lean_dec(v_e_u2082_289_);
v___x_355_ = 0;
return v___x_355_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_289_) == 7)
{
lean_object* v_i_356_; lean_object* v_var_357_; lean_object* v_i_358_; lean_object* v_var_359_; 
v_i_356_ = lean_ctor_get(v_e_u2081_288_, 0);
v_var_357_ = lean_ctor_get(v_e_u2081_288_, 1);
v_i_358_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_i_358_);
v_var_359_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc(v_var_359_);
lean_dec_ref_known(v_e_u2082_289_, 2);
v_i_u2081_300_ = v_i_356_;
v_v_u2081_301_ = v_var_357_;
v_i_u2082_302_ = v_i_358_;
v_v_u2082_303_ = v_var_359_;
v___y_304_ = v_a_290_;
goto v___jp_299_;
}
else
{
uint8_t v___x_360_; 
lean_dec(v_e_u2082_289_);
v___x_360_ = 0;
return v___x_360_;
}
}
case 8:
{
if (lean_obj_tag(v_e_u2082_289_) == 8)
{
lean_object* v_n_361_; lean_object* v_offset_362_; lean_object* v_var_363_; lean_object* v_n_364_; lean_object* v_offset_365_; lean_object* v_var_366_; uint8_t v___x_367_; 
v_n_361_ = lean_ctor_get(v_e_u2081_288_, 0);
v_offset_362_ = lean_ctor_get(v_e_u2081_288_, 1);
v_var_363_ = lean_ctor_get(v_e_u2081_288_, 2);
v_n_364_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_n_364_);
v_offset_365_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc(v_offset_365_);
v_var_366_ = lean_ctor_get(v_e_u2082_289_, 2);
lean_inc(v_var_366_);
lean_dec_ref_known(v_e_u2082_289_, 3);
v___x_367_ = lean_nat_dec_eq(v_n_361_, v_n_364_);
lean_dec(v_n_364_);
if (v___x_367_ == 0)
{
lean_dec(v_var_366_);
lean_dec(v_offset_365_);
return v___x_367_;
}
else
{
uint8_t v___x_368_; 
v___x_368_ = lean_nat_dec_eq(v_offset_362_, v_offset_365_);
lean_dec(v_offset_365_);
if (v___x_368_ == 0)
{
lean_dec(v_var_366_);
return v___x_368_;
}
else
{
uint8_t v___x_369_; 
v___x_369_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_var_363_, v_var_366_, v_a_290_);
lean_dec(v_var_366_);
return v___x_369_;
}
}
}
else
{
uint8_t v___x_370_; 
lean_dec(v_e_u2082_289_);
v___x_370_ = 0;
return v___x_370_;
}
}
case 9:
{
if (lean_obj_tag(v_e_u2082_289_) == 9)
{
lean_object* v_fn_371_; lean_object* v_args_372_; lean_object* v_fn_373_; lean_object* v_args_374_; 
v_fn_371_ = lean_ctor_get(v_e_u2081_288_, 0);
v_args_372_ = lean_ctor_get(v_e_u2081_288_, 1);
v_fn_373_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_fn_373_);
v_args_374_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc_ref(v_args_374_);
lean_dec_ref_known(v_e_u2082_289_, 2);
v_f_u2081_292_ = v_fn_371_;
v_as_u2081_293_ = v_args_372_;
v_f_u2082_294_ = v_fn_373_;
v_as_u2082_295_ = v_args_374_;
v___y_296_ = v_a_290_;
goto v___jp_291_;
}
else
{
uint8_t v___x_375_; 
lean_dec(v_e_u2082_289_);
v___x_375_ = 0;
return v___x_375_;
}
}
case 10:
{
if (lean_obj_tag(v_e_u2082_289_) == 10)
{
lean_object* v_fn_376_; lean_object* v_args_377_; lean_object* v_fn_378_; lean_object* v_args_379_; 
v_fn_376_ = lean_ctor_get(v_e_u2081_288_, 0);
v_args_377_ = lean_ctor_get(v_e_u2081_288_, 1);
v_fn_378_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_fn_378_);
v_args_379_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc_ref(v_args_379_);
lean_dec_ref_known(v_e_u2082_289_, 2);
v_f_u2081_292_ = v_fn_376_;
v_as_u2081_293_ = v_args_377_;
v_f_u2082_294_ = v_fn_378_;
v_as_u2082_295_ = v_args_379_;
v___y_296_ = v_a_290_;
goto v___jp_291_;
}
else
{
uint8_t v___x_380_; 
lean_dec(v_e_u2082_289_);
v___x_380_ = 0;
return v___x_380_;
}
}
case 11:
{
if (lean_obj_tag(v_e_u2082_289_) == 11)
{
lean_object* v_n_381_; lean_object* v_var_382_; lean_object* v_n_383_; lean_object* v_var_384_; 
v_n_381_ = lean_ctor_get(v_e_u2081_288_, 0);
v_var_382_ = lean_ctor_get(v_e_u2081_288_, 1);
v_n_383_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_n_383_);
v_var_384_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc(v_var_384_);
lean_dec_ref_known(v_e_u2082_289_, 2);
v_i_u2081_300_ = v_n_381_;
v_v_u2081_301_ = v_var_382_;
v_i_u2082_302_ = v_n_383_;
v_v_u2082_303_ = v_var_384_;
v___y_304_ = v_a_290_;
goto v___jp_299_;
}
else
{
uint8_t v___x_385_; 
lean_dec(v_e_u2082_289_);
v___x_385_ = 0;
return v___x_385_;
}
}
case 12:
{
if (lean_obj_tag(v_e_u2082_289_) == 12)
{
lean_object* v_var_386_; lean_object* v_i_387_; uint8_t v_updateHeader_388_; lean_object* v_args_389_; lean_object* v_var_390_; lean_object* v_i_391_; uint8_t v_updateHeader_392_; lean_object* v_args_393_; uint8_t v___y_395_; uint8_t v___x_398_; 
v_var_386_ = lean_ctor_get(v_e_u2081_288_, 0);
v_i_387_ = lean_ctor_get(v_e_u2081_288_, 1);
v_updateHeader_388_ = lean_ctor_get_uint8(v_e_u2081_288_, sizeof(void*)*3);
v_args_389_ = lean_ctor_get(v_e_u2081_288_, 2);
v_var_390_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_var_390_);
v_i_391_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc_ref(v_i_391_);
v_updateHeader_392_ = lean_ctor_get_uint8(v_e_u2082_289_, sizeof(void*)*3);
v_args_393_ = lean_ctor_get(v_e_u2082_289_, 2);
lean_inc_ref(v_args_393_);
lean_dec_ref_known(v_e_u2082_289_, 3);
v___x_398_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_i_387_, v_i_391_);
lean_dec_ref(v_i_391_);
if (v___x_398_ == 0)
{
v___y_395_ = v___x_398_;
goto v___jp_394_;
}
else
{
if (v_updateHeader_392_ == 0)
{
if (v_updateHeader_388_ == 0)
{
v___y_395_ = v___x_398_;
goto v___jp_394_;
}
else
{
lean_dec_ref(v_args_393_);
lean_dec(v_var_390_);
return v_updateHeader_392_;
}
}
else
{
v___y_395_ = v_updateHeader_388_;
goto v___jp_394_;
}
}
v___jp_394_:
{
if (v___y_395_ == 0)
{
lean_dec_ref(v_args_393_);
lean_dec(v_var_390_);
return v___y_395_;
}
else
{
uint8_t v___x_396_; 
v___x_396_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_var_386_, v_var_390_, v_a_290_);
lean_dec(v_var_390_);
if (v___x_396_ == 0)
{
lean_dec_ref(v_args_393_);
return v___x_396_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_287_, v_args_389_, v_args_393_, v_a_290_);
return v___x_397_;
}
}
}
}
else
{
uint8_t v___x_399_; 
lean_dec(v_e_u2082_289_);
v___x_399_ = 0;
return v___x_399_;
}
}
case 13:
{
if (lean_obj_tag(v_e_u2082_289_) == 13)
{
lean_object* v_ty_400_; lean_object* v_fvarId_401_; lean_object* v_ty_402_; lean_object* v_fvarId_403_; uint8_t v___x_404_; 
v_ty_400_ = lean_ctor_get(v_e_u2081_288_, 0);
v_fvarId_401_ = lean_ctor_get(v_e_u2081_288_, 1);
v_ty_402_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc_ref(v_ty_402_);
v_fvarId_403_ = lean_ctor_get(v_e_u2082_289_, 1);
lean_inc(v_fvarId_403_);
lean_dec_ref_known(v_e_u2082_289_, 2);
v___x_404_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_400_, v_ty_402_, v_a_290_);
lean_dec_ref(v_ty_402_);
if (v___x_404_ == 0)
{
lean_dec(v_fvarId_403_);
return v___x_404_;
}
else
{
uint8_t v___x_405_; 
v___x_405_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_401_, v_fvarId_403_, v_a_290_);
lean_dec(v_fvarId_403_);
return v___x_405_;
}
}
else
{
uint8_t v___x_406_; 
lean_dec(v_e_u2082_289_);
v___x_406_ = 0;
return v___x_406_;
}
}
case 14:
{
if (lean_obj_tag(v_e_u2082_289_) == 14)
{
lean_object* v_fvarId_407_; lean_object* v_fvarId_408_; uint8_t v___x_409_; 
v_fvarId_407_ = lean_ctor_get(v_e_u2081_288_, 0);
v_fvarId_408_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_fvarId_408_);
lean_dec_ref_known(v_e_u2082_289_, 1);
v___x_409_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_407_, v_fvarId_408_, v_a_290_);
lean_dec(v_fvarId_408_);
return v___x_409_;
}
else
{
uint8_t v___x_410_; 
lean_dec(v_e_u2082_289_);
v___x_410_ = 0;
return v___x_410_;
}
}
default: 
{
if (lean_obj_tag(v_e_u2082_289_) == 15)
{
lean_object* v_fvarId_411_; lean_object* v_fvarId_412_; uint8_t v___x_413_; 
v_fvarId_411_ = lean_ctor_get(v_e_u2081_288_, 0);
v_fvarId_412_ = lean_ctor_get(v_e_u2082_289_, 0);
lean_inc(v_fvarId_412_);
lean_dec_ref_known(v_e_u2082_289_, 1);
v___x_413_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_411_, v_fvarId_412_, v_a_290_);
lean_dec(v_fvarId_412_);
return v___x_413_;
}
else
{
uint8_t v___x_414_; 
lean_dec(v_e_u2082_289_);
v___x_414_ = 0;
return v___x_414_;
}
}
}
v___jp_291_:
{
uint8_t v___x_297_; 
v___x_297_ = lean_name_eq(v_f_u2081_292_, v_f_u2082_294_);
lean_dec(v_f_u2082_294_);
if (v___x_297_ == 0)
{
lean_dec_ref(v_as_u2082_295_);
return v___x_297_;
}
else
{
uint8_t v___x_298_; 
v___x_298_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_287_, v_as_u2081_293_, v_as_u2082_295_, v___y_296_);
return v___x_298_;
}
}
v___jp_299_:
{
uint8_t v___x_305_; 
v___x_305_ = lean_nat_dec_eq(v_i_u2081_300_, v_i_u2082_302_);
lean_dec(v_i_u2082_302_);
if (v___x_305_ == 0)
{
lean_dec(v_v_u2082_303_);
return v___x_305_;
}
else
{
uint8_t v___x_306_; 
v___x_306_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_v_u2081_301_, v_v_u2082_303_, v___y_304_);
lean_dec(v_v_u2082_303_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_287_ = stack[0].m_num;
lean_object* v_e_u2081_288_ = stack[1].m_obj;
lean_object* v_e_u2082_289_ = stack[2].m_obj;
lean_object* v_a_290_ = stack[3].m_obj;
uint8_t v_res_415_;
v_res_415_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_287_, v_e_u2081_288_, v_e_u2082_289_, v_a_290_);
stack->m_num = v_res_415_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue___boxed(lean_object* v_pu_416_, lean_object* v_e_u2081_417_, lean_object* v_e_u2082_418_, lean_object* v_a_419_){
_start:
{
uint8_t v_pu_boxed_420_; uint8_t v_res_421_; lean_object* v_r_422_; 
v_pu_boxed_420_ = lean_unbox(v_pu_416_);
v_res_421_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_boxed_420_, v_e_u2081_417_, v_e_u2082_418_, v_a_419_);
lean_dec(v_a_419_);
lean_dec(v_e_u2081_417_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(lean_object* v_fvarId_u2081_423_, lean_object* v_fvarId_u2082_424_, lean_object* v_x_425_, lean_object* v_a_426_){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_inc(v_a_426_);
v___x_427_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_424_, v_fvarId_u2081_423_, v_a_426_);
v___x_428_ = lean_apply_1(v_x_425_, v___x_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg___boxed(lean_object* v_fvarId_u2081_429_, lean_object* v_fvarId_u2082_430_, lean_object* v_x_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(v_fvarId_u2081_429_, v_fvarId_u2082_430_, v_x_431_, v_a_432_);
lean_dec(v_a_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar(lean_object* v_00_u03b1_434_, lean_object* v_fvarId_u2081_435_, lean_object* v_fvarId_u2082_436_, lean_object* v_x_437_, lean_object* v_a_438_){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_inc(v_a_438_);
v___x_439_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_436_, v_fvarId_u2081_435_, v_a_438_);
v___x_440_ = lean_apply_1(v_x_437_, v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___boxed(lean_object* v_00_u03b1_441_, lean_object* v_fvarId_u2081_442_, lean_object* v_fvarId_u2082_443_, lean_object* v_x_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar(v_00_u03b1_441_, v_fvarId_u2081_442_, v_fvarId_u2082_443_, v_x_444_, v_a_445_);
lean_dec(v_a_445_);
return v_res_446_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(lean_object* v_params_u2081_447_, lean_object* v_params_u2082_448_, lean_object* v_x_449_, lean_object* v_i_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = lean_array_get_size(v_params_u2081_447_);
v___x_453_ = lean_nat_dec_lt(v_i_450_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
lean_dec(v_i_450_);
v___x_454_ = lean_apply_1(v_x_449_, v_a_451_);
v___x_455_ = lean_unbox(v___x_454_);
return v___x_455_;
}
else
{
lean_object* v_p_u2081_456_; lean_object* v_fvarId_457_; lean_object* v_type_458_; lean_object* v_p_u2082_459_; lean_object* v_fvarId_460_; lean_object* v_type_461_; uint8_t v___x_462_; 
v_p_u2081_456_ = lean_array_fget_borrowed(v_params_u2081_447_, v_i_450_);
v_fvarId_457_ = lean_ctor_get(v_p_u2081_456_, 0);
v_type_458_ = lean_ctor_get(v_p_u2081_456_, 2);
v_p_u2082_459_ = lean_array_fget_borrowed(v_params_u2082_448_, v_i_450_);
v_fvarId_460_ = lean_ctor_get(v_p_u2082_459_, 0);
v_type_461_ = lean_ctor_get(v_p_u2082_459_, 2);
v___x_462_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_458_, v_type_461_, v_a_451_);
if (v___x_462_ == 0)
{
lean_dec(v_a_451_);
lean_dec(v_i_450_);
lean_dec_ref(v_x_449_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = lean_nat_add(v_i_450_, v___x_463_);
lean_dec(v_i_450_);
lean_inc(v_fvarId_457_);
lean_inc(v_fvarId_460_);
v___x_465_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_460_, v_fvarId_457_, v_a_451_);
v_i_450_ = v___x_464_;
v_a_451_ = v___x_465_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_u2081_447_ = stack[0].m_obj;
lean_object* v_params_u2082_448_ = stack[1].m_obj;
lean_object* v_x_449_ = stack[2].m_obj;
lean_object* v_i_450_ = stack[3].m_obj;
lean_object* v_a_451_ = stack[4].m_obj;
uint8_t v_res_467_;
v_res_467_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_447_, v_params_u2082_448_, v_x_449_, v_i_450_, v_a_451_);
stack->m_num = v_res_467_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg___boxed(lean_object* v_params_u2081_468_, lean_object* v_params_u2082_469_, lean_object* v_x_470_, lean_object* v_i_471_, lean_object* v_a_472_){
_start:
{
uint8_t v_res_473_; lean_object* v_r_474_; 
v_res_473_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_468_, v_params_u2082_469_, v_x_470_, v_i_471_, v_a_472_);
lean_dec_ref(v_params_u2082_469_);
lean_dec_ref(v_params_u2081_468_);
v_r_474_ = lean_box(v_res_473_);
return v_r_474_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(uint8_t v_pu_475_, lean_object* v_params_u2081_476_, lean_object* v_params_u2082_477_, lean_object* v_x_478_, lean_object* v_h_479_, lean_object* v_i_480_, lean_object* v_a_481_){
_start:
{
uint8_t v___x_482_; 
lean_inc(v_a_481_);
v___x_482_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_476_, v_params_u2082_477_, v_x_478_, v_i_480_, v_a_481_);
return v___x_482_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_475_ = stack[0].m_num;
lean_object* v_params_u2081_476_ = stack[1].m_obj;
lean_object* v_params_u2082_477_ = stack[2].m_obj;
lean_object* v_x_478_ = stack[3].m_obj;
lean_object* v_i_480_ = stack[5].m_obj;
lean_object* v_a_481_ = stack[6].m_obj;
uint8_t v_res_483_;
v_res_483_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(v_pu_475_, v_params_u2081_476_, v_params_u2082_477_, v_x_478_, lean_box(0), v_i_480_, v_a_481_);
stack->m_num = v_res_483_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___boxed(lean_object* v_pu_484_, lean_object* v_params_u2081_485_, lean_object* v_params_u2082_486_, lean_object* v_x_487_, lean_object* v_h_488_, lean_object* v_i_489_, lean_object* v_a_490_){
_start:
{
uint8_t v_pu_boxed_491_; uint8_t v_res_492_; lean_object* v_r_493_; 
v_pu_boxed_491_ = lean_unbox(v_pu_484_);
v_res_492_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(v_pu_boxed_491_, v_params_u2081_485_, v_params_u2082_486_, v_x_487_, v_h_488_, v_i_489_, v_a_490_);
lean_dec(v_a_490_);
lean_dec_ref(v_params_u2082_486_);
lean_dec_ref(v_params_u2081_485_);
v_r_493_ = lean_box(v_res_492_);
return v_r_493_;
}
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(lean_object* v_params_u2081_494_, lean_object* v_params_u2082_495_, lean_object* v_x_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_498_ = lean_array_get_size(v_params_u2082_495_);
v___x_499_ = lean_array_get_size(v_params_u2081_494_);
v___x_500_ = lean_nat_dec_eq(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec_ref(v_x_496_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; uint8_t v___x_502_; 
v___x_501_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_497_);
v___x_502_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_494_, v_params_u2082_495_, v_x_496_, v___x_501_, v_a_497_);
return v___x_502_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_u2081_494_ = stack[0].m_obj;
lean_object* v_params_u2082_495_ = stack[1].m_obj;
lean_object* v_x_496_ = stack[2].m_obj;
lean_object* v_a_497_ = stack[3].m_obj;
uint8_t v_res_503_;
v_res_503_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(v_params_u2081_494_, v_params_u2082_495_, v_x_496_, v_a_497_);
stack->m_num = v_res_503_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg___boxed(lean_object* v_params_u2081_504_, lean_object* v_params_u2082_505_, lean_object* v_x_506_, lean_object* v_a_507_){
_start:
{
uint8_t v_res_508_; lean_object* v_r_509_; 
v_res_508_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(v_params_u2081_504_, v_params_u2082_505_, v_x_506_, v_a_507_);
lean_dec(v_a_507_);
lean_dec_ref(v_params_u2082_505_);
lean_dec_ref(v_params_u2081_504_);
v_r_509_ = lean_box(v_res_508_);
return v_r_509_;
}
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams(uint8_t v_pu_510_, lean_object* v_params_u2081_511_, lean_object* v_params_u2082_512_, lean_object* v_x_513_, lean_object* v_a_514_){
_start:
{
lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v___x_515_ = lean_array_get_size(v_params_u2082_512_);
v___x_516_ = lean_array_get_size(v_params_u2081_511_);
v___x_517_ = lean_nat_dec_eq(v___x_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec_ref(v_x_513_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_514_);
v___x_519_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_511_, v_params_u2082_512_, v_x_513_, v___x_518_, v_a_514_);
return v___x_519_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_withParams_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_510_ = stack[0].m_num;
lean_object* v_params_u2081_511_ = stack[1].m_obj;
lean_object* v_params_u2082_512_ = stack[2].m_obj;
lean_object* v_x_513_ = stack[3].m_obj;
lean_object* v_a_514_ = stack[4].m_obj;
uint8_t v_res_520_;
v_res_520_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams(v_pu_510_, v_params_u2081_511_, v_params_u2082_512_, v_x_513_, v_a_514_);
stack->m_num = v_res_520_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___boxed(lean_object* v_pu_521_, lean_object* v_params_u2081_522_, lean_object* v_params_u2082_523_, lean_object* v_x_524_, lean_object* v_a_525_){
_start:
{
uint8_t v_pu_boxed_526_; uint8_t v_res_527_; lean_object* v_r_528_; 
v_pu_boxed_526_ = lean_unbox(v_pu_521_);
v_res_527_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams(v_pu_boxed_526_, v_params_u2081_522_, v_params_u2082_523_, v_x_524_, v_a_525_);
lean_dec(v_a_525_);
lean_dec_ref(v_params_u2082_523_);
lean_dec_ref(v_params_u2081_522_);
v_r_528_ = lean_box(v_res_527_);
return v_r_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(lean_object* v_hi_529_, lean_object* v_pivot_530_, lean_object* v_as_531_, lean_object* v_i_532_, lean_object* v_k_533_){
_start:
{
uint8_t v___y_545_; uint8_t v___x_546_; 
v___x_546_ = lean_nat_dec_lt(v_k_533_, v_hi_529_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; 
lean_dec(v_k_533_);
v___x_547_ = lean_array_fswap(v_as_531_, v_i_532_, v_hi_529_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_i_532_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = lean_array_fget_borrowed(v_as_531_, v_k_533_);
switch(lean_obj_tag(v___x_549_))
{
case 0:
{
switch(lean_obj_tag(v_pivot_530_))
{
case 2:
{
goto v___jp_538_;
}
case 0:
{
lean_object* v_ctorName_550_; lean_object* v_ctorName_551_; uint8_t v___x_552_; 
v_ctorName_550_ = lean_ctor_get(v___x_549_, 0);
v_ctorName_551_ = lean_ctor_get(v_pivot_530_, 0);
v___x_552_ = l_Lean_Name_lt(v_ctorName_550_, v_ctorName_551_);
v___y_545_ = v___x_552_;
goto v___jp_544_;
}
default: 
{
goto v___jp_534_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_pivot_530_))
{
case 2:
{
goto v___jp_538_;
}
case 1:
{
lean_object* v_info_553_; lean_object* v_info_554_; lean_object* v_name_555_; lean_object* v_name_556_; uint8_t v___x_557_; 
v_info_553_ = lean_ctor_get(v___x_549_, 0);
v_info_554_ = lean_ctor_get(v_pivot_530_, 0);
v_name_555_ = lean_ctor_get(v_info_553_, 0);
v_name_556_ = lean_ctor_get(v_info_554_, 0);
v___x_557_ = l_Lean_Name_lt(v_name_555_, v_name_556_);
v___y_545_ = v___x_557_;
goto v___jp_544_;
}
default: 
{
goto v___jp_534_;
}
}
}
default: 
{
goto v___jp_534_;
}
}
}
v___jp_534_:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_k_533_, v___x_535_);
lean_dec(v_k_533_);
v_k_533_ = v___x_536_;
goto _start;
}
v___jp_538_:
{
lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_539_ = lean_array_fswap(v_as_531_, v_i_532_, v_k_533_);
v___x_540_ = lean_unsigned_to_nat(1u);
v___x_541_ = lean_nat_add(v_i_532_, v___x_540_);
lean_dec(v_i_532_);
v___x_542_ = lean_nat_add(v_k_533_, v___x_540_);
lean_dec(v_k_533_);
v_as_531_ = v___x_539_;
v_i_532_ = v___x_541_;
v_k_533_ = v___x_542_;
goto _start;
}
v___jp_544_:
{
if (v___y_545_ == 0)
{
goto v___jp_534_;
}
else
{
goto v___jp_538_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg___boxed(lean_object* v_hi_558_, lean_object* v_pivot_559_, lean_object* v_as_560_, lean_object* v_i_561_, lean_object* v_k_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_558_, v_pivot_559_, v_as_560_, v_i_561_, v_k_562_);
lean_dec_ref(v_pivot_559_);
lean_dec(v_hi_558_);
return v_res_563_;
}
}
uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(uint8_t v___x_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
switch(lean_obj_tag(v_x_565_))
{
case 0:
{
switch(lean_obj_tag(v_x_566_))
{
case 2:
{
return v___x_564_;
}
case 0:
{
lean_object* v_ctorName_567_; lean_object* v_ctorName_568_; uint8_t v___x_569_; 
v_ctorName_567_ = lean_ctor_get(v_x_565_, 0);
v_ctorName_568_ = lean_ctor_get(v_x_566_, 0);
v___x_569_ = l_Lean_Name_lt(v_ctorName_567_, v_ctorName_568_);
return v___x_569_;
}
default: 
{
uint8_t v___x_570_; 
v___x_570_ = 0;
return v___x_570_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_566_))
{
case 2:
{
return v___x_564_;
}
case 1:
{
lean_object* v_info_571_; lean_object* v_info_572_; lean_object* v_name_573_; lean_object* v_name_574_; uint8_t v___x_575_; 
v_info_571_ = lean_ctor_get(v_x_565_, 0);
v_info_572_ = lean_ctor_get(v_x_566_, 0);
v_name_573_ = lean_ctor_get(v_info_571_, 0);
v_name_574_ = lean_ctor_get(v_info_572_, 0);
v___x_575_ = l_Lean_Name_lt(v_name_573_, v_name_574_);
return v___x_575_;
}
default: 
{
uint8_t v___x_576_; 
v___x_576_ = 0;
return v___x_576_;
}
}
}
default: 
{
uint8_t v___x_577_; 
v___x_577_ = 0;
return v___x_577_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_564_ = stack[0].m_num;
lean_object* v_x_565_ = stack[1].m_obj;
lean_object* v_x_566_ = stack[2].m_obj;
uint8_t v_res_578_;
v_res_578_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_564_, v_x_565_, v_x_566_);
stack->m_num = v_res_578_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed(lean_object* v___x_579_, lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
uint8_t v___x_448__boxed_582_; uint8_t v_res_583_; lean_object* v_r_584_; 
v___x_448__boxed_582_ = lean_unbox(v___x_579_);
v_res_583_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_448__boxed_582_, v_x_580_, v_x_581_);
lean_dec_ref(v_x_581_);
lean_dec_ref(v_x_580_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(lean_object* v_n_585_, lean_object* v_as_586_, lean_object* v_lo_587_, lean_object* v_hi_588_){
_start:
{
lean_object* v___y_590_; uint8_t v___x_600_; 
v___x_600_ = lean_nat_dec_lt(v_lo_587_, v_hi_588_);
if (v___x_600_ == 0)
{
lean_dec(v_lo_587_);
return v_as_586_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v_mid_603_; lean_object* v___y_605_; lean_object* v___y_611_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_601_ = lean_nat_add(v_lo_587_, v_hi_588_);
v___x_602_ = lean_unsigned_to_nat(1u);
v_mid_603_ = lean_nat_shiftr(v___x_601_, v___x_602_);
lean_dec(v___x_601_);
v___x_616_ = lean_array_fget_borrowed(v_as_586_, v_mid_603_);
v___x_617_ = lean_array_fget_borrowed(v_as_586_, v_lo_587_);
v___x_618_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_600_, v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
v___y_611_ = v_as_586_;
goto v___jp_610_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = lean_array_fswap(v_as_586_, v_lo_587_, v_mid_603_);
v___y_611_ = v___x_619_;
goto v___jp_610_;
}
v___jp_604_:
{
lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_606_ = lean_array_fget_borrowed(v___y_605_, v_mid_603_);
v___x_607_ = lean_array_fget_borrowed(v___y_605_, v_hi_588_);
v___x_608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_600_, v___x_606_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_mid_603_);
v___y_590_ = v___y_605_;
goto v___jp_589_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = lean_array_fswap(v___y_605_, v_mid_603_, v_hi_588_);
lean_dec(v_mid_603_);
v___y_590_ = v___x_609_;
goto v___jp_589_;
}
}
v___jp_610_:
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_array_fget_borrowed(v___y_611_, v_hi_588_);
v___x_613_ = lean_array_fget_borrowed(v___y_611_, v_lo_587_);
v___x_614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_600_, v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
v___y_605_ = v___y_611_;
goto v___jp_604_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_fswap(v___y_611_, v_lo_587_, v_hi_588_);
v___y_605_ = v___x_615_;
goto v___jp_604_;
}
}
}
v___jp_589_:
{
lean_object* v_pivot_591_; lean_object* v___x_592_; lean_object* v_fst_593_; lean_object* v_snd_594_; uint8_t v___x_595_; 
v_pivot_591_ = lean_array_fget(v___y_590_, v_hi_588_);
lean_inc_n(v_lo_587_, 2);
v___x_592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_588_, v_pivot_591_, v___y_590_, v_lo_587_, v_lo_587_);
lean_dec(v_pivot_591_);
v_fst_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_fst_593_);
v_snd_594_ = lean_ctor_get(v___x_592_, 1);
lean_inc(v_snd_594_);
lean_dec_ref(v___x_592_);
v___x_595_ = lean_nat_dec_le(v_hi_588_, v_fst_593_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_596_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_585_, v_snd_594_, v_lo_587_, v_fst_593_);
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_fst_593_, v___x_597_);
lean_dec(v_fst_593_);
v_as_586_ = v___x_596_;
v_lo_587_ = v___x_598_;
goto _start;
}
else
{
lean_dec(v_fst_593_);
lean_dec(v_lo_587_);
return v_snd_594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___boxed(lean_object* v_n_620_, lean_object* v_as_621_, lean_object* v_lo_622_, lean_object* v_hi_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_620_, v_as_621_, v_lo_622_, v_hi_623_);
lean_dec(v_hi_623_);
lean_dec(v_n_620_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(lean_object* v_alts_625_){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = lean_array_get_size(v_alts_625_);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_nat_dec_eq(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___y_632_; uint8_t v___x_636_; 
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_sub(v___x_626_, v___x_629_);
v___x_636_ = lean_nat_dec_le(v___x_627_, v___x_630_);
if (v___x_636_ == 0)
{
lean_inc(v___x_630_);
v___y_632_ = v___x_630_;
goto v___jp_631_;
}
else
{
v___y_632_ = v___x_627_;
goto v___jp_631_;
}
v___jp_631_:
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_le(v___y_632_, v___x_630_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; 
lean_dec(v___x_630_);
lean_inc(v___y_632_);
v___x_634_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_626_, v_alts_625_, v___y_632_, v___y_632_);
lean_dec(v___y_632_);
return v___x_634_;
}
else
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_626_, v_alts_625_, v___y_632_, v___x_630_);
lean_dec(v___x_630_);
return v___x_635_;
}
}
}
else
{
return v_alts_625_;
}
}
}
lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(uint8_t v_pu_637_, lean_object* v_alts_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_638_);
return v___x_639_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_sortAlts_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_637_ = stack[0].m_num;
lean_object* v_alts_638_ = stack[1].m_obj;
lean_object* v_res_640_;
v_res_640_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(v_pu_637_, v_alts_638_);
stack->m_obj
 = v_res_640_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___boxed(lean_object* v_pu_641_, lean_object* v_alts_642_){
_start:
{
uint8_t v_pu_boxed_643_; lean_object* v_res_644_; 
v_pu_boxed_643_ = lean_unbox(v_pu_641_);
v_res_644_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(v_pu_boxed_643_, v_alts_642_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(lean_object* v_n_645_, lean_object* v_as_646_, lean_object* v_lo_647_, lean_object* v_hi_648_, lean_object* v_w_649_, lean_object* v_hlo_650_, lean_object* v_hhi_651_){
_start:
{
lean_object* v___x_652_; 
v___x_652_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_645_, v_as_646_, v_lo_647_, v_hi_648_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___boxed(lean_object* v_n_653_, lean_object* v_as_654_, lean_object* v_lo_655_, lean_object* v_hi_656_, lean_object* v_w_657_, lean_object* v_hlo_658_, lean_object* v_hhi_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(v_n_653_, v_as_654_, v_lo_655_, v_hi_656_, v_w_657_, v_hlo_658_, v_hhi_659_);
lean_dec(v_hi_656_);
lean_dec(v_n_653_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(lean_object* v_n_661_, lean_object* v_lo_662_, lean_object* v_hi_663_, lean_object* v_hhi_664_, lean_object* v_pivot_665_, lean_object* v_as_666_, lean_object* v_i_667_, lean_object* v_k_668_, lean_object* v_ilo_669_, lean_object* v_ik_670_, lean_object* v_w_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_663_, v_pivot_665_, v_as_666_, v_i_667_, v_k_668_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___boxed(lean_object* v_n_673_, lean_object* v_lo_674_, lean_object* v_hi_675_, lean_object* v_hhi_676_, lean_object* v_pivot_677_, lean_object* v_as_678_, lean_object* v_i_679_, lean_object* v_k_680_, lean_object* v_ilo_681_, lean_object* v_ik_682_, lean_object* v_w_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(v_n_673_, v_lo_674_, v_hi_675_, v_hhi_676_, v_pivot_677_, v_as_678_, v_i_679_, v_k_680_, v_ilo_681_, v_ik_682_, v_w_683_);
lean_dec_ref(v_pivot_677_);
lean_dec(v_hi_675_);
lean_dec(v_lo_674_);
lean_dec(v_n_673_);
return v_res_684_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(lean_object* v_x_685_, lean_object* v_x_686_){
_start:
{
if (lean_obj_tag(v_x_685_) == 0)
{
if (lean_obj_tag(v_x_686_) == 0)
{
uint8_t v___x_687_; 
v___x_687_ = 1;
return v___x_687_;
}
else
{
uint8_t v___x_688_; 
v___x_688_ = 0;
return v___x_688_;
}
}
else
{
if (lean_obj_tag(v_x_686_) == 0)
{
uint8_t v___x_689_; 
v___x_689_ = 0;
return v___x_689_;
}
else
{
lean_object* v_val_690_; lean_object* v_val_691_; uint8_t v___x_692_; 
v_val_690_ = lean_ctor_get(v_x_685_, 0);
v_val_691_ = lean_ctor_get(v_x_686_, 0);
v___x_692_ = lean_nat_dec_eq(v_val_690_, v_val_691_);
return v___x_692_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_685_ = stack[0].m_obj;
lean_object* v_x_686_ = stack[1].m_obj;
uint8_t v_res_693_;
v_res_693_ = l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(v_x_685_, v_x_686_);
stack->m_num = v_res_693_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3___boxed(lean_object* v_x_694_, lean_object* v_x_695_){
_start:
{
uint8_t v_res_696_; lean_object* v_r_697_; 
v_res_696_ = l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(v_x_694_, v_x_695_);
lean_dec(v_x_695_);
lean_dec(v_x_694_);
v_r_697_ = lean_box(v_res_696_);
return v_r_697_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(uint8_t v_pu_701_, lean_object* v_as_702_, size_t v_sz_703_, size_t v_i_704_, lean_object* v_b_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_a_708_; uint8_t v___x_712_; 
v___x_712_ = lean_usize_dec_lt(v_i_704_, v_sz_703_);
if (v___x_712_ == 0)
{
return v_b_705_;
}
else
{
lean_object* v_snd_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_801_; 
v_snd_713_ = lean_ctor_get(v_b_705_, 1);
v_isSharedCheck_801_ = !lean_is_exclusive(v_b_705_);
if (v_isSharedCheck_801_ == 0)
{
lean_object* v_unused_802_; 
v_unused_802_ = lean_ctor_get(v_b_705_, 0);
lean_dec(v_unused_802_);
v___x_715_ = v_b_705_;
v_isShared_716_ = v_isSharedCheck_801_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_snd_713_);
lean_dec(v_b_705_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_801_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_array_717_; lean_object* v_start_718_; lean_object* v_stop_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_array_717_ = lean_ctor_get(v_snd_713_, 0);
v_start_718_ = lean_ctor_get(v_snd_713_, 1);
v_stop_719_ = lean_ctor_get(v_snd_713_, 2);
v___x_720_ = lean_box(0);
v___x_721_ = lean_nat_dec_lt(v_start_718_, v_stop_719_);
if (v___x_721_ == 0)
{
lean_object* v___x_723_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_720_);
v___x_723_ = v___x_715_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v_snd_713_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
else
{
lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_797_; 
lean_inc(v_stop_719_);
lean_inc(v_start_718_);
lean_inc_ref(v_array_717_);
v_isSharedCheck_797_ = !lean_is_exclusive(v_snd_713_);
if (v_isSharedCheck_797_ == 0)
{
lean_object* v_unused_798_; lean_object* v_unused_799_; lean_object* v_unused_800_; 
v_unused_798_ = lean_ctor_get(v_snd_713_, 2);
lean_dec(v_unused_798_);
v_unused_799_ = lean_ctor_get(v_snd_713_, 1);
lean_dec(v_unused_799_);
v_unused_800_ = lean_ctor_get(v_snd_713_, 0);
lean_dec(v_unused_800_);
v___x_726_ = v_snd_713_;
v_isShared_727_ = v_isSharedCheck_797_;
goto v_resetjp_725_;
}
else
{
lean_dec(v_snd_713_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_797_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v_a_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v_a_728_ = lean_array_uget_borrowed(v_as_702_, v_i_704_);
v___x_729_ = lean_array_fget(v_array_717_, v_start_718_);
v___x_730_ = lean_unsigned_to_nat(1u);
v___x_731_ = lean_nat_add(v_start_718_, v___x_730_);
lean_dec(v_start_718_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v___x_731_);
v___x_733_ = v___x_726_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_array_717_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_796_, 2, v_stop_719_);
v___x_733_ = v_reuseFailAlloc_796_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
uint8_t v___y_735_; 
switch(lean_obj_tag(v_a_728_))
{
case 0:
{
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_ctorName_744_; lean_object* v_params_745_; lean_object* v_code_746_; lean_object* v_ctorName_747_; lean_object* v_params_748_; lean_object* v_code_749_; uint8_t v___x_750_; 
v_ctorName_744_ = lean_ctor_get(v_a_728_, 0);
v_params_745_ = lean_ctor_get(v_a_728_, 1);
v_code_746_ = lean_ctor_get(v_a_728_, 2);
v_ctorName_747_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_ctorName_747_);
v_params_748_ = lean_ctor_get(v___x_729_, 1);
lean_inc_ref(v_params_748_);
v_code_749_ = lean_ctor_get(v___x_729_, 2);
lean_inc_ref(v_code_749_);
lean_dec_ref_known(v___x_729_, 3);
v___x_750_ = lean_name_eq(v_ctorName_744_, v_ctorName_747_);
lean_dec(v_ctorName_747_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec_ref(v_code_749_);
lean_dec_ref(v_params_748_);
lean_del_object(v___x_715_);
v___x_751_ = lean_box(v___x_750_);
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_733_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_754_ = lean_array_get_size(v_params_748_);
v___x_755_ = lean_array_get_size(v_params_745_);
v___x_756_ = lean_nat_dec_eq(v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
lean_dec_ref(v_code_749_);
lean_dec_ref(v_params_748_);
v___y_735_ = v___x_756_;
goto v___jp_734_;
}
else
{
lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_706_);
lean_inc_ref(v_code_746_);
v___x_758_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_701_, v_code_746_, v_code_749_, v_params_745_, v_params_748_, v___x_757_, v___y_706_);
lean_dec_ref(v_params_748_);
if (v___x_758_ == 0)
{
v___y_735_ = v___x_758_;
goto v___jp_734_;
}
else
{
lean_object* v___x_759_; 
lean_del_object(v___x_715_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v___x_720_);
lean_ctor_set(v___x_759_, 1, v___x_733_);
v_a_708_ = v___x_759_;
goto v___jp_707_;
}
}
}
}
else
{
lean_dec(v___x_729_);
lean_del_object(v___x_715_);
goto v___jp_741_;
}
}
case 1:
{
lean_del_object(v___x_715_);
if (lean_obj_tag(v___x_729_) == 1)
{
lean_object* v_info_760_; lean_object* v_code_761_; lean_object* v_info_762_; lean_object* v_code_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_782_; 
v_info_760_ = lean_ctor_get(v_a_728_, 0);
v_code_761_ = lean_ctor_get(v_a_728_, 1);
v_info_762_ = lean_ctor_get(v___x_729_, 0);
v_code_763_ = lean_ctor_get(v___x_729_, 1);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_782_ == 0)
{
v___x_765_ = v___x_729_;
v_isShared_766_ = v_isSharedCheck_782_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_code_763_);
lean_inc(v_info_762_);
lean_dec(v___x_729_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_782_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
uint8_t v___x_767_; 
v___x_767_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_info_760_, v_info_762_);
lean_dec_ref(v_info_762_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_771_; 
lean_dec_ref(v_code_763_);
v___x_768_ = lean_box(v___x_767_);
v___x_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 0);
lean_ctor_set(v___x_765_, 1, v___x_733_);
lean_ctor_set(v___x_765_, 0, v___x_769_);
v___x_771_ = v___x_765_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___x_733_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
else
{
uint8_t v___x_773_; 
lean_inc(v___y_706_);
lean_inc_ref(v_code_761_);
v___x_773_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_701_, v_code_761_, v_code_763_, v___y_706_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v___x_774_ = lean_box(v___x_773_);
v___x_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 0);
lean_ctor_set(v___x_765_, 1, v___x_733_);
lean_ctor_set(v___x_765_, 0, v___x_775_);
v___x_777_ = v___x_765_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_733_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
else
{
lean_object* v___x_780_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set_tag(v___x_765_, 0);
lean_ctor_set(v___x_765_, 1, v___x_733_);
lean_ctor_set(v___x_765_, 0, v___x_720_);
v___x_780_ = v___x_765_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v___x_733_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
v_a_708_ = v___x_780_;
goto v___jp_707_;
}
}
}
}
}
else
{
lean_dec(v___x_729_);
goto v___jp_741_;
}
}
default: 
{
lean_del_object(v___x_715_);
if (lean_obj_tag(v___x_729_) == 2)
{
lean_object* v_code_783_; lean_object* v_code_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_795_; 
v_code_783_ = lean_ctor_get(v_a_728_, 0);
v_code_784_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_795_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_795_ == 0)
{
v___x_786_ = v___x_729_;
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_code_784_);
lean_dec(v___x_729_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_795_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
uint8_t v___x_788_; 
lean_inc(v___y_706_);
lean_inc_ref(v_code_783_);
v___x_788_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_701_, v_code_783_, v_code_784_, v___y_706_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; lean_object* v___x_791_; 
v___x_789_ = lean_box(v___x_788_);
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 1);
lean_ctor_set(v___x_786_, 0, v___x_789_);
v___x_791_ = v___x_786_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_789_);
v___x_791_ = v_reuseFailAlloc_793_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
lean_object* v___x_792_; 
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_791_);
lean_ctor_set(v___x_792_, 1, v___x_733_);
return v___x_792_;
}
}
else
{
lean_object* v___x_794_; 
lean_del_object(v___x_786_);
v___x_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_794_, 0, v___x_720_);
lean_ctor_set(v___x_794_, 1, v___x_733_);
v_a_708_ = v___x_794_;
goto v___jp_707_;
}
}
}
else
{
lean_dec(v___x_729_);
goto v___jp_741_;
}
}
}
v___jp_734_:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_739_; 
v___x_736_ = lean_box(v___y_735_);
v___x_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v___x_733_);
lean_ctor_set(v___x_715_, 0, v___x_737_);
v___x_739_ = v___x_715_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_737_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v___x_733_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
v___jp_741_:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0));
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_733_);
return v___x_743_;
}
}
}
}
}
}
v___jp_707_:
{
size_t v___x_709_; size_t v___x_710_; 
v___x_709_ = ((size_t)1ULL);
v___x_710_ = lean_usize_add(v_i_704_, v___x_709_);
v_i_704_ = v___x_710_;
v_b_705_ = v_a_708_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_701_ = stack[0].m_num;
lean_object* v_as_702_ = stack[1].m_obj;
size_t v_sz_703_ = stack[2].m_num;
size_t v_i_704_ = stack[3].m_num;
lean_object* v_b_705_ = stack[4].m_obj;
lean_object* v___y_706_ = stack[5].m_obj;
lean_object* v_res_803_;
v_res_803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_701_, v_as_702_, v_sz_703_, v_i_704_, v_b_705_, v___y_706_);
stack->m_obj
 = v_res_803_;
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(uint8_t v_pu_804_, lean_object* v_alts_u2081_805_, lean_object* v_alts_u2082_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_808_ = lean_array_get_size(v_alts_u2081_805_);
v___x_809_ = lean_array_get_size(v_alts_u2082_806_);
v___x_810_ = lean_nat_dec_eq(v___x_808_, v___x_809_);
if (v___x_810_ == 0)
{
lean_dec_ref(v_alts_u2082_806_);
lean_dec_ref(v_alts_u2081_805_);
return v___x_810_;
}
else
{
lean_object* v_alts_u2081_811_; lean_object* v_alts_u2082_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; size_t v_sz_818_; size_t v___x_819_; lean_object* v___x_820_; lean_object* v_fst_821_; 
v_alts_u2081_811_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2081_805_);
v_alts_u2082_812_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2082_806_);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_array_get_size(v_alts_u2082_812_);
v___x_815_ = l_Array_toSubarray___redArg(v_alts_u2082_812_, v___x_813_, v___x_814_);
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v___x_815_);
v_sz_818_ = lean_array_size(v_alts_u2081_811_);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_804_, v_alts_u2081_811_, v_sz_818_, v___x_819_, v___x_817_, v_a_807_);
lean_dec_ref(v_alts_u2081_811_);
v_fst_821_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_fst_821_);
lean_dec_ref(v___x_820_);
if (lean_obj_tag(v_fst_821_) == 0)
{
return v___x_810_;
}
else
{
lean_object* v_val_822_; uint8_t v___x_823_; 
v_val_822_ = lean_ctor_get(v_fst_821_, 0);
lean_inc(v_val_822_);
lean_dec_ref_known(v_fst_821_, 1);
v___x_823_ = lean_unbox(v_val_822_);
lean_dec(v_val_822_);
return v___x_823_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_804_ = stack[0].m_num;
lean_object* v_alts_u2081_805_ = stack[1].m_obj;
lean_object* v_alts_u2082_806_ = stack[2].m_obj;
lean_object* v_a_807_ = stack[3].m_obj;
uint8_t v_res_824_;
v_res_824_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_804_, v_alts_u2081_805_, v_alts_u2082_806_, v_a_807_);
stack->m_num = v_res_824_;
}
uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqv(uint8_t v_pu_825_, lean_object* v_code_u2081_826_, lean_object* v_code_u2082_827_, lean_object* v_a_828_){
_start:
{
switch(lean_obj_tag(v_code_u2081_826_))
{
case 0:
{
if (lean_obj_tag(v_code_u2082_827_) == 0)
{
lean_object* v_decl_829_; lean_object* v_decl_830_; lean_object* v_k_831_; lean_object* v_k_832_; lean_object* v_fvarId_833_; lean_object* v_type_834_; lean_object* v_value_835_; lean_object* v_fvarId_836_; lean_object* v_type_837_; lean_object* v_value_838_; uint8_t v___x_839_; 
v_decl_829_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc_ref(v_decl_829_);
v_decl_830_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc_ref(v_decl_830_);
v_k_831_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc_ref(v_k_831_);
lean_dec_ref_known(v_code_u2081_826_, 2);
v_k_832_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc_ref(v_k_832_);
lean_dec_ref_known(v_code_u2082_827_, 2);
v_fvarId_833_ = lean_ctor_get(v_decl_829_, 0);
lean_inc(v_fvarId_833_);
v_type_834_ = lean_ctor_get(v_decl_829_, 2);
lean_inc_ref(v_type_834_);
v_value_835_ = lean_ctor_get(v_decl_829_, 3);
lean_inc(v_value_835_);
lean_dec_ref(v_decl_829_);
v_fvarId_836_ = lean_ctor_get(v_decl_830_, 0);
lean_inc(v_fvarId_836_);
v_type_837_ = lean_ctor_get(v_decl_830_, 2);
lean_inc_ref(v_type_837_);
v_value_838_ = lean_ctor_get(v_decl_830_, 3);
lean_inc(v_value_838_);
lean_dec_ref(v_decl_830_);
v___x_839_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_834_, v_type_837_, v_a_828_);
lean_dec_ref(v_type_837_);
lean_dec_ref(v_type_834_);
if (v___x_839_ == 0)
{
lean_dec(v_value_838_);
lean_dec(v_fvarId_836_);
lean_dec(v_value_835_);
lean_dec(v_fvarId_833_);
lean_dec_ref(v_k_832_);
lean_dec_ref(v_k_831_);
lean_dec(v_a_828_);
return v___x_839_;
}
else
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_825_, v_value_835_, v_value_838_, v_a_828_);
lean_dec(v_value_835_);
if (v___x_840_ == 0)
{
lean_dec(v_fvarId_836_);
lean_dec(v_fvarId_833_);
lean_dec_ref(v_k_832_);
lean_dec_ref(v_k_831_);
lean_dec(v_a_828_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_836_, v_fvarId_833_, v_a_828_);
v_code_u2081_826_ = v_k_831_;
v_code_u2082_827_ = v_k_832_;
v_a_828_ = v___x_841_;
goto _start;
}
}
}
else
{
uint8_t v___x_843_; 
lean_dec_ref_known(v_code_u2081_826_, 2);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_843_ = 0;
return v___x_843_;
}
}
case 1:
{
if (lean_obj_tag(v_code_u2082_827_) == 1)
{
lean_object* v_decl_844_; lean_object* v_decl_845_; lean_object* v_k_846_; lean_object* v_k_847_; lean_object* v_fvarId_848_; lean_object* v_params_849_; lean_object* v_type_850_; lean_object* v_value_851_; lean_object* v_fvarId_852_; lean_object* v_params_853_; lean_object* v_type_854_; lean_object* v_value_855_; uint8_t v___x_856_; 
v_decl_844_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc_ref(v_decl_844_);
v_decl_845_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc_ref(v_decl_845_);
v_k_846_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc_ref(v_k_846_);
lean_dec_ref_known(v_code_u2081_826_, 2);
v_k_847_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc_ref(v_k_847_);
lean_dec_ref_known(v_code_u2082_827_, 2);
v_fvarId_848_ = lean_ctor_get(v_decl_844_, 0);
lean_inc(v_fvarId_848_);
v_params_849_ = lean_ctor_get(v_decl_844_, 2);
lean_inc_ref(v_params_849_);
v_type_850_ = lean_ctor_get(v_decl_844_, 3);
lean_inc_ref(v_type_850_);
v_value_851_ = lean_ctor_get(v_decl_844_, 4);
lean_inc_ref(v_value_851_);
lean_dec_ref(v_decl_844_);
v_fvarId_852_ = lean_ctor_get(v_decl_845_, 0);
lean_inc(v_fvarId_852_);
v_params_853_ = lean_ctor_get(v_decl_845_, 2);
lean_inc_ref(v_params_853_);
v_type_854_ = lean_ctor_get(v_decl_845_, 3);
lean_inc_ref(v_type_854_);
v_value_855_ = lean_ctor_get(v_decl_845_, 4);
lean_inc_ref(v_value_855_);
lean_dec_ref(v_decl_845_);
v___x_856_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_850_, v_type_854_, v_a_828_);
lean_dec_ref(v_type_854_);
lean_dec_ref(v_type_850_);
if (v___x_856_ == 0)
{
lean_dec_ref(v_value_855_);
lean_dec_ref(v_params_853_);
lean_dec(v_fvarId_852_);
lean_dec_ref(v_value_851_);
lean_dec_ref(v_params_849_);
lean_dec(v_fvarId_848_);
lean_dec_ref(v_k_847_);
lean_dec_ref(v_k_846_);
lean_dec(v_a_828_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_857_ = lean_array_get_size(v_params_853_);
v___x_858_ = lean_array_get_size(v_params_849_);
v___x_859_ = lean_nat_dec_eq(v___x_857_, v___x_858_);
if (v___x_859_ == 0)
{
lean_dec_ref(v_value_855_);
lean_dec_ref(v_params_853_);
lean_dec(v_fvarId_852_);
lean_dec_ref(v_value_851_);
lean_dec_ref(v_params_849_);
lean_dec(v_fvarId_848_);
lean_dec_ref(v_k_847_);
lean_dec_ref(v_k_846_);
lean_dec(v_a_828_);
return v___x_859_;
}
else
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_828_);
v___x_861_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_825_, v_value_851_, v_value_855_, v_params_849_, v_params_853_, v___x_860_, v_a_828_);
lean_dec_ref(v_params_853_);
lean_dec_ref(v_params_849_);
if (v___x_861_ == 0)
{
lean_dec(v_fvarId_852_);
lean_dec(v_fvarId_848_);
lean_dec_ref(v_k_847_);
lean_dec_ref(v_k_846_);
lean_dec(v_a_828_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_852_, v_fvarId_848_, v_a_828_);
v_code_u2081_826_ = v_k_846_;
v_code_u2082_827_ = v_k_847_;
v_a_828_ = v___x_862_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_864_; 
lean_dec_ref_known(v_code_u2081_826_, 2);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_864_ = 0;
return v___x_864_;
}
}
case 2:
{
if (lean_obj_tag(v_code_u2082_827_) == 2)
{
lean_object* v_decl_865_; lean_object* v_decl_866_; lean_object* v_k_867_; lean_object* v_k_868_; lean_object* v_fvarId_869_; lean_object* v_params_870_; lean_object* v_type_871_; lean_object* v_value_872_; lean_object* v_fvarId_873_; lean_object* v_params_874_; lean_object* v_type_875_; lean_object* v_value_876_; uint8_t v___x_877_; 
v_decl_865_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc_ref(v_decl_865_);
v_decl_866_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc_ref(v_decl_866_);
v_k_867_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc_ref(v_k_867_);
lean_dec_ref_known(v_code_u2081_826_, 2);
v_k_868_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc_ref(v_k_868_);
lean_dec_ref_known(v_code_u2082_827_, 2);
v_fvarId_869_ = lean_ctor_get(v_decl_865_, 0);
lean_inc(v_fvarId_869_);
v_params_870_ = lean_ctor_get(v_decl_865_, 2);
lean_inc_ref(v_params_870_);
v_type_871_ = lean_ctor_get(v_decl_865_, 3);
lean_inc_ref(v_type_871_);
v_value_872_ = lean_ctor_get(v_decl_865_, 4);
lean_inc_ref(v_value_872_);
lean_dec_ref(v_decl_865_);
v_fvarId_873_ = lean_ctor_get(v_decl_866_, 0);
lean_inc(v_fvarId_873_);
v_params_874_ = lean_ctor_get(v_decl_866_, 2);
lean_inc_ref(v_params_874_);
v_type_875_ = lean_ctor_get(v_decl_866_, 3);
lean_inc_ref(v_type_875_);
v_value_876_ = lean_ctor_get(v_decl_866_, 4);
lean_inc_ref(v_value_876_);
lean_dec_ref(v_decl_866_);
v___x_877_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_871_, v_type_875_, v_a_828_);
lean_dec_ref(v_type_875_);
lean_dec_ref(v_type_871_);
if (v___x_877_ == 0)
{
lean_dec_ref(v_value_876_);
lean_dec_ref(v_params_874_);
lean_dec(v_fvarId_873_);
lean_dec_ref(v_value_872_);
lean_dec_ref(v_params_870_);
lean_dec(v_fvarId_869_);
lean_dec_ref(v_k_868_);
lean_dec_ref(v_k_867_);
lean_dec(v_a_828_);
return v___x_877_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_878_ = lean_array_get_size(v_params_874_);
v___x_879_ = lean_array_get_size(v_params_870_);
v___x_880_ = lean_nat_dec_eq(v___x_878_, v___x_879_);
if (v___x_880_ == 0)
{
lean_dec_ref(v_value_876_);
lean_dec_ref(v_params_874_);
lean_dec(v_fvarId_873_);
lean_dec_ref(v_value_872_);
lean_dec_ref(v_params_870_);
lean_dec(v_fvarId_869_);
lean_dec_ref(v_k_868_);
lean_dec_ref(v_k_867_);
lean_dec(v_a_828_);
return v___x_880_;
}
else
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_828_);
v___x_882_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_825_, v_value_872_, v_value_876_, v_params_870_, v_params_874_, v___x_881_, v_a_828_);
lean_dec_ref(v_params_874_);
lean_dec_ref(v_params_870_);
if (v___x_882_ == 0)
{
lean_dec(v_fvarId_873_);
lean_dec(v_fvarId_869_);
lean_dec_ref(v_k_868_);
lean_dec_ref(v_k_867_);
lean_dec(v_a_828_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; 
v___x_883_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_873_, v_fvarId_869_, v_a_828_);
v_code_u2081_826_ = v_k_867_;
v_code_u2082_827_ = v_k_868_;
v_a_828_ = v___x_883_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_885_; 
lean_dec_ref_known(v_code_u2081_826_, 2);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_885_ = 0;
return v___x_885_;
}
}
case 3:
{
if (lean_obj_tag(v_code_u2082_827_) == 3)
{
lean_object* v_fvarId_886_; lean_object* v_args_887_; lean_object* v_fvarId_888_; lean_object* v_args_889_; uint8_t v___x_890_; 
v_fvarId_886_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc(v_fvarId_886_);
v_args_887_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc_ref(v_args_887_);
lean_dec_ref_known(v_code_u2081_826_, 2);
v_fvarId_888_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc(v_fvarId_888_);
v_args_889_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc_ref(v_args_889_);
lean_dec_ref_known(v_code_u2082_827_, 2);
v___x_890_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_886_, v_fvarId_888_, v_a_828_);
lean_dec(v_fvarId_888_);
lean_dec(v_fvarId_886_);
if (v___x_890_ == 0)
{
lean_dec_ref(v_args_889_);
lean_dec_ref(v_args_887_);
lean_dec(v_a_828_);
return v___x_890_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_825_, v_args_887_, v_args_889_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_args_887_);
return v___x_891_;
}
}
else
{
uint8_t v___x_892_; 
lean_dec_ref_known(v_code_u2081_826_, 2);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_892_ = 0;
return v___x_892_;
}
}
case 4:
{
if (lean_obj_tag(v_code_u2082_827_) == 4)
{
lean_object* v_cases_893_; lean_object* v_cases_894_; lean_object* v_resultType_895_; lean_object* v_discr_896_; lean_object* v_alts_897_; lean_object* v_resultType_898_; lean_object* v_discr_899_; lean_object* v_alts_900_; uint8_t v___x_901_; 
v_cases_893_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc_ref(v_cases_893_);
lean_dec_ref_known(v_code_u2081_826_, 1);
v_cases_894_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc_ref(v_cases_894_);
lean_dec_ref_known(v_code_u2082_827_, 1);
v_resultType_895_ = lean_ctor_get(v_cases_893_, 1);
lean_inc_ref(v_resultType_895_);
v_discr_896_ = lean_ctor_get(v_cases_893_, 2);
lean_inc(v_discr_896_);
v_alts_897_ = lean_ctor_get(v_cases_893_, 3);
lean_inc_ref(v_alts_897_);
lean_dec_ref(v_cases_893_);
v_resultType_898_ = lean_ctor_get(v_cases_894_, 1);
lean_inc_ref(v_resultType_898_);
v_discr_899_ = lean_ctor_get(v_cases_894_, 2);
lean_inc(v_discr_899_);
v_alts_900_ = lean_ctor_get(v_cases_894_, 3);
lean_inc_ref(v_alts_900_);
lean_dec_ref(v_cases_894_);
v___x_901_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_discr_896_, v_discr_899_, v_a_828_);
lean_dec(v_discr_899_);
lean_dec(v_discr_896_);
if (v___x_901_ == 0)
{
lean_dec_ref(v_alts_900_);
lean_dec_ref(v_resultType_898_);
lean_dec_ref(v_alts_897_);
lean_dec_ref(v_resultType_895_);
lean_dec(v_a_828_);
return v___x_901_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_resultType_895_, v_resultType_898_, v_a_828_);
lean_dec_ref(v_resultType_898_);
lean_dec_ref(v_resultType_895_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_alts_900_);
lean_dec_ref(v_alts_897_);
lean_dec(v_a_828_);
return v___x_902_;
}
else
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_825_, v_alts_897_, v_alts_900_, v_a_828_);
lean_dec(v_a_828_);
return v___x_903_;
}
}
}
else
{
uint8_t v___x_904_; 
lean_dec_ref_known(v_code_u2081_826_, 1);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_904_ = 0;
return v___x_904_;
}
}
case 5:
{
if (lean_obj_tag(v_code_u2082_827_) == 5)
{
lean_object* v_fvarId_905_; lean_object* v_fvarId_906_; uint8_t v___x_907_; 
v_fvarId_905_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc(v_fvarId_905_);
lean_dec_ref_known(v_code_u2081_826_, 1);
v_fvarId_906_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc(v_fvarId_906_);
lean_dec_ref_known(v_code_u2082_827_, 1);
v___x_907_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_905_, v_fvarId_906_, v_a_828_);
lean_dec(v_a_828_);
lean_dec(v_fvarId_906_);
lean_dec(v_fvarId_905_);
return v___x_907_;
}
else
{
uint8_t v___x_908_; 
lean_dec_ref_known(v_code_u2081_826_, 1);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_908_ = 0;
return v___x_908_;
}
}
case 6:
{
if (lean_obj_tag(v_code_u2082_827_) == 6)
{
lean_object* v_type_909_; lean_object* v_type_910_; uint8_t v___x_911_; 
v_type_909_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc_ref(v_type_909_);
lean_dec_ref_known(v_code_u2081_826_, 1);
v_type_910_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc_ref(v_type_910_);
lean_dec_ref_known(v_code_u2082_827_, 1);
v___x_911_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_909_, v_type_910_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_type_910_);
lean_dec_ref(v_type_909_);
return v___x_911_;
}
else
{
uint8_t v___x_912_; 
lean_dec_ref_known(v_code_u2081_826_, 1);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_912_ = 0;
return v___x_912_;
}
}
case 7:
{
if (lean_obj_tag(v_code_u2082_827_) == 7)
{
lean_object* v_fvarId_913_; lean_object* v_i_914_; lean_object* v_y_915_; lean_object* v_k_916_; lean_object* v_fvarId_917_; lean_object* v_i_918_; lean_object* v_y_919_; lean_object* v_k_920_; uint8_t v___x_921_; 
v_fvarId_913_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc(v_fvarId_913_);
v_i_914_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc(v_i_914_);
v_y_915_ = lean_ctor_get(v_code_u2081_826_, 2);
lean_inc(v_y_915_);
v_k_916_ = lean_ctor_get(v_code_u2081_826_, 3);
lean_inc_ref(v_k_916_);
lean_dec_ref_known(v_code_u2081_826_, 4);
v_fvarId_917_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc(v_fvarId_917_);
v_i_918_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc(v_i_918_);
v_y_919_ = lean_ctor_get(v_code_u2082_827_, 2);
lean_inc(v_y_919_);
v_k_920_ = lean_ctor_get(v_code_u2082_827_, 3);
lean_inc_ref(v_k_920_);
lean_dec_ref_known(v_code_u2082_827_, 4);
v___x_921_ = lean_nat_dec_eq(v_i_914_, v_i_918_);
lean_dec(v_i_918_);
lean_dec(v_i_914_);
if (v___x_921_ == 0)
{
lean_dec_ref(v_k_920_);
lean_dec(v_y_919_);
lean_dec(v_fvarId_917_);
lean_dec_ref(v_k_916_);
lean_dec(v_y_915_);
lean_dec(v_fvarId_913_);
lean_dec(v_a_828_);
return v___x_921_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_913_, v_fvarId_917_, v_a_828_);
lean_dec(v_fvarId_917_);
lean_dec(v_fvarId_913_);
if (v___x_922_ == 0)
{
lean_dec_ref(v_k_920_);
lean_dec(v_y_919_);
lean_dec_ref(v_k_916_);
lean_dec(v_y_915_);
lean_dec(v_a_828_);
return v___x_922_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_y_915_, v_y_919_, v_a_828_);
lean_dec(v_y_919_);
lean_dec(v_y_915_);
if (v___x_923_ == 0)
{
lean_dec_ref(v_k_920_);
lean_dec_ref(v_k_916_);
lean_dec(v_a_828_);
return v___x_923_;
}
else
{
v_code_u2081_826_ = v_k_916_;
v_code_u2082_827_ = v_k_920_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_925_; 
lean_dec_ref_known(v_code_u2081_826_, 4);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_925_ = 0;
return v___x_925_;
}
}
case 8:
{
if (lean_obj_tag(v_code_u2082_827_) == 8)
{
lean_object* v_fvarId_926_; lean_object* v_i_927_; lean_object* v_y_928_; lean_object* v_k_929_; lean_object* v_fvarId_930_; lean_object* v_i_931_; lean_object* v_y_932_; lean_object* v_k_933_; uint8_t v___x_934_; 
v_fvarId_926_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc(v_fvarId_926_);
v_i_927_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc(v_i_927_);
v_y_928_ = lean_ctor_get(v_code_u2081_826_, 2);
lean_inc(v_y_928_);
v_k_929_ = lean_ctor_get(v_code_u2081_826_, 3);
lean_inc_ref(v_k_929_);
lean_dec_ref_known(v_code_u2081_826_, 4);
v_fvarId_930_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc(v_fvarId_930_);
v_i_931_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc(v_i_931_);
v_y_932_ = lean_ctor_get(v_code_u2082_827_, 2);
lean_inc(v_y_932_);
v_k_933_ = lean_ctor_get(v_code_u2082_827_, 3);
lean_inc_ref(v_k_933_);
lean_dec_ref_known(v_code_u2082_827_, 4);
v___x_934_ = lean_nat_dec_eq(v_i_927_, v_i_931_);
lean_dec(v_i_931_);
lean_dec(v_i_927_);
if (v___x_934_ == 0)
{
lean_dec_ref(v_k_933_);
lean_dec(v_y_932_);
lean_dec(v_fvarId_930_);
lean_dec_ref(v_k_929_);
lean_dec(v_y_928_);
lean_dec(v_fvarId_926_);
lean_dec(v_a_828_);
return v___x_934_;
}
else
{
uint8_t v___x_935_; 
v___x_935_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_926_, v_fvarId_930_, v_a_828_);
lean_dec(v_fvarId_930_);
lean_dec(v_fvarId_926_);
if (v___x_935_ == 0)
{
lean_dec_ref(v_k_933_);
lean_dec(v_y_932_);
lean_dec_ref(v_k_929_);
lean_dec(v_y_928_);
lean_dec(v_a_828_);
return v___x_935_;
}
else
{
uint8_t v___x_936_; 
v___x_936_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_928_, v_y_932_, v_a_828_);
lean_dec(v_y_932_);
lean_dec(v_y_928_);
if (v___x_936_ == 0)
{
lean_dec_ref(v_k_933_);
lean_dec_ref(v_k_929_);
lean_dec(v_a_828_);
return v___x_936_;
}
else
{
v_code_u2081_826_ = v_k_929_;
v_code_u2082_827_ = v_k_933_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_938_; 
lean_dec_ref_known(v_code_u2081_826_, 4);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_938_ = 0;
return v___x_938_;
}
}
case 9:
{
if (lean_obj_tag(v_code_u2082_827_) == 9)
{
lean_object* v_fvarId_939_; lean_object* v_i_940_; lean_object* v_offset_941_; lean_object* v_y_942_; lean_object* v_ty_943_; lean_object* v_k_944_; lean_object* v_fvarId_945_; lean_object* v_i_946_; lean_object* v_offset_947_; lean_object* v_y_948_; lean_object* v_ty_949_; lean_object* v_k_950_; uint8_t v___x_951_; 
v_fvarId_939_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc(v_fvarId_939_);
v_i_940_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc(v_i_940_);
v_offset_941_ = lean_ctor_get(v_code_u2081_826_, 2);
lean_inc(v_offset_941_);
v_y_942_ = lean_ctor_get(v_code_u2081_826_, 3);
lean_inc(v_y_942_);
v_ty_943_ = lean_ctor_get(v_code_u2081_826_, 4);
lean_inc_ref(v_ty_943_);
v_k_944_ = lean_ctor_get(v_code_u2081_826_, 5);
lean_inc_ref(v_k_944_);
lean_dec_ref_known(v_code_u2081_826_, 6);
v_fvarId_945_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc(v_fvarId_945_);
v_i_946_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc(v_i_946_);
v_offset_947_ = lean_ctor_get(v_code_u2082_827_, 2);
lean_inc(v_offset_947_);
v_y_948_ = lean_ctor_get(v_code_u2082_827_, 3);
lean_inc(v_y_948_);
v_ty_949_ = lean_ctor_get(v_code_u2082_827_, 4);
lean_inc_ref(v_ty_949_);
v_k_950_ = lean_ctor_get(v_code_u2082_827_, 5);
lean_inc_ref(v_k_950_);
lean_dec_ref_known(v_code_u2082_827_, 6);
v___x_951_ = lean_nat_dec_eq(v_i_940_, v_i_946_);
lean_dec(v_i_946_);
lean_dec(v_i_940_);
if (v___x_951_ == 0)
{
lean_dec_ref(v_k_950_);
lean_dec_ref(v_ty_949_);
lean_dec(v_y_948_);
lean_dec(v_offset_947_);
lean_dec(v_fvarId_945_);
lean_dec_ref(v_k_944_);
lean_dec_ref(v_ty_943_);
lean_dec(v_y_942_);
lean_dec(v_offset_941_);
lean_dec(v_fvarId_939_);
lean_dec(v_a_828_);
return v___x_951_;
}
else
{
uint8_t v___x_952_; 
v___x_952_ = lean_nat_dec_eq(v_offset_941_, v_offset_947_);
lean_dec(v_offset_947_);
lean_dec(v_offset_941_);
if (v___x_952_ == 0)
{
lean_dec_ref(v_k_950_);
lean_dec_ref(v_ty_949_);
lean_dec(v_y_948_);
lean_dec(v_fvarId_945_);
lean_dec_ref(v_k_944_);
lean_dec_ref(v_ty_943_);
lean_dec(v_y_942_);
lean_dec(v_fvarId_939_);
lean_dec(v_a_828_);
return v___x_952_;
}
else
{
uint8_t v___x_953_; 
v___x_953_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_939_, v_fvarId_945_, v_a_828_);
lean_dec(v_fvarId_945_);
lean_dec(v_fvarId_939_);
if (v___x_953_ == 0)
{
lean_dec_ref(v_k_950_);
lean_dec_ref(v_ty_949_);
lean_dec(v_y_948_);
lean_dec_ref(v_k_944_);
lean_dec_ref(v_ty_943_);
lean_dec(v_y_942_);
lean_dec(v_a_828_);
return v___x_953_;
}
else
{
uint8_t v___x_954_; 
v___x_954_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_942_, v_y_948_, v_a_828_);
lean_dec(v_y_948_);
lean_dec(v_y_942_);
if (v___x_954_ == 0)
{
lean_dec_ref(v_k_950_);
lean_dec_ref(v_ty_949_);
lean_dec_ref(v_k_944_);
lean_dec_ref(v_ty_943_);
lean_dec(v_a_828_);
return v___x_954_;
}
else
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_943_, v_ty_949_, v_a_828_);
lean_dec_ref(v_ty_949_);
lean_dec_ref(v_ty_943_);
if (v___x_955_ == 0)
{
lean_dec_ref(v_k_950_);
lean_dec_ref(v_k_944_);
lean_dec(v_a_828_);
return v___x_955_;
}
else
{
v_code_u2081_826_ = v_k_944_;
v_code_u2082_827_ = v_k_950_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_957_; 
lean_dec_ref_known(v_code_u2081_826_, 6);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_957_ = 0;
return v___x_957_;
}
}
case 10:
{
if (lean_obj_tag(v_code_u2082_827_) == 10)
{
lean_object* v_fvarId_958_; lean_object* v_cidx_959_; lean_object* v_k_960_; lean_object* v_fvarId_961_; lean_object* v_cidx_962_; lean_object* v_k_963_; uint8_t v___x_964_; 
v_fvarId_958_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc(v_fvarId_958_);
v_cidx_959_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc(v_cidx_959_);
v_k_960_ = lean_ctor_get(v_code_u2081_826_, 2);
lean_inc_ref(v_k_960_);
lean_dec_ref_known(v_code_u2081_826_, 3);
v_fvarId_961_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc(v_fvarId_961_);
v_cidx_962_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc(v_cidx_962_);
v_k_963_ = lean_ctor_get(v_code_u2082_827_, 2);
lean_inc_ref(v_k_963_);
lean_dec_ref_known(v_code_u2082_827_, 3);
v___x_964_ = lean_nat_dec_eq(v_cidx_959_, v_cidx_962_);
lean_dec(v_cidx_962_);
lean_dec(v_cidx_959_);
if (v___x_964_ == 0)
{
lean_dec_ref(v_k_963_);
lean_dec(v_fvarId_961_);
lean_dec_ref(v_k_960_);
lean_dec(v_fvarId_958_);
lean_dec(v_a_828_);
return v___x_964_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_958_, v_fvarId_961_, v_a_828_);
lean_dec(v_fvarId_961_);
lean_dec(v_fvarId_958_);
if (v___x_965_ == 0)
{
lean_dec_ref(v_k_963_);
lean_dec_ref(v_k_960_);
lean_dec(v_a_828_);
return v___x_965_;
}
else
{
v_code_u2081_826_ = v_k_960_;
v_code_u2082_827_ = v_k_963_;
goto _start;
}
}
}
else
{
uint8_t v___x_967_; 
lean_dec_ref_known(v_code_u2081_826_, 3);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_967_ = 0;
return v___x_967_;
}
}
case 11:
{
if (lean_obj_tag(v_code_u2082_827_) == 11)
{
lean_object* v_fvarId_968_; lean_object* v_n_969_; uint8_t v_check_970_; uint8_t v_persistent_971_; lean_object* v_k_972_; lean_object* v_fvarId_973_; lean_object* v_n_974_; uint8_t v_check_975_; uint8_t v_persistent_976_; lean_object* v_k_977_; uint8_t v___y_982_; uint8_t v___x_983_; 
v_fvarId_968_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc(v_fvarId_968_);
v_n_969_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc(v_n_969_);
v_check_970_ = lean_ctor_get_uint8(v_code_u2081_826_, sizeof(void*)*3);
v_persistent_971_ = lean_ctor_get_uint8(v_code_u2081_826_, sizeof(void*)*3 + 1);
v_k_972_ = lean_ctor_get(v_code_u2081_826_, 2);
lean_inc_ref(v_k_972_);
lean_dec_ref_known(v_code_u2081_826_, 3);
v_fvarId_973_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc(v_fvarId_973_);
v_n_974_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc(v_n_974_);
v_check_975_ = lean_ctor_get_uint8(v_code_u2082_827_, sizeof(void*)*3);
v_persistent_976_ = lean_ctor_get_uint8(v_code_u2082_827_, sizeof(void*)*3 + 1);
v_k_977_ = lean_ctor_get(v_code_u2082_827_, 2);
lean_inc_ref(v_k_977_);
lean_dec_ref_known(v_code_u2082_827_, 3);
v___x_983_ = lean_nat_dec_eq(v_n_969_, v_n_974_);
lean_dec(v_n_974_);
lean_dec(v_n_969_);
if (v___x_983_ == 0)
{
lean_dec_ref(v_k_977_);
lean_dec(v_fvarId_973_);
lean_dec_ref(v_k_972_);
lean_dec(v_fvarId_968_);
lean_dec(v_a_828_);
return v___x_983_;
}
else
{
if (v_check_975_ == 0)
{
if (v_check_970_ == 0)
{
v___y_982_ = v___x_983_;
goto v___jp_981_;
}
else
{
lean_dec_ref(v_k_977_);
lean_dec(v_fvarId_973_);
lean_dec_ref(v_k_972_);
lean_dec(v_fvarId_968_);
lean_dec(v_a_828_);
return v_check_975_;
}
}
else
{
v___y_982_ = v_check_970_;
goto v___jp_981_;
}
}
v___jp_978_:
{
uint8_t v___x_979_; 
v___x_979_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_968_, v_fvarId_973_, v_a_828_);
lean_dec(v_fvarId_973_);
lean_dec(v_fvarId_968_);
if (v___x_979_ == 0)
{
lean_dec_ref(v_k_977_);
lean_dec_ref(v_k_972_);
lean_dec(v_a_828_);
return v___x_979_;
}
else
{
v_code_u2081_826_ = v_k_972_;
v_code_u2082_827_ = v_k_977_;
goto _start;
}
}
v___jp_981_:
{
if (v___y_982_ == 0)
{
lean_dec_ref(v_k_977_);
lean_dec(v_fvarId_973_);
lean_dec_ref(v_k_972_);
lean_dec(v_fvarId_968_);
lean_dec(v_a_828_);
return v___y_982_;
}
else
{
if (v_persistent_976_ == 0)
{
if (v_persistent_971_ == 0)
{
goto v___jp_978_;
}
else
{
lean_dec_ref(v_k_977_);
lean_dec(v_fvarId_973_);
lean_dec_ref(v_k_972_);
lean_dec(v_fvarId_968_);
lean_dec(v_a_828_);
return v_persistent_976_;
}
}
else
{
if (v_persistent_971_ == 0)
{
lean_dec_ref(v_k_977_);
lean_dec(v_fvarId_973_);
lean_dec_ref(v_k_972_);
lean_dec(v_fvarId_968_);
lean_dec(v_a_828_);
return v_persistent_971_;
}
else
{
goto v___jp_978_;
}
}
}
}
}
else
{
uint8_t v___x_984_; 
lean_dec_ref_known(v_code_u2081_826_, 3);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_984_ = 0;
return v___x_984_;
}
}
case 12:
{
if (lean_obj_tag(v_code_u2082_827_) == 12)
{
lean_object* v_fvarId_985_; lean_object* v_n_986_; uint8_t v_check_987_; uint8_t v_persistent_988_; lean_object* v_objs_x3f_989_; lean_object* v_k_990_; lean_object* v_fvarId_991_; lean_object* v_n_992_; uint8_t v_check_993_; uint8_t v_persistent_994_; lean_object* v_objs_x3f_995_; lean_object* v_k_996_; uint8_t v___y_1002_; uint8_t v___x_1003_; 
v_fvarId_985_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc(v_fvarId_985_);
v_n_986_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc(v_n_986_);
v_check_987_ = lean_ctor_get_uint8(v_code_u2081_826_, sizeof(void*)*4);
v_persistent_988_ = lean_ctor_get_uint8(v_code_u2081_826_, sizeof(void*)*4 + 1);
v_objs_x3f_989_ = lean_ctor_get(v_code_u2081_826_, 2);
lean_inc(v_objs_x3f_989_);
v_k_990_ = lean_ctor_get(v_code_u2081_826_, 3);
lean_inc_ref(v_k_990_);
lean_dec_ref_known(v_code_u2081_826_, 4);
v_fvarId_991_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc(v_fvarId_991_);
v_n_992_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc(v_n_992_);
v_check_993_ = lean_ctor_get_uint8(v_code_u2082_827_, sizeof(void*)*4);
v_persistent_994_ = lean_ctor_get_uint8(v_code_u2082_827_, sizeof(void*)*4 + 1);
v_objs_x3f_995_ = lean_ctor_get(v_code_u2082_827_, 2);
lean_inc(v_objs_x3f_995_);
v_k_996_ = lean_ctor_get(v_code_u2082_827_, 3);
lean_inc_ref(v_k_996_);
lean_dec_ref_known(v_code_u2082_827_, 4);
v___x_1003_ = lean_nat_dec_eq(v_n_986_, v_n_992_);
lean_dec(v_n_992_);
lean_dec(v_n_986_);
if (v___x_1003_ == 0)
{
lean_dec_ref(v_k_996_);
lean_dec(v_objs_x3f_995_);
lean_dec(v_fvarId_991_);
lean_dec_ref(v_k_990_);
lean_dec(v_objs_x3f_989_);
lean_dec(v_fvarId_985_);
lean_dec(v_a_828_);
return v___x_1003_;
}
else
{
if (v_check_993_ == 0)
{
if (v_check_987_ == 0)
{
v___y_1002_ = v___x_1003_;
goto v___jp_1001_;
}
else
{
lean_dec_ref(v_k_996_);
lean_dec(v_objs_x3f_995_);
lean_dec(v_fvarId_991_);
lean_dec_ref(v_k_990_);
lean_dec(v_objs_x3f_989_);
lean_dec(v_fvarId_985_);
lean_dec(v_a_828_);
return v_check_993_;
}
}
else
{
v___y_1002_ = v_check_987_;
goto v___jp_1001_;
}
}
v___jp_997_:
{
uint8_t v___x_998_; 
v___x_998_ = l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(v_objs_x3f_989_, v_objs_x3f_995_);
lean_dec(v_objs_x3f_995_);
lean_dec(v_objs_x3f_989_);
if (v___x_998_ == 0)
{
lean_dec_ref(v_k_996_);
lean_dec(v_fvarId_991_);
lean_dec_ref(v_k_990_);
lean_dec(v_fvarId_985_);
lean_dec(v_a_828_);
return v___x_998_;
}
else
{
uint8_t v___x_999_; 
v___x_999_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_985_, v_fvarId_991_, v_a_828_);
lean_dec(v_fvarId_991_);
lean_dec(v_fvarId_985_);
if (v___x_999_ == 0)
{
lean_dec_ref(v_k_996_);
lean_dec_ref(v_k_990_);
lean_dec(v_a_828_);
return v___x_999_;
}
else
{
v_code_u2081_826_ = v_k_990_;
v_code_u2082_827_ = v_k_996_;
goto _start;
}
}
}
v___jp_1001_:
{
if (v___y_1002_ == 0)
{
lean_dec_ref(v_k_996_);
lean_dec(v_objs_x3f_995_);
lean_dec(v_fvarId_991_);
lean_dec_ref(v_k_990_);
lean_dec(v_objs_x3f_989_);
lean_dec(v_fvarId_985_);
lean_dec(v_a_828_);
return v___y_1002_;
}
else
{
if (v_persistent_994_ == 0)
{
if (v_persistent_988_ == 0)
{
goto v___jp_997_;
}
else
{
lean_dec_ref(v_k_996_);
lean_dec(v_objs_x3f_995_);
lean_dec(v_fvarId_991_);
lean_dec_ref(v_k_990_);
lean_dec(v_objs_x3f_989_);
lean_dec(v_fvarId_985_);
lean_dec(v_a_828_);
return v_persistent_994_;
}
}
else
{
if (v_persistent_988_ == 0)
{
lean_dec_ref(v_k_996_);
lean_dec(v_objs_x3f_995_);
lean_dec(v_fvarId_991_);
lean_dec_ref(v_k_990_);
lean_dec(v_objs_x3f_989_);
lean_dec(v_fvarId_985_);
lean_dec(v_a_828_);
return v_persistent_988_;
}
else
{
goto v___jp_997_;
}
}
}
}
}
else
{
uint8_t v___x_1004_; 
lean_dec_ref_known(v_code_u2081_826_, 4);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_1004_ = 0;
return v___x_1004_;
}
}
default: 
{
if (lean_obj_tag(v_code_u2082_827_) == 13)
{
lean_object* v_fvarId_1005_; lean_object* v_k_1006_; lean_object* v_fvarId_1007_; lean_object* v_k_1008_; uint8_t v___x_1009_; 
v_fvarId_1005_ = lean_ctor_get(v_code_u2081_826_, 0);
lean_inc(v_fvarId_1005_);
v_k_1006_ = lean_ctor_get(v_code_u2081_826_, 1);
lean_inc_ref(v_k_1006_);
lean_dec_ref_known(v_code_u2081_826_, 2);
v_fvarId_1007_ = lean_ctor_get(v_code_u2082_827_, 0);
lean_inc(v_fvarId_1007_);
v_k_1008_ = lean_ctor_get(v_code_u2082_827_, 1);
lean_inc_ref(v_k_1008_);
lean_dec_ref_known(v_code_u2082_827_, 2);
v___x_1009_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_1005_, v_fvarId_1007_, v_a_828_);
lean_dec(v_fvarId_1007_);
lean_dec(v_fvarId_1005_);
if (v___x_1009_ == 0)
{
lean_dec_ref(v_k_1008_);
lean_dec_ref(v_k_1006_);
lean_dec(v_a_828_);
return v___x_1009_;
}
else
{
v_code_u2081_826_ = v_k_1006_;
v_code_u2082_827_ = v_k_1008_;
goto _start;
}
}
else
{
uint8_t v___x_1011_; 
lean_dec_ref_known(v_code_u2081_826_, 2);
lean_dec(v_a_828_);
lean_dec_ref(v_code_u2082_827_);
v___x_1011_ = 0;
return v___x_1011_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_AlphaEqv_eqv_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_825_ = stack[0].m_num;
lean_object* v_code_u2081_826_ = stack[1].m_obj;
lean_object* v_code_u2082_827_ = stack[2].m_obj;
lean_object* v_a_828_ = stack[3].m_obj;
uint8_t v_res_1012_;
v_res_1012_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_825_, v_code_u2081_826_, v_code_u2082_827_, v_a_828_);
stack->m_num = v_res_1012_;
}
uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(uint8_t v_pu_1013_, lean_object* v_code_1014_, lean_object* v_code_1015_, lean_object* v_params_u2081_1016_, lean_object* v_params_u2082_1017_, lean_object* v_i_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_array_get_size(v_params_u2081_1016_);
v___x_1021_ = lean_nat_dec_lt(v_i_1018_, v___x_1020_);
if (v___x_1021_ == 0)
{
uint8_t v___x_1022_; 
lean_dec(v_i_1018_);
v___x_1022_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_1013_, v_code_1014_, v_code_1015_, v_a_1019_);
return v___x_1022_;
}
else
{
lean_object* v_p_u2081_1023_; lean_object* v_fvarId_1024_; lean_object* v_type_1025_; lean_object* v_p_u2082_1026_; lean_object* v_fvarId_1027_; lean_object* v_type_1028_; uint8_t v___x_1029_; 
v_p_u2081_1023_ = lean_array_fget_borrowed(v_params_u2081_1016_, v_i_1018_);
v_fvarId_1024_ = lean_ctor_get(v_p_u2081_1023_, 0);
v_type_1025_ = lean_ctor_get(v_p_u2081_1023_, 2);
v_p_u2082_1026_ = lean_array_fget_borrowed(v_params_u2082_1017_, v_i_1018_);
v_fvarId_1027_ = lean_ctor_get(v_p_u2082_1026_, 0);
v_type_1028_ = lean_ctor_get(v_p_u2082_1026_, 2);
v___x_1029_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_1025_, v_type_1028_, v_a_1019_);
if (v___x_1029_ == 0)
{
lean_dec(v_a_1019_);
lean_dec(v_i_1018_);
lean_dec_ref(v_code_1015_);
lean_dec_ref(v_code_1014_);
return v___x_1029_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_unsigned_to_nat(1u);
v___x_1031_ = lean_nat_add(v_i_1018_, v___x_1030_);
lean_dec(v_i_1018_);
lean_inc(v_fvarId_1024_);
lean_inc(v_fvarId_1027_);
v___x_1032_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1027_, v_fvarId_1024_, v_a_1019_);
v_i_1018_ = v___x_1031_;
v_a_1019_ = v___x_1032_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1013_ = stack[0].m_num;
lean_object* v_code_1014_ = stack[1].m_obj;
lean_object* v_code_1015_ = stack[2].m_obj;
lean_object* v_params_u2081_1016_ = stack[3].m_obj;
lean_object* v_params_u2082_1017_ = stack[4].m_obj;
lean_object* v_i_1018_ = stack[5].m_obj;
lean_object* v_a_1019_ = stack[6].m_obj;
uint8_t v_res_1034_;
v_res_1034_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_1013_, v_code_1014_, v_code_1015_, v_params_u2081_1016_, v_params_u2082_1017_, v_i_1018_, v_a_1019_);
stack->m_num = v_res_1034_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg___boxed(lean_object* v_pu_1035_, lean_object* v_code_1036_, lean_object* v_code_1037_, lean_object* v_params_u2081_1038_, lean_object* v_params_u2082_1039_, lean_object* v_i_1040_, lean_object* v_a_1041_){
_start:
{
uint8_t v_pu_boxed_1042_; uint8_t v_res_1043_; lean_object* v_r_1044_; 
v_pu_boxed_1042_ = lean_unbox(v_pu_1035_);
v_res_1043_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_boxed_1042_, v_code_1036_, v_code_1037_, v_params_u2081_1038_, v_params_u2082_1039_, v_i_1040_, v_a_1041_);
lean_dec_ref(v_params_u2082_1039_);
lean_dec_ref(v_params_u2081_1038_);
v_r_1044_ = lean_box(v_res_1043_);
return v_r_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts___boxed(lean_object* v_pu_1045_, lean_object* v_alts_u2081_1046_, lean_object* v_alts_u2082_1047_, lean_object* v_a_1048_){
_start:
{
uint8_t v_pu_boxed_1049_; uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_pu_boxed_1049_ = lean_unbox(v_pu_1045_);
v_res_1050_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_boxed_1049_, v_alts_u2081_1046_, v_alts_u2082_1047_, v_a_1048_);
lean_dec(v_a_1048_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___boxed(lean_object* v_pu_1052_, lean_object* v_as_1053_, lean_object* v_sz_1054_, lean_object* v_i_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_){
_start:
{
uint8_t v_pu_boxed_1058_; size_t v_sz_boxed_1059_; size_t v_i_boxed_1060_; lean_object* v_res_1061_; 
v_pu_boxed_1058_ = lean_unbox(v_pu_1052_);
v_sz_boxed_1059_ = lean_unbox_usize(v_sz_1054_);
lean_dec(v_sz_1054_);
v_i_boxed_1060_ = lean_unbox_usize(v_i_1055_);
lean_dec(v_i_1055_);
v_res_1061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_boxed_1058_, v_as_1053_, v_sz_boxed_1059_, v_i_boxed_1060_, v_b_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v_as_1053_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqv___boxed(lean_object* v_pu_1062_, lean_object* v_code_u2081_1063_, lean_object* v_code_u2082_1064_, lean_object* v_a_1065_){
_start:
{
uint8_t v_pu_boxed_1066_; uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_pu_boxed_1066_ = lean_unbox(v_pu_1062_);
v_res_1067_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_boxed_1066_, v_code_u2081_1063_, v_code_u2082_1064_, v_a_1065_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(uint8_t v_pu_1069_, lean_object* v_code_1070_, lean_object* v_code_1071_, uint8_t v_pu_1072_, lean_object* v_params_u2081_1073_, lean_object* v_params_u2082_1074_, lean_object* v_h_1075_, lean_object* v_i_1076_, lean_object* v_a_1077_){
_start:
{
uint8_t v___x_1078_; 
lean_inc(v_a_1077_);
v___x_1078_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_1069_, v_code_1070_, v_code_1071_, v_params_u2081_1073_, v_params_u2082_1074_, v_i_1076_, v_a_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1069_ = stack[0].m_num;
lean_object* v_code_1070_ = stack[1].m_obj;
lean_object* v_code_1071_ = stack[2].m_obj;
uint8_t v_pu_1072_ = stack[3].m_num;
lean_object* v_params_u2081_1073_ = stack[4].m_obj;
lean_object* v_params_u2082_1074_ = stack[5].m_obj;
lean_object* v_i_1076_ = stack[7].m_obj;
lean_object* v_a_1077_ = stack[8].m_obj;
uint8_t v_res_1079_;
v_res_1079_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(v_pu_1069_, v_code_1070_, v_code_1071_, v_pu_1072_, v_params_u2081_1073_, v_params_u2082_1074_, lean_box(0), v_i_1076_, v_a_1077_);
stack->m_num = v_res_1079_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___boxed(lean_object* v_pu_1080_, lean_object* v_code_1081_, lean_object* v_code_1082_, lean_object* v_pu_1083_, lean_object* v_params_u2081_1084_, lean_object* v_params_u2082_1085_, lean_object* v_h_1086_, lean_object* v_i_1087_, lean_object* v_a_1088_){
_start:
{
uint8_t v_pu_boxed_1089_; uint8_t v_pu_boxed_1090_; uint8_t v_res_1091_; lean_object* v_r_1092_; 
v_pu_boxed_1089_ = lean_unbox(v_pu_1080_);
v_pu_boxed_1090_ = lean_unbox(v_pu_1083_);
v_res_1091_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(v_pu_boxed_1089_, v_code_1081_, v_code_1082_, v_pu_boxed_1090_, v_params_u2081_1084_, v_params_u2082_1085_, v_h_1086_, v_i_1087_, v_a_1088_);
lean_dec(v_a_1088_);
lean_dec_ref(v_params_u2082_1085_);
lean_dec_ref(v_params_u2081_1084_);
v_r_1092_ = lean_box(v_res_1091_);
return v_r_1092_;
}
}
uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t v_pu_1093_, lean_object* v_c_u2081_1094_, lean_object* v_c_u2082_1095_){
_start:
{
lean_object* v___x_1096_; uint8_t v___x_1097_; 
v___x_1096_ = lean_box(1);
v___x_1097_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_1093_, v_c_u2081_1094_, v_c_u2082_1095_, v___x_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_alphaEqv_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_1093_ = stack[0].m_num;
lean_object* v_c_u2081_1094_ = stack[1].m_obj;
lean_object* v_c_u2082_1095_ = stack[2].m_obj;
uint8_t v_res_1098_;
v_res_1098_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v_pu_1093_, v_c_u2081_1094_, v_c_u2082_1095_);
stack->m_num = v_res_1098_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_alphaEqv___boxed(lean_object* v_pu_1099_, lean_object* v_c_u2081_1100_, lean_object* v_c_u2082_1101_){
_start:
{
uint8_t v_pu_boxed_1102_; uint8_t v_res_1103_; lean_object* v_r_1104_; 
v_pu_boxed_1102_ = lean_unbox(v_pu_1099_);
v_res_1103_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v_pu_boxed_1102_, v_c_u2081_1100_, v_c_u2082_1101_);
v_r_1104_ = lean_box(v_res_1103_);
return v_r_1104_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
}
#ifdef __cplusplus
}
#endif
