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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(lean_object* v_fvarId_u2081_15_, lean_object* v_fvarId_u2082_16_, lean_object* v_a_17_){
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar___boxed(lean_object* v_fvarId_u2081_22_, lean_object* v_fvarId_u2082_23_, lean_object* v_a_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_u2081_22_, v_fvarId_u2082_23_, v_a_24_);
lean_dec(v_a_24_);
lean_dec(v_fvarId_u2082_23_);
lean_dec(v_fvarId_u2081_22_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0(lean_object* v_00_u03b4_27_, lean_object* v_t_28_, lean_object* v_k_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___redArg(v_t_28_, v_k_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0___boxed(lean_object* v_00_u03b4_31_, lean_object* v_t_32_, lean_object* v_k_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Compiler_LCNF_AlphaEqv_eqvFVar_spec__0(v_00_u03b4_31_, v_t_32_, v_k_33_);
lean_dec(v_k_33_);
lean_dec(v_t_32_);
return v_res_34_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvType(lean_object* v_e_u2081_35_, lean_object* v_e_u2082_36_, lean_object* v_a_37_){
_start:
{
switch(lean_obj_tag(v_e_u2081_35_))
{
case 5:
{
if (lean_obj_tag(v_e_u2082_36_) == 5)
{
lean_object* v_fn_38_; lean_object* v_arg_39_; lean_object* v_fn_40_; lean_object* v_arg_41_; uint8_t v___x_42_; 
v_fn_38_ = lean_ctor_get(v_e_u2081_35_, 0);
v_arg_39_ = lean_ctor_get(v_e_u2081_35_, 1);
v_fn_40_ = lean_ctor_get(v_e_u2082_36_, 0);
v_arg_41_ = lean_ctor_get(v_e_u2082_36_, 1);
v___x_42_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_arg_39_, v_arg_41_, v_a_37_);
if (v___x_42_ == 0)
{
return v___x_42_;
}
else
{
v_e_u2081_35_ = v_fn_38_;
v_e_u2082_36_ = v_fn_40_;
goto _start;
}
}
else
{
uint8_t v___x_44_; 
v___x_44_ = lean_expr_eqv(v_e_u2081_35_, v_e_u2082_36_);
return v___x_44_;
}
}
case 1:
{
if (lean_obj_tag(v_e_u2082_36_) == 1)
{
lean_object* v_fvarId_45_; lean_object* v_fvarId_46_; uint8_t v___x_47_; 
v_fvarId_45_ = lean_ctor_get(v_e_u2081_35_, 0);
v_fvarId_46_ = lean_ctor_get(v_e_u2082_36_, 0);
v___x_47_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_45_, v_fvarId_46_, v_a_37_);
return v___x_47_;
}
else
{
uint8_t v___x_48_; 
v___x_48_ = lean_expr_eqv(v_e_u2081_35_, v_e_u2082_36_);
return v___x_48_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_36_) == 7)
{
lean_object* v_binderType_49_; lean_object* v_body_50_; lean_object* v_binderType_51_; lean_object* v_body_52_; uint8_t v___x_53_; 
v_binderType_49_ = lean_ctor_get(v_e_u2081_35_, 1);
v_body_50_ = lean_ctor_get(v_e_u2081_35_, 2);
v_binderType_51_ = lean_ctor_get(v_e_u2082_36_, 1);
v_body_52_ = lean_ctor_get(v_e_u2082_36_, 2);
v___x_53_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_binderType_49_, v_binderType_51_, v_a_37_);
if (v___x_53_ == 0)
{
return v___x_53_;
}
else
{
v_e_u2081_35_ = v_body_50_;
v_e_u2082_36_ = v_body_52_;
goto _start;
}
}
else
{
uint8_t v___x_55_; 
v___x_55_ = lean_expr_eqv(v_e_u2081_35_, v_e_u2082_36_);
return v___x_55_;
}
}
default: 
{
uint8_t v___x_56_; 
v___x_56_ = lean_expr_eqv(v_e_u2081_35_, v_e_u2082_36_);
return v___x_56_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvType___boxed(lean_object* v_e_u2081_57_, lean_object* v_e_u2082_58_, lean_object* v_a_59_){
_start:
{
uint8_t v_res_60_; lean_object* v_r_61_; 
v_res_60_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_e_u2081_57_, v_e_u2082_58_, v_a_59_);
lean_dec(v_a_59_);
lean_dec_ref(v_e_u2082_58_);
lean_dec_ref(v_e_u2081_57_);
v_r_61_ = lean_box(v_res_60_);
return v_r_61_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(lean_object* v_as_62_, size_t v_sz_63_, size_t v_i_64_, lean_object* v_b_65_, lean_object* v___y_66_){
_start:
{
uint8_t v___x_67_; 
v___x_67_ = lean_usize_dec_lt(v_i_64_, v_sz_63_);
if (v___x_67_ == 0)
{
return v_b_65_;
}
else
{
lean_object* v_snd_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_106_; 
v_snd_68_ = lean_ctor_get(v_b_65_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_b_65_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v_b_65_, 0);
lean_dec(v_unused_107_);
v___x_70_ = v_b_65_;
v_isShared_71_ = v_isSharedCheck_106_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_snd_68_);
lean_dec(v_b_65_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_106_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_array_72_; lean_object* v_start_73_; lean_object* v_stop_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_array_72_ = lean_ctor_get(v_snd_68_, 0);
v_start_73_ = lean_ctor_get(v_snd_68_, 1);
v_stop_74_ = lean_ctor_get(v_snd_68_, 2);
v___x_75_ = lean_box(0);
v___x_76_ = lean_nat_dec_lt(v_start_73_, v_stop_74_);
if (v___x_76_ == 0)
{
lean_object* v___x_78_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_75_);
v___x_78_ = v___x_70_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_79_, 1, v_snd_68_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
else
{
lean_object* v___x_81_; uint8_t v_isShared_82_; uint8_t v_isSharedCheck_102_; 
lean_inc(v_stop_74_);
lean_inc(v_start_73_);
lean_inc_ref(v_array_72_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_snd_68_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; lean_object* v_unused_104_; lean_object* v_unused_105_; 
v_unused_103_ = lean_ctor_get(v_snd_68_, 2);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_snd_68_, 1);
lean_dec(v_unused_104_);
v_unused_105_ = lean_ctor_get(v_snd_68_, 0);
lean_dec(v_unused_105_);
v___x_81_ = v_snd_68_;
v_isShared_82_ = v_isSharedCheck_102_;
goto v_resetjp_80_;
}
else
{
lean_dec(v_snd_68_);
v___x_81_ = lean_box(0);
v_isShared_82_ = v_isSharedCheck_102_;
goto v_resetjp_80_;
}
v_resetjp_80_:
{
lean_object* v_a_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v_a_83_ = lean_array_uget_borrowed(v_as_62_, v_i_64_);
v___x_84_ = lean_array_fget(v_array_72_, v_start_73_);
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = lean_nat_add(v_start_73_, v___x_85_);
lean_dec(v_start_73_);
if (v_isShared_82_ == 0)
{
lean_ctor_set(v___x_81_, 1, v___x_86_);
v___x_88_ = v___x_81_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_array_72_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___x_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_stop_74_);
v___x_88_ = v_reuseFailAlloc_101_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
uint8_t v___x_89_; 
v___x_89_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_a_83_, v___x_84_, v___y_66_);
lean_dec(v___x_84_);
if (v___x_89_ == 0)
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_90_ = lean_box(v___x_89_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_88_);
lean_ctor_set(v___x_70_, 0, v___x_91_);
v___x_93_ = v___x_70_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v___x_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
else
{
lean_object* v___x_96_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 1, v___x_88_);
lean_ctor_set(v___x_70_, 0, v___x_75_);
v___x_96_ = v___x_70_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_75_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v___x_88_);
v___x_96_ = v_reuseFailAlloc_100_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
size_t v___x_97_; size_t v___x_98_; 
v___x_97_ = ((size_t)1ULL);
v___x_98_ = lean_usize_add(v_i_64_, v___x_97_);
v_i_64_ = v___x_98_;
v_b_65_ = v___x_96_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0___boxed(lean_object* v_as_108_, lean_object* v_sz_109_, lean_object* v_i_110_, lean_object* v_b_111_, lean_object* v___y_112_){
_start:
{
size_t v_sz_boxed_113_; size_t v_i_boxed_114_; lean_object* v_res_115_; 
v_sz_boxed_113_ = lean_unbox_usize(v_sz_109_);
lean_dec(v_sz_109_);
v_i_boxed_114_ = lean_unbox_usize(v_i_110_);
lean_dec(v_i_110_);
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(v_as_108_, v_sz_boxed_113_, v_i_boxed_114_, v_b_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v_as_108_);
return v_res_115_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes(lean_object* v_es_u2081_116_, lean_object* v_es_u2082_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = lean_array_get_size(v_es_u2081_116_);
v___x_120_ = lean_array_get_size(v_es_u2082_117_);
v___x_121_ = lean_nat_dec_eq(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
lean_dec_ref(v_es_u2082_117_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; size_t v_sz_126_; size_t v___x_127_; lean_object* v___x_128_; lean_object* v_fst_129_; 
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = l_Array_toSubarray___redArg(v_es_u2082_117_, v___x_122_, v___x_120_);
v___x_124_ = lean_box(0);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_123_);
v_sz_126_ = lean_array_size(v_es_u2081_116_);
v___x_127_ = ((size_t)0ULL);
v___x_128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvTypes_spec__0(v_es_u2081_116_, v_sz_126_, v___x_127_, v___x_125_, v_a_118_);
v_fst_129_ = lean_ctor_get(v___x_128_, 0);
lean_inc(v_fst_129_);
lean_dec_ref(v___x_128_);
if (lean_obj_tag(v_fst_129_) == 0)
{
return v___x_121_;
}
else
{
lean_object* v_val_130_; uint8_t v___x_131_; 
v_val_130_ = lean_ctor_get(v_fst_129_, 0);
lean_inc(v_val_130_);
lean_dec_ref_known(v_fst_129_, 1);
v___x_131_ = lean_unbox(v_val_130_);
lean_dec(v_val_130_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes___boxed(lean_object* v_es_u2081_132_, lean_object* v_es_u2082_133_, lean_object* v_a_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvTypes(v_es_u2081_132_, v_es_u2082_133_, v_a_134_);
lean_dec(v_a_134_);
lean_dec_ref(v_es_u2081_132_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(lean_object* v_a_u2081_137_, lean_object* v_a_u2082_138_, lean_object* v_a_139_){
_start:
{
switch(lean_obj_tag(v_a_u2081_137_))
{
case 0:
{
if (lean_obj_tag(v_a_u2082_138_) == 0)
{
uint8_t v___x_140_; 
v___x_140_ = 1;
return v___x_140_;
}
else
{
uint8_t v___x_141_; 
v___x_141_ = 0;
return v___x_141_;
}
}
case 1:
{
if (lean_obj_tag(v_a_u2082_138_) == 1)
{
lean_object* v_fvarId_142_; lean_object* v_fvarId_143_; uint8_t v___x_144_; 
v_fvarId_142_ = lean_ctor_get(v_a_u2081_137_, 0);
v_fvarId_143_ = lean_ctor_get(v_a_u2082_138_, 0);
v___x_144_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_142_, v_fvarId_143_, v_a_139_);
return v___x_144_;
}
else
{
uint8_t v___x_145_; 
v___x_145_ = 0;
return v___x_145_;
}
}
default: 
{
if (lean_obj_tag(v_a_u2082_138_) == 2)
{
lean_object* v_expr_146_; lean_object* v_expr_147_; uint8_t v___x_148_; 
v_expr_146_ = lean_ctor_get(v_a_u2081_137_, 0);
v_expr_147_ = lean_ctor_get(v_a_u2082_138_, 0);
v___x_148_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_expr_146_, v_expr_147_, v_a_139_);
return v___x_148_;
}
else
{
uint8_t v___x_149_; 
v___x_149_ = 0;
return v___x_149_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg___boxed(lean_object* v_a_u2081_150_, lean_object* v_a_u2082_151_, lean_object* v_a_152_){
_start:
{
uint8_t v_res_153_; lean_object* v_r_154_; 
v_res_153_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_a_u2081_150_, v_a_u2082_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec(v_a_u2082_151_);
lean_dec(v_a_u2081_150_);
v_r_154_ = lean_box(v_res_153_);
return v_r_154_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvArg(uint8_t v_pu_155_, lean_object* v_a_u2081_156_, lean_object* v_a_u2082_157_, lean_object* v_a_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_a_u2081_156_, v_a_u2082_157_, v_a_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___boxed(lean_object* v_pu_160_, lean_object* v_a_u2081_161_, lean_object* v_a_u2082_162_, lean_object* v_a_163_){
_start:
{
uint8_t v_pu_boxed_164_; uint8_t v_res_165_; lean_object* v_r_166_; 
v_pu_boxed_164_ = lean_unbox(v_pu_160_);
v_res_165_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg(v_pu_boxed_164_, v_a_u2081_161_, v_a_u2082_162_, v_a_163_);
lean_dec(v_a_163_);
lean_dec(v_a_u2082_162_);
lean_dec(v_a_u2081_161_);
v_r_166_ = lean_box(v_res_165_);
return v_r_166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(lean_object* v_as_167_, size_t v_sz_168_, size_t v_i_169_, lean_object* v_b_170_, lean_object* v___y_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lean_usize_dec_lt(v_i_169_, v_sz_168_);
if (v___x_172_ == 0)
{
return v_b_170_;
}
else
{
lean_object* v_snd_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_211_; 
v_snd_173_ = lean_ctor_get(v_b_170_, 1);
v_isSharedCheck_211_ = !lean_is_exclusive(v_b_170_);
if (v_isSharedCheck_211_ == 0)
{
lean_object* v_unused_212_; 
v_unused_212_ = lean_ctor_get(v_b_170_, 0);
lean_dec(v_unused_212_);
v___x_175_ = v_b_170_;
v_isShared_176_ = v_isSharedCheck_211_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snd_173_);
lean_dec(v_b_170_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_211_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v_array_177_; lean_object* v_start_178_; lean_object* v_stop_179_; lean_object* v___x_180_; uint8_t v___x_181_; 
v_array_177_ = lean_ctor_get(v_snd_173_, 0);
v_start_178_ = lean_ctor_get(v_snd_173_, 1);
v_stop_179_ = lean_ctor_get(v_snd_173_, 2);
v___x_180_ = lean_box(0);
v___x_181_ = lean_nat_dec_lt(v_start_178_, v_stop_179_);
if (v___x_181_ == 0)
{
lean_object* v___x_183_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_180_);
v___x_183_ = v___x_175_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_snd_173_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
else
{
lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_207_; 
lean_inc(v_stop_179_);
lean_inc(v_start_178_);
lean_inc_ref(v_array_177_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_snd_173_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; lean_object* v_unused_209_; lean_object* v_unused_210_; 
v_unused_208_ = lean_ctor_get(v_snd_173_, 2);
lean_dec(v_unused_208_);
v_unused_209_ = lean_ctor_get(v_snd_173_, 1);
lean_dec(v_unused_209_);
v_unused_210_ = lean_ctor_get(v_snd_173_, 0);
lean_dec(v_unused_210_);
v___x_186_ = v_snd_173_;
v_isShared_187_ = v_isSharedCheck_207_;
goto v_resetjp_185_;
}
else
{
lean_dec(v_snd_173_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_207_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v_a_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v_a_188_ = lean_array_uget_borrowed(v_as_167_, v_i_169_);
v___x_189_ = lean_array_fget(v_array_177_, v_start_178_);
v___x_190_ = lean_unsigned_to_nat(1u);
v___x_191_ = lean_nat_add(v_start_178_, v___x_190_);
lean_dec(v_start_178_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v___x_191_);
v___x_193_ = v___x_186_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_array_177_);
lean_ctor_set(v_reuseFailAlloc_206_, 1, v___x_191_);
lean_ctor_set(v_reuseFailAlloc_206_, 2, v_stop_179_);
v___x_193_ = v_reuseFailAlloc_206_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
uint8_t v___x_194_; 
v___x_194_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_a_188_, v___x_189_, v___y_171_);
lean_dec(v___x_189_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_195_ = lean_box(v___x_194_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_193_);
lean_ctor_set(v___x_175_, 0, v___x_196_);
v___x_198_ = v___x_175_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
else
{
lean_object* v___x_201_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_193_);
lean_ctor_set(v___x_175_, 0, v___x_180_);
v___x_201_ = v___x_175_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_180_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_193_);
v___x_201_ = v_reuseFailAlloc_205_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
size_t v___x_202_; size_t v___x_203_; 
v___x_202_ = ((size_t)1ULL);
v___x_203_ = lean_usize_add(v_i_169_, v___x_202_);
v_i_169_ = v___x_203_;
v_b_170_ = v___x_201_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg___boxed(lean_object* v_as_213_, lean_object* v_sz_214_, lean_object* v_i_215_, lean_object* v_b_216_, lean_object* v___y_217_){
_start:
{
size_t v_sz_boxed_218_; size_t v_i_boxed_219_; lean_object* v_res_220_; 
v_sz_boxed_218_ = lean_unbox_usize(v_sz_214_);
lean_dec(v_sz_214_);
v_i_boxed_219_ = lean_unbox_usize(v_i_215_);
lean_dec(v_i_215_);
v_res_220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_213_, v_sz_boxed_218_, v_i_boxed_219_, v_b_216_, v___y_217_);
lean_dec(v___y_217_);
lean_dec_ref(v_as_213_);
return v_res_220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(uint8_t v_pu_221_, lean_object* v_as_u2081_222_, lean_object* v_as_u2082_223_, lean_object* v_a_224_){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = lean_array_get_size(v_as_u2081_222_);
v___x_226_ = lean_array_get_size(v_as_u2082_223_);
v___x_227_ = lean_nat_dec_eq(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec_ref(v_as_u2082_223_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; size_t v_sz_232_; size_t v___x_233_; lean_object* v___x_234_; lean_object* v_fst_235_; 
v___x_228_ = lean_unsigned_to_nat(0u);
v___x_229_ = l_Array_toSubarray___redArg(v_as_u2082_223_, v___x_228_, v___x_226_);
v___x_230_ = lean_box(0);
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_229_);
v_sz_232_ = lean_array_size(v_as_u2081_222_);
v___x_233_ = ((size_t)0ULL);
v___x_234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_u2081_222_, v_sz_232_, v___x_233_, v___x_231_, v_a_224_);
v_fst_235_ = lean_ctor_get(v___x_234_, 0);
lean_inc(v_fst_235_);
lean_dec_ref(v___x_234_);
if (lean_obj_tag(v_fst_235_) == 0)
{
return v___x_227_;
}
else
{
lean_object* v_val_236_; uint8_t v___x_237_; 
v_val_236_ = lean_ctor_get(v_fst_235_, 0);
lean_inc(v_val_236_);
lean_dec_ref_known(v_fst_235_, 1);
v___x_237_ = lean_unbox(v_val_236_);
lean_dec(v_val_236_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs___boxed(lean_object* v_pu_238_, lean_object* v_as_u2081_239_, lean_object* v_as_u2082_240_, lean_object* v_a_241_){
_start:
{
uint8_t v_pu_boxed_242_; uint8_t v_res_243_; lean_object* v_r_244_; 
v_pu_boxed_242_ = lean_unbox(v_pu_238_);
v_res_243_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_boxed_242_, v_as_u2081_239_, v_as_u2082_240_, v_a_241_);
lean_dec(v_a_241_);
lean_dec_ref(v_as_u2081_239_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0(uint8_t v_pu_245_, lean_object* v_as_246_, size_t v_sz_247_, size_t v_i_248_, lean_object* v_b_249_, lean_object* v___y_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___redArg(v_as_246_, v_sz_247_, v_i_248_, v_b_249_, v___y_250_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0___boxed(lean_object* v_pu_252_, lean_object* v_as_253_, lean_object* v_sz_254_, lean_object* v_i_255_, lean_object* v_b_256_, lean_object* v___y_257_){
_start:
{
uint8_t v_pu_boxed_258_; size_t v_sz_boxed_259_; size_t v_i_boxed_260_; lean_object* v_res_261_; 
v_pu_boxed_258_ = lean_unbox(v_pu_252_);
v_sz_boxed_259_ = lean_unbox_usize(v_sz_254_);
lean_dec(v_sz_254_);
v_i_boxed_260_ = lean_unbox_usize(v_i_255_);
lean_dec(v_i_255_);
v_res_261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvArgs_spec__0(v_pu_boxed_258_, v_as_253_, v_sz_boxed_259_, v_i_boxed_260_, v_b_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v_as_253_);
return v_res_261_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
if (lean_obj_tag(v_x_263_) == 0)
{
uint8_t v___x_264_; 
v___x_264_ = 1;
return v___x_264_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = 0;
return v___x_265_;
}
}
else
{
if (lean_obj_tag(v_x_263_) == 0)
{
uint8_t v___x_266_; 
v___x_266_ = 0;
return v___x_266_;
}
else
{
lean_object* v_head_267_; lean_object* v_tail_268_; lean_object* v_head_269_; lean_object* v_tail_270_; uint8_t v___x_271_; 
v_head_267_ = lean_ctor_get(v_x_262_, 0);
v_tail_268_ = lean_ctor_get(v_x_262_, 1);
v_head_269_ = lean_ctor_get(v_x_263_, 0);
v_tail_270_ = lean_ctor_get(v_x_263_, 1);
v___x_271_ = lean_level_eq(v_head_267_, v_head_269_);
if (v___x_271_ == 0)
{
return v___x_271_;
}
else
{
v_x_262_ = v_tail_268_;
v_x_263_ = v_tail_270_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0___boxed(lean_object* v_x_273_, lean_object* v_x_274_){
_start:
{
uint8_t v_res_275_; lean_object* v_r_276_; 
v_res_275_ = l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(v_x_273_, v_x_274_);
lean_dec(v_x_274_);
lean_dec(v_x_273_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(uint8_t v_pu_277_, lean_object* v_e_u2081_278_, lean_object* v_e_u2082_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_f_u2081_282_; lean_object* v_as_u2081_283_; lean_object* v_f_u2082_284_; lean_object* v_as_u2082_285_; lean_object* v___y_286_; lean_object* v_i_u2081_290_; lean_object* v_v_u2081_291_; lean_object* v_i_u2082_292_; lean_object* v_v_u2082_293_; lean_object* v___y_294_; 
switch(lean_obj_tag(v_e_u2081_278_))
{
case 0:
{
if (lean_obj_tag(v_e_u2082_279_) == 0)
{
lean_object* v_value_297_; lean_object* v_value_298_; uint8_t v___x_299_; 
v_value_297_ = lean_ctor_get(v_e_u2081_278_, 0);
v_value_298_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc_ref(v_value_298_);
lean_dec_ref_known(v_e_u2082_279_, 1);
v___x_299_ = l_Lean_Compiler_LCNF_instBEqLitValue_beq(v_value_297_, v_value_298_);
lean_dec_ref(v_value_298_);
return v___x_299_;
}
else
{
uint8_t v___x_300_; 
lean_dec(v_e_u2082_279_);
v___x_300_ = 0;
return v___x_300_;
}
}
case 1:
{
if (lean_obj_tag(v_e_u2082_279_) == 1)
{
uint8_t v___x_301_; 
v___x_301_ = 1;
return v___x_301_;
}
else
{
uint8_t v___x_302_; 
lean_dec(v_e_u2082_279_);
v___x_302_ = 0;
return v___x_302_;
}
}
case 2:
{
if (lean_obj_tag(v_e_u2082_279_) == 2)
{
lean_object* v_typeName_303_; lean_object* v_idx_304_; lean_object* v_struct_305_; lean_object* v_typeName_306_; lean_object* v_idx_307_; lean_object* v_struct_308_; uint8_t v___y_310_; uint8_t v___x_312_; 
v_typeName_303_ = lean_ctor_get(v_e_u2081_278_, 0);
v_idx_304_ = lean_ctor_get(v_e_u2081_278_, 1);
v_struct_305_ = lean_ctor_get(v_e_u2081_278_, 2);
v_typeName_306_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_typeName_306_);
v_idx_307_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_idx_307_);
v_struct_308_ = lean_ctor_get(v_e_u2082_279_, 2);
lean_inc(v_struct_308_);
lean_dec_ref_known(v_e_u2082_279_, 3);
v___x_312_ = lean_name_eq(v_typeName_303_, v_typeName_306_);
lean_dec(v_typeName_306_);
if (v___x_312_ == 0)
{
lean_dec(v_idx_307_);
v___y_310_ = v___x_312_;
goto v___jp_309_;
}
else
{
uint8_t v___x_313_; 
v___x_313_ = lean_nat_dec_eq(v_idx_304_, v_idx_307_);
lean_dec(v_idx_307_);
v___y_310_ = v___x_313_;
goto v___jp_309_;
}
v___jp_309_:
{
if (v___y_310_ == 0)
{
lean_dec(v_struct_308_);
return v___y_310_;
}
else
{
uint8_t v___x_311_; 
v___x_311_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_struct_305_, v_struct_308_, v_a_280_);
lean_dec(v_struct_308_);
return v___x_311_;
}
}
}
else
{
uint8_t v___x_314_; 
lean_dec(v_e_u2082_279_);
v___x_314_ = 0;
return v___x_314_;
}
}
case 3:
{
if (lean_obj_tag(v_e_u2082_279_) == 3)
{
lean_object* v_declName_315_; lean_object* v_us_316_; lean_object* v_args_317_; lean_object* v_declName_318_; lean_object* v_us_319_; lean_object* v_args_320_; uint8_t v___y_322_; uint8_t v___x_324_; 
v_declName_315_ = lean_ctor_get(v_e_u2081_278_, 0);
v_us_316_ = lean_ctor_get(v_e_u2081_278_, 1);
v_args_317_ = lean_ctor_get(v_e_u2081_278_, 2);
v_declName_318_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_declName_318_);
v_us_319_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_us_319_);
v_args_320_ = lean_ctor_get(v_e_u2082_279_, 2);
lean_inc_ref(v_args_320_);
lean_dec_ref_known(v_e_u2082_279_, 3);
v___x_324_ = lean_name_eq(v_declName_315_, v_declName_318_);
lean_dec(v_declName_318_);
if (v___x_324_ == 0)
{
lean_dec(v_us_319_);
v___y_322_ = v___x_324_;
goto v___jp_321_;
}
else
{
uint8_t v___x_325_; 
v___x_325_ = l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(v_us_316_, v_us_319_);
lean_dec(v_us_319_);
v___y_322_ = v___x_325_;
goto v___jp_321_;
}
v___jp_321_:
{
if (v___y_322_ == 0)
{
lean_dec_ref(v_args_320_);
return v___y_322_;
}
else
{
uint8_t v___x_323_; 
v___x_323_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_args_317_, v_args_320_, v_a_280_);
return v___x_323_;
}
}
}
else
{
uint8_t v___x_326_; 
lean_dec(v_e_u2082_279_);
v___x_326_ = 0;
return v___x_326_;
}
}
case 4:
{
if (lean_obj_tag(v_e_u2082_279_) == 4)
{
lean_object* v_fvarId_327_; lean_object* v_args_328_; lean_object* v_fvarId_329_; lean_object* v_args_330_; uint8_t v___x_331_; 
v_fvarId_327_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_328_ = lean_ctor_get(v_e_u2081_278_, 1);
v_fvarId_329_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fvarId_329_);
v_args_330_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_330_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v___x_331_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_327_, v_fvarId_329_, v_a_280_);
lean_dec(v_fvarId_329_);
if (v___x_331_ == 0)
{
lean_dec_ref(v_args_330_);
return v___x_331_;
}
else
{
uint8_t v___x_332_; 
v___x_332_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_args_328_, v_args_330_, v_a_280_);
return v___x_332_;
}
}
else
{
uint8_t v___x_333_; 
lean_dec(v_e_u2082_279_);
v___x_333_ = 0;
return v___x_333_;
}
}
case 5:
{
if (lean_obj_tag(v_e_u2082_279_) == 5)
{
lean_object* v_i_334_; lean_object* v_args_335_; lean_object* v_i_336_; lean_object* v_args_337_; uint8_t v___x_338_; 
v_i_334_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_335_ = lean_ctor_get(v_e_u2081_278_, 1);
v_i_336_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc_ref(v_i_336_);
v_args_337_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_337_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v___x_338_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_i_334_, v_i_336_);
lean_dec_ref(v_i_336_);
if (v___x_338_ == 0)
{
lean_dec_ref(v_args_337_);
return v___x_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_args_335_, v_args_337_, v_a_280_);
return v___x_339_;
}
}
else
{
uint8_t v___x_340_; 
lean_dec(v_e_u2082_279_);
v___x_340_ = 0;
return v___x_340_;
}
}
case 6:
{
if (lean_obj_tag(v_e_u2082_279_) == 6)
{
lean_object* v_i_341_; lean_object* v_var_342_; lean_object* v_i_343_; lean_object* v_var_344_; 
v_i_341_ = lean_ctor_get(v_e_u2081_278_, 0);
v_var_342_ = lean_ctor_get(v_e_u2081_278_, 1);
v_i_343_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_i_343_);
v_var_344_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_var_344_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_i_u2081_290_ = v_i_341_;
v_v_u2081_291_ = v_var_342_;
v_i_u2082_292_ = v_i_343_;
v_v_u2082_293_ = v_var_344_;
v___y_294_ = v_a_280_;
goto v___jp_289_;
}
else
{
uint8_t v___x_345_; 
lean_dec(v_e_u2082_279_);
v___x_345_ = 0;
return v___x_345_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_279_) == 7)
{
lean_object* v_i_346_; lean_object* v_var_347_; lean_object* v_i_348_; lean_object* v_var_349_; 
v_i_346_ = lean_ctor_get(v_e_u2081_278_, 0);
v_var_347_ = lean_ctor_get(v_e_u2081_278_, 1);
v_i_348_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_i_348_);
v_var_349_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_var_349_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_i_u2081_290_ = v_i_346_;
v_v_u2081_291_ = v_var_347_;
v_i_u2082_292_ = v_i_348_;
v_v_u2082_293_ = v_var_349_;
v___y_294_ = v_a_280_;
goto v___jp_289_;
}
else
{
uint8_t v___x_350_; 
lean_dec(v_e_u2082_279_);
v___x_350_ = 0;
return v___x_350_;
}
}
case 8:
{
if (lean_obj_tag(v_e_u2082_279_) == 8)
{
lean_object* v_n_351_; lean_object* v_offset_352_; lean_object* v_var_353_; lean_object* v_n_354_; lean_object* v_offset_355_; lean_object* v_var_356_; uint8_t v___x_357_; 
v_n_351_ = lean_ctor_get(v_e_u2081_278_, 0);
v_offset_352_ = lean_ctor_get(v_e_u2081_278_, 1);
v_var_353_ = lean_ctor_get(v_e_u2081_278_, 2);
v_n_354_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_n_354_);
v_offset_355_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_offset_355_);
v_var_356_ = lean_ctor_get(v_e_u2082_279_, 2);
lean_inc(v_var_356_);
lean_dec_ref_known(v_e_u2082_279_, 3);
v___x_357_ = lean_nat_dec_eq(v_n_351_, v_n_354_);
lean_dec(v_n_354_);
if (v___x_357_ == 0)
{
lean_dec(v_var_356_);
lean_dec(v_offset_355_);
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = lean_nat_dec_eq(v_offset_352_, v_offset_355_);
lean_dec(v_offset_355_);
if (v___x_358_ == 0)
{
lean_dec(v_var_356_);
return v___x_358_;
}
else
{
uint8_t v___x_359_; 
v___x_359_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_var_353_, v_var_356_, v_a_280_);
lean_dec(v_var_356_);
return v___x_359_;
}
}
}
else
{
uint8_t v___x_360_; 
lean_dec(v_e_u2082_279_);
v___x_360_ = 0;
return v___x_360_;
}
}
case 9:
{
if (lean_obj_tag(v_e_u2082_279_) == 9)
{
lean_object* v_fn_361_; lean_object* v_args_362_; lean_object* v_fn_363_; lean_object* v_args_364_; 
v_fn_361_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_362_ = lean_ctor_get(v_e_u2081_278_, 1);
v_fn_363_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fn_363_);
v_args_364_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_364_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_f_u2081_282_ = v_fn_361_;
v_as_u2081_283_ = v_args_362_;
v_f_u2082_284_ = v_fn_363_;
v_as_u2082_285_ = v_args_364_;
v___y_286_ = v_a_280_;
goto v___jp_281_;
}
else
{
uint8_t v___x_365_; 
lean_dec(v_e_u2082_279_);
v___x_365_ = 0;
return v___x_365_;
}
}
case 10:
{
if (lean_obj_tag(v_e_u2082_279_) == 10)
{
lean_object* v_fn_366_; lean_object* v_args_367_; lean_object* v_fn_368_; lean_object* v_args_369_; 
v_fn_366_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_367_ = lean_ctor_get(v_e_u2081_278_, 1);
v_fn_368_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fn_368_);
v_args_369_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_369_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_f_u2081_282_ = v_fn_366_;
v_as_u2081_283_ = v_args_367_;
v_f_u2082_284_ = v_fn_368_;
v_as_u2082_285_ = v_args_369_;
v___y_286_ = v_a_280_;
goto v___jp_281_;
}
else
{
uint8_t v___x_370_; 
lean_dec(v_e_u2082_279_);
v___x_370_ = 0;
return v___x_370_;
}
}
case 11:
{
if (lean_obj_tag(v_e_u2082_279_) == 11)
{
lean_object* v_n_371_; lean_object* v_var_372_; lean_object* v_n_373_; lean_object* v_var_374_; 
v_n_371_ = lean_ctor_get(v_e_u2081_278_, 0);
v_var_372_ = lean_ctor_get(v_e_u2081_278_, 1);
v_n_373_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_n_373_);
v_var_374_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_var_374_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_i_u2081_290_ = v_n_371_;
v_v_u2081_291_ = v_var_372_;
v_i_u2082_292_ = v_n_373_;
v_v_u2082_293_ = v_var_374_;
v___y_294_ = v_a_280_;
goto v___jp_289_;
}
else
{
uint8_t v___x_375_; 
lean_dec(v_e_u2082_279_);
v___x_375_ = 0;
return v___x_375_;
}
}
case 12:
{
if (lean_obj_tag(v_e_u2082_279_) == 12)
{
lean_object* v_var_376_; lean_object* v_i_377_; uint8_t v_updateHeader_378_; lean_object* v_args_379_; lean_object* v_var_380_; lean_object* v_i_381_; uint8_t v_updateHeader_382_; lean_object* v_args_383_; uint8_t v___y_385_; uint8_t v___x_388_; 
v_var_376_ = lean_ctor_get(v_e_u2081_278_, 0);
v_i_377_ = lean_ctor_get(v_e_u2081_278_, 1);
v_updateHeader_378_ = lean_ctor_get_uint8(v_e_u2081_278_, sizeof(void*)*3);
v_args_379_ = lean_ctor_get(v_e_u2081_278_, 2);
v_var_380_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_var_380_);
v_i_381_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_i_381_);
v_updateHeader_382_ = lean_ctor_get_uint8(v_e_u2082_279_, sizeof(void*)*3);
v_args_383_ = lean_ctor_get(v_e_u2082_279_, 2);
lean_inc_ref(v_args_383_);
lean_dec_ref_known(v_e_u2082_279_, 3);
v___x_388_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_i_377_, v_i_381_);
lean_dec_ref(v_i_381_);
if (v___x_388_ == 0)
{
v___y_385_ = v___x_388_;
goto v___jp_384_;
}
else
{
if (v_updateHeader_382_ == 0)
{
if (v_updateHeader_378_ == 0)
{
v___y_385_ = v___x_388_;
goto v___jp_384_;
}
else
{
lean_dec_ref(v_args_383_);
lean_dec(v_var_380_);
return v_updateHeader_382_;
}
}
else
{
v___y_385_ = v_updateHeader_378_;
goto v___jp_384_;
}
}
v___jp_384_:
{
if (v___y_385_ == 0)
{
lean_dec_ref(v_args_383_);
lean_dec(v_var_380_);
return v___y_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_var_376_, v_var_380_, v_a_280_);
lean_dec(v_var_380_);
if (v___x_386_ == 0)
{
lean_dec_ref(v_args_383_);
return v___x_386_;
}
else
{
uint8_t v___x_387_; 
v___x_387_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_args_379_, v_args_383_, v_a_280_);
return v___x_387_;
}
}
}
}
else
{
uint8_t v___x_389_; 
lean_dec(v_e_u2082_279_);
v___x_389_ = 0;
return v___x_389_;
}
}
case 13:
{
if (lean_obj_tag(v_e_u2082_279_) == 13)
{
lean_object* v_ty_390_; lean_object* v_fvarId_391_; lean_object* v_ty_392_; lean_object* v_fvarId_393_; uint8_t v___x_394_; 
v_ty_390_ = lean_ctor_get(v_e_u2081_278_, 0);
v_fvarId_391_ = lean_ctor_get(v_e_u2081_278_, 1);
v_ty_392_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc_ref(v_ty_392_);
v_fvarId_393_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_fvarId_393_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v___x_394_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_390_, v_ty_392_, v_a_280_);
lean_dec_ref(v_ty_392_);
if (v___x_394_ == 0)
{
lean_dec(v_fvarId_393_);
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_391_, v_fvarId_393_, v_a_280_);
lean_dec(v_fvarId_393_);
return v___x_395_;
}
}
else
{
uint8_t v___x_396_; 
lean_dec(v_e_u2082_279_);
v___x_396_ = 0;
return v___x_396_;
}
}
case 14:
{
if (lean_obj_tag(v_e_u2082_279_) == 14)
{
lean_object* v_fvarId_397_; lean_object* v_fvarId_398_; uint8_t v___x_399_; 
v_fvarId_397_ = lean_ctor_get(v_e_u2081_278_, 0);
v_fvarId_398_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fvarId_398_);
lean_dec_ref_known(v_e_u2082_279_, 1);
v___x_399_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_397_, v_fvarId_398_, v_a_280_);
lean_dec(v_fvarId_398_);
return v___x_399_;
}
else
{
uint8_t v___x_400_; 
lean_dec(v_e_u2082_279_);
v___x_400_ = 0;
return v___x_400_;
}
}
default: 
{
if (lean_obj_tag(v_e_u2082_279_) == 15)
{
lean_object* v_fvarId_401_; lean_object* v_fvarId_402_; uint8_t v___x_403_; 
v_fvarId_401_ = lean_ctor_get(v_e_u2081_278_, 0);
v_fvarId_402_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fvarId_402_);
lean_dec_ref_known(v_e_u2082_279_, 1);
v___x_403_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_401_, v_fvarId_402_, v_a_280_);
lean_dec(v_fvarId_402_);
return v___x_403_;
}
else
{
uint8_t v___x_404_; 
lean_dec(v_e_u2082_279_);
v___x_404_ = 0;
return v___x_404_;
}
}
}
v___jp_281_:
{
uint8_t v___x_287_; 
v___x_287_ = lean_name_eq(v_f_u2081_282_, v_f_u2082_284_);
lean_dec(v_f_u2082_284_);
if (v___x_287_ == 0)
{
lean_dec_ref(v_as_u2082_285_);
return v___x_287_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_as_u2081_283_, v_as_u2082_285_, v___y_286_);
return v___x_288_;
}
}
v___jp_289_:
{
uint8_t v___x_295_; 
v___x_295_ = lean_nat_dec_eq(v_i_u2081_290_, v_i_u2082_292_);
lean_dec(v_i_u2082_292_);
if (v___x_295_ == 0)
{
lean_dec(v_v_u2082_293_);
return v___x_295_;
}
else
{
uint8_t v___x_296_; 
v___x_296_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_v_u2081_291_, v_v_u2082_293_, v___y_294_);
lean_dec(v_v_u2082_293_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue___boxed(lean_object* v_pu_405_, lean_object* v_e_u2081_406_, lean_object* v_e_u2082_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_pu_boxed_409_; uint8_t v_res_410_; lean_object* v_r_411_; 
v_pu_boxed_409_ = lean_unbox(v_pu_405_);
v_res_410_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_boxed_409_, v_e_u2081_406_, v_e_u2082_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec(v_e_u2081_406_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(lean_object* v_fvarId_u2081_412_, lean_object* v_fvarId_u2082_413_, lean_object* v_x_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; 
lean_inc(v_a_415_);
v___x_416_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_413_, v_fvarId_u2081_412_, v_a_415_);
v___x_417_ = lean_apply_1(v_x_414_, v___x_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg___boxed(lean_object* v_fvarId_u2081_418_, lean_object* v_fvarId_u2082_419_, lean_object* v_x_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(v_fvarId_u2081_418_, v_fvarId_u2082_419_, v_x_420_, v_a_421_);
lean_dec(v_a_421_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar(lean_object* v_00_u03b1_423_, lean_object* v_fvarId_u2081_424_, lean_object* v_fvarId_u2082_425_, lean_object* v_x_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
lean_inc(v_a_427_);
v___x_428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_425_, v_fvarId_u2081_424_, v_a_427_);
v___x_429_ = lean_apply_1(v_x_426_, v___x_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___boxed(lean_object* v_00_u03b1_430_, lean_object* v_fvarId_u2081_431_, lean_object* v_fvarId_u2082_432_, lean_object* v_x_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar(v_00_u03b1_430_, v_fvarId_u2081_431_, v_fvarId_u2082_432_, v_x_433_, v_a_434_);
lean_dec(v_a_434_);
return v_res_435_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(lean_object* v_params_u2081_436_, lean_object* v_params_u2082_437_, lean_object* v_x_438_, lean_object* v_i_439_, lean_object* v_a_440_){
_start:
{
lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_441_ = lean_array_get_size(v_params_u2081_436_);
v___x_442_ = lean_nat_dec_lt(v_i_439_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; uint8_t v___x_444_; 
lean_dec(v_i_439_);
v___x_443_ = lean_apply_1(v_x_438_, v_a_440_);
v___x_444_ = lean_unbox(v___x_443_);
return v___x_444_;
}
else
{
lean_object* v_p_u2081_445_; lean_object* v_fvarId_446_; lean_object* v_type_447_; lean_object* v_p_u2082_448_; lean_object* v_fvarId_449_; lean_object* v_type_450_; uint8_t v___x_451_; 
v_p_u2081_445_ = lean_array_fget_borrowed(v_params_u2081_436_, v_i_439_);
v_fvarId_446_ = lean_ctor_get(v_p_u2081_445_, 0);
v_type_447_ = lean_ctor_get(v_p_u2081_445_, 2);
v_p_u2082_448_ = lean_array_fget_borrowed(v_params_u2082_437_, v_i_439_);
v_fvarId_449_ = lean_ctor_get(v_p_u2082_448_, 0);
v_type_450_ = lean_ctor_get(v_p_u2082_448_, 2);
v___x_451_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_447_, v_type_450_, v_a_440_);
if (v___x_451_ == 0)
{
lean_dec(v_a_440_);
lean_dec(v_i_439_);
lean_dec_ref(v_x_438_);
return v___x_451_;
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; 
v___x_452_ = lean_unsigned_to_nat(1u);
v___x_453_ = lean_nat_add(v_i_439_, v___x_452_);
lean_dec(v_i_439_);
lean_inc(v_fvarId_446_);
lean_inc(v_fvarId_449_);
v___x_454_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_449_, v_fvarId_446_, v_a_440_);
v_i_439_ = v___x_453_;
v_a_440_ = v___x_454_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg___boxed(lean_object* v_params_u2081_456_, lean_object* v_params_u2082_457_, lean_object* v_x_458_, lean_object* v_i_459_, lean_object* v_a_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_456_, v_params_u2082_457_, v_x_458_, v_i_459_, v_a_460_);
lean_dec_ref(v_params_u2082_457_);
lean_dec_ref(v_params_u2081_456_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(uint8_t v_pu_463_, lean_object* v_params_u2081_464_, lean_object* v_params_u2082_465_, lean_object* v_x_466_, lean_object* v_h_467_, lean_object* v_i_468_, lean_object* v_a_469_){
_start:
{
uint8_t v___x_470_; 
lean_inc(v_a_469_);
v___x_470_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_464_, v_params_u2082_465_, v_x_466_, v_i_468_, v_a_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___boxed(lean_object* v_pu_471_, lean_object* v_params_u2081_472_, lean_object* v_params_u2082_473_, lean_object* v_x_474_, lean_object* v_h_475_, lean_object* v_i_476_, lean_object* v_a_477_){
_start:
{
uint8_t v_pu_boxed_478_; uint8_t v_res_479_; lean_object* v_r_480_; 
v_pu_boxed_478_ = lean_unbox(v_pu_471_);
v_res_479_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(v_pu_boxed_478_, v_params_u2081_472_, v_params_u2082_473_, v_x_474_, v_h_475_, v_i_476_, v_a_477_);
lean_dec(v_a_477_);
lean_dec_ref(v_params_u2082_473_);
lean_dec_ref(v_params_u2081_472_);
v_r_480_ = lean_box(v_res_479_);
return v_r_480_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(lean_object* v_params_u2081_481_, lean_object* v_params_u2082_482_, lean_object* v_x_483_, lean_object* v_a_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_485_ = lean_array_get_size(v_params_u2082_482_);
v___x_486_ = lean_array_get_size(v_params_u2081_481_);
v___x_487_ = lean_nat_dec_eq(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_dec_ref(v_x_483_);
return v___x_487_;
}
else
{
lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_484_);
v___x_489_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_481_, v_params_u2082_482_, v_x_483_, v___x_488_, v_a_484_);
return v___x_489_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg___boxed(lean_object* v_params_u2081_490_, lean_object* v_params_u2082_491_, lean_object* v_x_492_, lean_object* v_a_493_){
_start:
{
uint8_t v_res_494_; lean_object* v_r_495_; 
v_res_494_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(v_params_u2081_490_, v_params_u2082_491_, v_x_492_, v_a_493_);
lean_dec(v_a_493_);
lean_dec_ref(v_params_u2082_491_);
lean_dec_ref(v_params_u2081_490_);
v_r_495_ = lean_box(v_res_494_);
return v_r_495_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams(uint8_t v_pu_496_, lean_object* v_params_u2081_497_, lean_object* v_params_u2082_498_, lean_object* v_x_499_, lean_object* v_a_500_){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_501_ = lean_array_get_size(v_params_u2082_498_);
v___x_502_ = lean_array_get_size(v_params_u2081_497_);
v___x_503_ = lean_nat_dec_eq(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_dec_ref(v_x_499_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_500_);
v___x_505_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_497_, v_params_u2082_498_, v_x_499_, v___x_504_, v_a_500_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___boxed(lean_object* v_pu_506_, lean_object* v_params_u2081_507_, lean_object* v_params_u2082_508_, lean_object* v_x_509_, lean_object* v_a_510_){
_start:
{
uint8_t v_pu_boxed_511_; uint8_t v_res_512_; lean_object* v_r_513_; 
v_pu_boxed_511_ = lean_unbox(v_pu_506_);
v_res_512_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams(v_pu_boxed_511_, v_params_u2081_507_, v_params_u2082_508_, v_x_509_, v_a_510_);
lean_dec(v_a_510_);
lean_dec_ref(v_params_u2082_508_);
lean_dec_ref(v_params_u2081_507_);
v_r_513_ = lean_box(v_res_512_);
return v_r_513_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(lean_object* v_hi_514_, lean_object* v_pivot_515_, lean_object* v_as_516_, lean_object* v_i_517_, lean_object* v_k_518_){
_start:
{
uint8_t v___y_530_; uint8_t v___x_531_; 
v___x_531_ = lean_nat_dec_lt(v_k_518_, v_hi_514_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v_k_518_);
v___x_532_ = lean_array_fswap(v_as_516_, v_i_517_, v_hi_514_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v_i_517_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = lean_array_fget_borrowed(v_as_516_, v_k_518_);
switch(lean_obj_tag(v___x_534_))
{
case 0:
{
switch(lean_obj_tag(v_pivot_515_))
{
case 2:
{
goto v___jp_523_;
}
case 0:
{
lean_object* v_ctorName_535_; lean_object* v_ctorName_536_; uint8_t v___x_537_; 
v_ctorName_535_ = lean_ctor_get(v___x_534_, 0);
v_ctorName_536_ = lean_ctor_get(v_pivot_515_, 0);
v___x_537_ = l_Lean_Name_lt(v_ctorName_535_, v_ctorName_536_);
v___y_530_ = v___x_537_;
goto v___jp_529_;
}
default: 
{
goto v___jp_519_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_pivot_515_))
{
case 2:
{
goto v___jp_523_;
}
case 1:
{
lean_object* v_info_538_; lean_object* v_info_539_; lean_object* v_name_540_; lean_object* v_name_541_; uint8_t v___x_542_; 
v_info_538_ = lean_ctor_get(v___x_534_, 0);
v_info_539_ = lean_ctor_get(v_pivot_515_, 0);
v_name_540_ = lean_ctor_get(v_info_538_, 0);
v_name_541_ = lean_ctor_get(v_info_539_, 0);
v___x_542_ = l_Lean_Name_lt(v_name_540_, v_name_541_);
v___y_530_ = v___x_542_;
goto v___jp_529_;
}
default: 
{
goto v___jp_519_;
}
}
}
default: 
{
goto v___jp_519_;
}
}
}
v___jp_519_:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_add(v_k_518_, v___x_520_);
lean_dec(v_k_518_);
v_k_518_ = v___x_521_;
goto _start;
}
v___jp_523_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_524_ = lean_array_fswap(v_as_516_, v_i_517_, v_k_518_);
v___x_525_ = lean_unsigned_to_nat(1u);
v___x_526_ = lean_nat_add(v_i_517_, v___x_525_);
lean_dec(v_i_517_);
v___x_527_ = lean_nat_add(v_k_518_, v___x_525_);
lean_dec(v_k_518_);
v_as_516_ = v___x_524_;
v_i_517_ = v___x_526_;
v_k_518_ = v___x_527_;
goto _start;
}
v___jp_529_:
{
if (v___y_530_ == 0)
{
goto v___jp_519_;
}
else
{
goto v___jp_523_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg___boxed(lean_object* v_hi_543_, lean_object* v_pivot_544_, lean_object* v_as_545_, lean_object* v_i_546_, lean_object* v_k_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_543_, v_pivot_544_, v_as_545_, v_i_546_, v_k_547_);
lean_dec_ref(v_pivot_544_);
lean_dec(v_hi_543_);
return v_res_548_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(uint8_t v___x_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
switch(lean_obj_tag(v_x_550_))
{
case 0:
{
switch(lean_obj_tag(v_x_551_))
{
case 2:
{
return v___x_549_;
}
case 0:
{
lean_object* v_ctorName_552_; lean_object* v_ctorName_553_; uint8_t v___x_554_; 
v_ctorName_552_ = lean_ctor_get(v_x_550_, 0);
v_ctorName_553_ = lean_ctor_get(v_x_551_, 0);
v___x_554_ = l_Lean_Name_lt(v_ctorName_552_, v_ctorName_553_);
return v___x_554_;
}
default: 
{
uint8_t v___x_555_; 
v___x_555_ = 0;
return v___x_555_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_551_))
{
case 2:
{
return v___x_549_;
}
case 1:
{
lean_object* v_info_556_; lean_object* v_info_557_; lean_object* v_name_558_; lean_object* v_name_559_; uint8_t v___x_560_; 
v_info_556_ = lean_ctor_get(v_x_550_, 0);
v_info_557_ = lean_ctor_get(v_x_551_, 0);
v_name_558_ = lean_ctor_get(v_info_556_, 0);
v_name_559_ = lean_ctor_get(v_info_557_, 0);
v___x_560_ = l_Lean_Name_lt(v_name_558_, v_name_559_);
return v___x_560_;
}
default: 
{
uint8_t v___x_561_; 
v___x_561_ = 0;
return v___x_561_;
}
}
}
default: 
{
uint8_t v___x_562_; 
v___x_562_ = 0;
return v___x_562_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed(lean_object* v___x_563_, lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
uint8_t v___x_426__boxed_566_; uint8_t v_res_567_; lean_object* v_r_568_; 
v___x_426__boxed_566_ = lean_unbox(v___x_563_);
v_res_567_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_426__boxed_566_, v_x_564_, v_x_565_);
lean_dec_ref(v_x_565_);
lean_dec_ref(v_x_564_);
v_r_568_ = lean_box(v_res_567_);
return v_r_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(lean_object* v_n_569_, lean_object* v_as_570_, lean_object* v_lo_571_, lean_object* v_hi_572_){
_start:
{
lean_object* v___y_574_; uint8_t v___x_584_; 
v___x_584_ = lean_nat_dec_lt(v_lo_571_, v_hi_572_);
if (v___x_584_ == 0)
{
lean_dec(v_lo_571_);
return v_as_570_;
}
else
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v_mid_587_; lean_object* v___y_589_; lean_object* v___y_595_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_585_ = lean_nat_add(v_lo_571_, v_hi_572_);
v___x_586_ = lean_unsigned_to_nat(1u);
v_mid_587_ = lean_nat_shiftr(v___x_585_, v___x_586_);
lean_dec(v___x_585_);
v___x_600_ = lean_array_fget_borrowed(v_as_570_, v_mid_587_);
v___x_601_ = lean_array_fget_borrowed(v_as_570_, v_lo_571_);
v___x_602_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_584_, v___x_600_, v___x_601_);
if (v___x_602_ == 0)
{
v___y_595_ = v_as_570_;
goto v___jp_594_;
}
else
{
lean_object* v___x_603_; 
v___x_603_ = lean_array_fswap(v_as_570_, v_lo_571_, v_mid_587_);
v___y_595_ = v___x_603_;
goto v___jp_594_;
}
v___jp_588_:
{
lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_590_ = lean_array_fget_borrowed(v___y_589_, v_mid_587_);
v___x_591_ = lean_array_fget_borrowed(v___y_589_, v_hi_572_);
v___x_592_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_584_, v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v_mid_587_);
v___y_574_ = v___y_589_;
goto v___jp_573_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = lean_array_fswap(v___y_589_, v_mid_587_, v_hi_572_);
lean_dec(v_mid_587_);
v___y_574_ = v___x_593_;
goto v___jp_573_;
}
}
v___jp_594_:
{
lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_596_ = lean_array_fget_borrowed(v___y_595_, v_hi_572_);
v___x_597_ = lean_array_fget_borrowed(v___y_595_, v_lo_571_);
v___x_598_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_584_, v___x_596_, v___x_597_);
if (v___x_598_ == 0)
{
v___y_589_ = v___y_595_;
goto v___jp_588_;
}
else
{
lean_object* v___x_599_; 
v___x_599_ = lean_array_fswap(v___y_595_, v_lo_571_, v_hi_572_);
v___y_589_ = v___x_599_;
goto v___jp_588_;
}
}
}
v___jp_573_:
{
lean_object* v_pivot_575_; lean_object* v___x_576_; lean_object* v_fst_577_; lean_object* v_snd_578_; uint8_t v___x_579_; 
v_pivot_575_ = lean_array_fget(v___y_574_, v_hi_572_);
lean_inc_n(v_lo_571_, 2);
v___x_576_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_572_, v_pivot_575_, v___y_574_, v_lo_571_, v_lo_571_);
lean_dec(v_pivot_575_);
v_fst_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_fst_577_);
v_snd_578_ = lean_ctor_get(v___x_576_, 1);
lean_inc(v_snd_578_);
lean_dec_ref(v___x_576_);
v___x_579_ = lean_nat_dec_le(v_hi_572_, v_fst_577_);
if (v___x_579_ == 0)
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_569_, v_snd_578_, v_lo_571_, v_fst_577_);
v___x_581_ = lean_unsigned_to_nat(1u);
v___x_582_ = lean_nat_add(v_fst_577_, v___x_581_);
lean_dec(v_fst_577_);
v_as_570_ = v___x_580_;
v_lo_571_ = v___x_582_;
goto _start;
}
else
{
lean_dec(v_fst_577_);
lean_dec(v_lo_571_);
return v_snd_578_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___boxed(lean_object* v_n_604_, lean_object* v_as_605_, lean_object* v_lo_606_, lean_object* v_hi_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_604_, v_as_605_, v_lo_606_, v_hi_607_);
lean_dec(v_hi_607_);
lean_dec(v_n_604_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(lean_object* v_alts_609_){
_start:
{
lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_610_ = lean_array_get_size(v_alts_609_);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_nat_dec_eq(v___x_610_, v___x_611_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___y_616_; uint8_t v___x_620_; 
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_sub(v___x_610_, v___x_613_);
v___x_620_ = lean_nat_dec_le(v___x_611_, v___x_614_);
if (v___x_620_ == 0)
{
lean_inc(v___x_614_);
v___y_616_ = v___x_614_;
goto v___jp_615_;
}
else
{
v___y_616_ = v___x_611_;
goto v___jp_615_;
}
v___jp_615_:
{
uint8_t v___x_617_; 
v___x_617_ = lean_nat_dec_le(v___y_616_, v___x_614_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec(v___x_614_);
lean_inc(v___y_616_);
v___x_618_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_610_, v_alts_609_, v___y_616_, v___y_616_);
lean_dec(v___y_616_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_610_, v_alts_609_, v___y_616_, v___x_614_);
lean_dec(v___x_614_);
return v___x_619_;
}
}
}
else
{
return v_alts_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(uint8_t v_pu_621_, lean_object* v_alts_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___boxed(lean_object* v_pu_624_, lean_object* v_alts_625_){
_start:
{
uint8_t v_pu_boxed_626_; lean_object* v_res_627_; 
v_pu_boxed_626_ = lean_unbox(v_pu_624_);
v_res_627_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(v_pu_boxed_626_, v_alts_625_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(lean_object* v_n_628_, lean_object* v_as_629_, lean_object* v_lo_630_, lean_object* v_hi_631_, lean_object* v_w_632_, lean_object* v_hlo_633_, lean_object* v_hhi_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_628_, v_as_629_, v_lo_630_, v_hi_631_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___boxed(lean_object* v_n_636_, lean_object* v_as_637_, lean_object* v_lo_638_, lean_object* v_hi_639_, lean_object* v_w_640_, lean_object* v_hlo_641_, lean_object* v_hhi_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(v_n_636_, v_as_637_, v_lo_638_, v_hi_639_, v_w_640_, v_hlo_641_, v_hhi_642_);
lean_dec(v_hi_639_);
lean_dec(v_n_636_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(lean_object* v_n_644_, lean_object* v_lo_645_, lean_object* v_hi_646_, lean_object* v_hhi_647_, lean_object* v_pivot_648_, lean_object* v_as_649_, lean_object* v_i_650_, lean_object* v_k_651_, lean_object* v_ilo_652_, lean_object* v_ik_653_, lean_object* v_w_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_646_, v_pivot_648_, v_as_649_, v_i_650_, v_k_651_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___boxed(lean_object* v_n_656_, lean_object* v_lo_657_, lean_object* v_hi_658_, lean_object* v_hhi_659_, lean_object* v_pivot_660_, lean_object* v_as_661_, lean_object* v_i_662_, lean_object* v_k_663_, lean_object* v_ilo_664_, lean_object* v_ik_665_, lean_object* v_w_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(v_n_656_, v_lo_657_, v_hi_658_, v_hhi_659_, v_pivot_660_, v_as_661_, v_i_662_, v_k_663_, v_ilo_664_, v_ik_665_, v_w_666_);
lean_dec_ref(v_pivot_660_);
lean_dec(v_hi_658_);
lean_dec(v_lo_657_);
lean_dec(v_n_656_);
return v_res_667_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
if (lean_obj_tag(v_x_669_) == 0)
{
uint8_t v___x_670_; 
v___x_670_ = 1;
return v___x_670_;
}
else
{
uint8_t v___x_671_; 
v___x_671_ = 0;
return v___x_671_;
}
}
else
{
if (lean_obj_tag(v_x_669_) == 0)
{
uint8_t v___x_672_; 
v___x_672_ = 0;
return v___x_672_;
}
else
{
lean_object* v_val_673_; lean_object* v_val_674_; uint8_t v___x_675_; 
v_val_673_ = lean_ctor_get(v_x_668_, 0);
v_val_674_ = lean_ctor_get(v_x_669_, 0);
v___x_675_ = lean_nat_dec_eq(v_val_673_, v_val_674_);
return v___x_675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3___boxed(lean_object* v_x_676_, lean_object* v_x_677_){
_start:
{
uint8_t v_res_678_; lean_object* v_r_679_; 
v_res_678_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(v_x_676_, v_x_677_);
lean_dec(v_x_677_);
lean_dec(v_x_676_);
v_r_679_ = lean_box(v_res_678_);
return v_r_679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(uint8_t v_pu_683_, lean_object* v_as_684_, size_t v_sz_685_, size_t v_i_686_, lean_object* v_b_687_, lean_object* v___y_688_){
_start:
{
lean_object* v_a_690_; uint8_t v___x_694_; 
v___x_694_ = lean_usize_dec_lt(v_i_686_, v_sz_685_);
if (v___x_694_ == 0)
{
return v_b_687_;
}
else
{
lean_object* v_snd_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_783_; 
v_snd_695_ = lean_ctor_get(v_b_687_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_b_687_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_b_687_, 0);
lean_dec(v_unused_784_);
v___x_697_ = v_b_687_;
v_isShared_698_ = v_isSharedCheck_783_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snd_695_);
lean_dec(v_b_687_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_783_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_array_699_; lean_object* v_start_700_; lean_object* v_stop_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_array_699_ = lean_ctor_get(v_snd_695_, 0);
v_start_700_ = lean_ctor_get(v_snd_695_, 1);
v_stop_701_ = lean_ctor_get(v_snd_695_, 2);
v___x_702_ = lean_box(0);
v___x_703_ = lean_nat_dec_lt(v_start_700_, v_stop_701_);
if (v___x_703_ == 0)
{
lean_object* v___x_705_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_702_);
v___x_705_ = v___x_697_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_snd_695_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
return v___x_705_;
}
}
else
{
lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_779_; 
lean_inc(v_stop_701_);
lean_inc(v_start_700_);
lean_inc_ref(v_array_699_);
v_isSharedCheck_779_ = !lean_is_exclusive(v_snd_695_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; lean_object* v_unused_781_; lean_object* v_unused_782_; 
v_unused_780_ = lean_ctor_get(v_snd_695_, 2);
lean_dec(v_unused_780_);
v_unused_781_ = lean_ctor_get(v_snd_695_, 1);
lean_dec(v_unused_781_);
v_unused_782_ = lean_ctor_get(v_snd_695_, 0);
lean_dec(v_unused_782_);
v___x_708_ = v_snd_695_;
v_isShared_709_ = v_isSharedCheck_779_;
goto v_resetjp_707_;
}
else
{
lean_dec(v_snd_695_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_779_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v_a_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v_a_710_ = lean_array_uget_borrowed(v_as_684_, v_i_686_);
v___x_711_ = lean_array_fget(v_array_699_, v_start_700_);
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_start_700_, v___x_712_);
lean_dec(v_start_700_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_713_);
v___x_715_ = v___x_708_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_array_699_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_stop_701_);
v___x_715_ = v_reuseFailAlloc_778_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
uint8_t v___y_717_; 
switch(lean_obj_tag(v_a_710_))
{
case 0:
{
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_ctorName_726_; lean_object* v_params_727_; lean_object* v_code_728_; lean_object* v_ctorName_729_; lean_object* v_params_730_; lean_object* v_code_731_; uint8_t v___x_732_; 
v_ctorName_726_ = lean_ctor_get(v_a_710_, 0);
v_params_727_ = lean_ctor_get(v_a_710_, 1);
v_code_728_ = lean_ctor_get(v_a_710_, 2);
v_ctorName_729_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_ctorName_729_);
v_params_730_ = lean_ctor_get(v___x_711_, 1);
lean_inc_ref(v_params_730_);
v_code_731_ = lean_ctor_get(v___x_711_, 2);
lean_inc_ref(v_code_731_);
lean_dec_ref_known(v___x_711_, 3);
v___x_732_ = lean_name_eq(v_ctorName_726_, v_ctorName_729_);
lean_dec(v_ctorName_729_);
if (v___x_732_ == 0)
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec_ref(v_code_731_);
lean_dec_ref(v_params_730_);
lean_del_object(v___x_697_);
v___x_733_ = lean_box(v___x_732_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v___x_733_);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v___x_715_);
return v___x_735_;
}
else
{
lean_object* v___x_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v___x_736_ = lean_array_get_size(v_params_730_);
v___x_737_ = lean_array_get_size(v_params_727_);
v___x_738_ = lean_nat_dec_eq(v___x_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_dec_ref(v_code_731_);
lean_dec_ref(v_params_730_);
v___y_717_ = v___x_738_;
goto v___jp_716_;
}
else
{
lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_739_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_688_);
lean_inc_ref(v_code_728_);
v___x_740_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_683_, v_code_728_, v_code_731_, v_params_727_, v_params_730_, v___x_739_, v___y_688_);
lean_dec_ref(v_params_730_);
if (v___x_740_ == 0)
{
v___y_717_ = v___x_740_;
goto v___jp_716_;
}
else
{
lean_object* v___x_741_; 
lean_del_object(v___x_697_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_702_);
lean_ctor_set(v___x_741_, 1, v___x_715_);
v_a_690_ = v___x_741_;
goto v___jp_689_;
}
}
}
}
else
{
lean_dec(v___x_711_);
lean_del_object(v___x_697_);
goto v___jp_723_;
}
}
case 1:
{
lean_del_object(v___x_697_);
if (lean_obj_tag(v___x_711_) == 1)
{
lean_object* v_info_742_; lean_object* v_code_743_; lean_object* v_info_744_; lean_object* v_code_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_764_; 
v_info_742_ = lean_ctor_get(v_a_710_, 0);
v_code_743_ = lean_ctor_get(v_a_710_, 1);
v_info_744_ = lean_ctor_get(v___x_711_, 0);
v_code_745_ = lean_ctor_get(v___x_711_, 1);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_764_ == 0)
{
v___x_747_ = v___x_711_;
v_isShared_748_ = v_isSharedCheck_764_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_code_745_);
lean_inc(v_info_744_);
lean_dec(v___x_711_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_764_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
uint8_t v___x_749_; 
v___x_749_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_info_742_, v_info_744_);
lean_dec_ref(v_info_744_);
if (v___x_749_ == 0)
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
lean_dec_ref(v_code_745_);
v___x_750_ = lean_box(v___x_749_);
v___x_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
lean_ctor_set(v___x_747_, 1, v___x_715_);
lean_ctor_set(v___x_747_, 0, v___x_751_);
v___x_753_ = v___x_747_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_715_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
else
{
uint8_t v___x_755_; 
lean_inc(v___y_688_);
lean_inc_ref(v_code_743_);
v___x_755_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_683_, v_code_743_, v_code_745_, v___y_688_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_759_; 
v___x_756_ = lean_box(v___x_755_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v___x_756_);
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
lean_ctor_set(v___x_747_, 1, v___x_715_);
lean_ctor_set(v___x_747_, 0, v___x_757_);
v___x_759_ = v___x_747_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v___x_715_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
else
{
lean_object* v___x_762_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set_tag(v___x_747_, 0);
lean_ctor_set(v___x_747_, 1, v___x_715_);
lean_ctor_set(v___x_747_, 0, v___x_702_);
v___x_762_ = v___x_747_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___x_715_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
v_a_690_ = v___x_762_;
goto v___jp_689_;
}
}
}
}
}
else
{
lean_dec(v___x_711_);
goto v___jp_723_;
}
}
default: 
{
lean_del_object(v___x_697_);
if (lean_obj_tag(v___x_711_) == 2)
{
lean_object* v_code_765_; lean_object* v_code_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_777_; 
v_code_765_ = lean_ctor_get(v_a_710_, 0);
v_code_766_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_777_ == 0)
{
v___x_768_ = v___x_711_;
v_isShared_769_ = v_isSharedCheck_777_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_code_766_);
lean_dec(v___x_711_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_777_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
uint8_t v___x_770_; 
lean_inc(v___y_688_);
lean_inc_ref(v_code_765_);
v___x_770_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_683_, v_code_765_, v_code_766_, v___y_688_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_771_ = lean_box(v___x_770_);
if (v_isShared_769_ == 0)
{
lean_ctor_set_tag(v___x_768_, 1);
lean_ctor_set(v___x_768_, 0, v___x_771_);
v___x_773_ = v___x_768_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v___x_771_);
v___x_773_ = v_reuseFailAlloc_775_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_715_);
return v___x_774_;
}
}
else
{
lean_object* v___x_776_; 
lean_del_object(v___x_768_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_702_);
lean_ctor_set(v___x_776_, 1, v___x_715_);
v_a_690_ = v___x_776_;
goto v___jp_689_;
}
}
}
else
{
lean_dec(v___x_711_);
goto v___jp_723_;
}
}
}
v___jp_716_:
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_718_ = lean_box(v___y_717_);
v___x_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_715_);
lean_ctor_set(v___x_697_, 0, v___x_719_);
v___x_721_ = v___x_697_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_715_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
v___jp_723_:
{
lean_object* v___x_724_; lean_object* v___x_725_; 
v___x_724_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0));
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___x_715_);
return v___x_725_;
}
}
}
}
}
}
v___jp_689_:
{
size_t v___x_691_; size_t v___x_692_; 
v___x_691_ = ((size_t)1ULL);
v___x_692_ = lean_usize_add(v_i_686_, v___x_691_);
v_i_686_ = v___x_692_;
v_b_687_ = v_a_690_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(uint8_t v_pu_785_, lean_object* v_alts_u2081_786_, lean_object* v_alts_u2082_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v___x_789_ = lean_array_get_size(v_alts_u2081_786_);
v___x_790_ = lean_array_get_size(v_alts_u2082_787_);
v___x_791_ = lean_nat_dec_eq(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_dec_ref(v_alts_u2082_787_);
lean_dec_ref(v_alts_u2081_786_);
return v___x_791_;
}
else
{
lean_object* v_alts_u2081_792_; lean_object* v_alts_u2082_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; size_t v_sz_799_; size_t v___x_800_; lean_object* v___x_801_; lean_object* v_fst_802_; 
v_alts_u2081_792_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2081_786_);
v_alts_u2082_793_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2082_787_);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v_alts_u2082_793_);
v___x_796_ = l_Array_toSubarray___redArg(v_alts_u2082_793_, v___x_794_, v___x_795_);
v___x_797_ = lean_box(0);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___x_796_);
v_sz_799_ = lean_array_size(v_alts_u2081_792_);
v___x_800_ = ((size_t)0ULL);
v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_785_, v_alts_u2081_792_, v_sz_799_, v___x_800_, v___x_798_, v_a_788_);
lean_dec_ref(v_alts_u2081_792_);
v_fst_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_fst_802_);
lean_dec_ref(v___x_801_);
if (lean_obj_tag(v_fst_802_) == 0)
{
return v___x_791_;
}
else
{
lean_object* v_val_803_; uint8_t v___x_804_; 
v_val_803_ = lean_ctor_get(v_fst_802_, 0);
lean_inc(v_val_803_);
lean_dec_ref_known(v_fst_802_, 1);
v___x_804_ = lean_unbox(v_val_803_);
lean_dec(v_val_803_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqv(uint8_t v_pu_805_, lean_object* v_code_u2081_806_, lean_object* v_code_u2082_807_, lean_object* v_a_808_){
_start:
{
switch(lean_obj_tag(v_code_u2081_806_))
{
case 0:
{
if (lean_obj_tag(v_code_u2082_807_) == 0)
{
lean_object* v_decl_809_; lean_object* v_decl_810_; lean_object* v_k_811_; lean_object* v_k_812_; lean_object* v_fvarId_813_; lean_object* v_type_814_; lean_object* v_value_815_; lean_object* v_fvarId_816_; lean_object* v_type_817_; lean_object* v_value_818_; uint8_t v___x_819_; 
v_decl_809_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc_ref(v_decl_809_);
v_decl_810_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc_ref(v_decl_810_);
v_k_811_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc_ref(v_k_811_);
lean_dec_ref_known(v_code_u2081_806_, 2);
v_k_812_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc_ref(v_k_812_);
lean_dec_ref_known(v_code_u2082_807_, 2);
v_fvarId_813_ = lean_ctor_get(v_decl_809_, 0);
lean_inc(v_fvarId_813_);
v_type_814_ = lean_ctor_get(v_decl_809_, 2);
lean_inc_ref(v_type_814_);
v_value_815_ = lean_ctor_get(v_decl_809_, 3);
lean_inc(v_value_815_);
lean_dec_ref(v_decl_809_);
v_fvarId_816_ = lean_ctor_get(v_decl_810_, 0);
lean_inc(v_fvarId_816_);
v_type_817_ = lean_ctor_get(v_decl_810_, 2);
lean_inc_ref(v_type_817_);
v_value_818_ = lean_ctor_get(v_decl_810_, 3);
lean_inc(v_value_818_);
lean_dec_ref(v_decl_810_);
v___x_819_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_814_, v_type_817_, v_a_808_);
lean_dec_ref(v_type_817_);
lean_dec_ref(v_type_814_);
if (v___x_819_ == 0)
{
lean_dec(v_value_818_);
lean_dec(v_fvarId_816_);
lean_dec(v_value_815_);
lean_dec(v_fvarId_813_);
lean_dec_ref(v_k_812_);
lean_dec_ref(v_k_811_);
lean_dec(v_a_808_);
return v___x_819_;
}
else
{
uint8_t v___x_820_; 
v___x_820_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_805_, v_value_815_, v_value_818_, v_a_808_);
lean_dec(v_value_815_);
if (v___x_820_ == 0)
{
lean_dec(v_fvarId_816_);
lean_dec(v_fvarId_813_);
lean_dec_ref(v_k_812_);
lean_dec_ref(v_k_811_);
lean_dec(v_a_808_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_816_, v_fvarId_813_, v_a_808_);
v_code_u2081_806_ = v_k_811_;
v_code_u2082_807_ = v_k_812_;
v_a_808_ = v___x_821_;
goto _start;
}
}
}
else
{
uint8_t v___x_823_; 
lean_dec_ref_known(v_code_u2081_806_, 2);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_823_ = 0;
return v___x_823_;
}
}
case 1:
{
if (lean_obj_tag(v_code_u2082_807_) == 1)
{
lean_object* v_decl_824_; lean_object* v_decl_825_; lean_object* v_k_826_; lean_object* v_k_827_; lean_object* v_fvarId_828_; lean_object* v_params_829_; lean_object* v_type_830_; lean_object* v_value_831_; lean_object* v_fvarId_832_; lean_object* v_params_833_; lean_object* v_type_834_; lean_object* v_value_835_; uint8_t v___x_836_; 
v_decl_824_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc_ref(v_decl_824_);
v_decl_825_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc_ref(v_decl_825_);
v_k_826_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc_ref(v_k_826_);
lean_dec_ref_known(v_code_u2081_806_, 2);
v_k_827_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc_ref(v_k_827_);
lean_dec_ref_known(v_code_u2082_807_, 2);
v_fvarId_828_ = lean_ctor_get(v_decl_824_, 0);
lean_inc(v_fvarId_828_);
v_params_829_ = lean_ctor_get(v_decl_824_, 2);
lean_inc_ref(v_params_829_);
v_type_830_ = lean_ctor_get(v_decl_824_, 3);
lean_inc_ref(v_type_830_);
v_value_831_ = lean_ctor_get(v_decl_824_, 4);
lean_inc_ref(v_value_831_);
lean_dec_ref(v_decl_824_);
v_fvarId_832_ = lean_ctor_get(v_decl_825_, 0);
lean_inc(v_fvarId_832_);
v_params_833_ = lean_ctor_get(v_decl_825_, 2);
lean_inc_ref(v_params_833_);
v_type_834_ = lean_ctor_get(v_decl_825_, 3);
lean_inc_ref(v_type_834_);
v_value_835_ = lean_ctor_get(v_decl_825_, 4);
lean_inc_ref(v_value_835_);
lean_dec_ref(v_decl_825_);
v___x_836_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_830_, v_type_834_, v_a_808_);
lean_dec_ref(v_type_834_);
lean_dec_ref(v_type_830_);
if (v___x_836_ == 0)
{
lean_dec_ref(v_value_835_);
lean_dec_ref(v_params_833_);
lean_dec(v_fvarId_832_);
lean_dec_ref(v_value_831_);
lean_dec_ref(v_params_829_);
lean_dec(v_fvarId_828_);
lean_dec_ref(v_k_827_);
lean_dec_ref(v_k_826_);
lean_dec(v_a_808_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_837_ = lean_array_get_size(v_params_833_);
v___x_838_ = lean_array_get_size(v_params_829_);
v___x_839_ = lean_nat_dec_eq(v___x_837_, v___x_838_);
if (v___x_839_ == 0)
{
lean_dec_ref(v_value_835_);
lean_dec_ref(v_params_833_);
lean_dec(v_fvarId_832_);
lean_dec_ref(v_value_831_);
lean_dec_ref(v_params_829_);
lean_dec(v_fvarId_828_);
lean_dec_ref(v_k_827_);
lean_dec_ref(v_k_826_);
lean_dec(v_a_808_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_808_);
v___x_841_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_805_, v_value_831_, v_value_835_, v_params_829_, v_params_833_, v___x_840_, v_a_808_);
lean_dec_ref(v_params_833_);
lean_dec_ref(v_params_829_);
if (v___x_841_ == 0)
{
lean_dec(v_fvarId_832_);
lean_dec(v_fvarId_828_);
lean_dec_ref(v_k_827_);
lean_dec_ref(v_k_826_);
lean_dec(v_a_808_);
return v___x_841_;
}
else
{
lean_object* v___x_842_; 
v___x_842_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_832_, v_fvarId_828_, v_a_808_);
v_code_u2081_806_ = v_k_826_;
v_code_u2082_807_ = v_k_827_;
v_a_808_ = v___x_842_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_844_; 
lean_dec_ref_known(v_code_u2081_806_, 2);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_844_ = 0;
return v___x_844_;
}
}
case 2:
{
if (lean_obj_tag(v_code_u2082_807_) == 2)
{
lean_object* v_decl_845_; lean_object* v_decl_846_; lean_object* v_k_847_; lean_object* v_k_848_; lean_object* v_fvarId_849_; lean_object* v_params_850_; lean_object* v_type_851_; lean_object* v_value_852_; lean_object* v_fvarId_853_; lean_object* v_params_854_; lean_object* v_type_855_; lean_object* v_value_856_; uint8_t v___x_857_; 
v_decl_845_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc_ref(v_decl_845_);
v_decl_846_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc_ref(v_decl_846_);
v_k_847_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc_ref(v_k_847_);
lean_dec_ref_known(v_code_u2081_806_, 2);
v_k_848_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc_ref(v_k_848_);
lean_dec_ref_known(v_code_u2082_807_, 2);
v_fvarId_849_ = lean_ctor_get(v_decl_845_, 0);
lean_inc(v_fvarId_849_);
v_params_850_ = lean_ctor_get(v_decl_845_, 2);
lean_inc_ref(v_params_850_);
v_type_851_ = lean_ctor_get(v_decl_845_, 3);
lean_inc_ref(v_type_851_);
v_value_852_ = lean_ctor_get(v_decl_845_, 4);
lean_inc_ref(v_value_852_);
lean_dec_ref(v_decl_845_);
v_fvarId_853_ = lean_ctor_get(v_decl_846_, 0);
lean_inc(v_fvarId_853_);
v_params_854_ = lean_ctor_get(v_decl_846_, 2);
lean_inc_ref(v_params_854_);
v_type_855_ = lean_ctor_get(v_decl_846_, 3);
lean_inc_ref(v_type_855_);
v_value_856_ = lean_ctor_get(v_decl_846_, 4);
lean_inc_ref(v_value_856_);
lean_dec_ref(v_decl_846_);
v___x_857_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_851_, v_type_855_, v_a_808_);
lean_dec_ref(v_type_855_);
lean_dec_ref(v_type_851_);
if (v___x_857_ == 0)
{
lean_dec_ref(v_value_856_);
lean_dec_ref(v_params_854_);
lean_dec(v_fvarId_853_);
lean_dec_ref(v_value_852_);
lean_dec_ref(v_params_850_);
lean_dec(v_fvarId_849_);
lean_dec_ref(v_k_848_);
lean_dec_ref(v_k_847_);
lean_dec(v_a_808_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_858_ = lean_array_get_size(v_params_854_);
v___x_859_ = lean_array_get_size(v_params_850_);
v___x_860_ = lean_nat_dec_eq(v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
lean_dec_ref(v_value_856_);
lean_dec_ref(v_params_854_);
lean_dec(v_fvarId_853_);
lean_dec_ref(v_value_852_);
lean_dec_ref(v_params_850_);
lean_dec(v_fvarId_849_);
lean_dec_ref(v_k_848_);
lean_dec_ref(v_k_847_);
lean_dec(v_a_808_);
return v___x_860_;
}
else
{
lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_808_);
v___x_862_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_805_, v_value_852_, v_value_856_, v_params_850_, v_params_854_, v___x_861_, v_a_808_);
lean_dec_ref(v_params_854_);
lean_dec_ref(v_params_850_);
if (v___x_862_ == 0)
{
lean_dec(v_fvarId_853_);
lean_dec(v_fvarId_849_);
lean_dec_ref(v_k_848_);
lean_dec_ref(v_k_847_);
lean_dec(v_a_808_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_853_, v_fvarId_849_, v_a_808_);
v_code_u2081_806_ = v_k_847_;
v_code_u2082_807_ = v_k_848_;
v_a_808_ = v___x_863_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_865_; 
lean_dec_ref_known(v_code_u2081_806_, 2);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_865_ = 0;
return v___x_865_;
}
}
case 3:
{
if (lean_obj_tag(v_code_u2082_807_) == 3)
{
lean_object* v_fvarId_866_; lean_object* v_args_867_; lean_object* v_fvarId_868_; lean_object* v_args_869_; uint8_t v___x_870_; 
v_fvarId_866_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc(v_fvarId_866_);
v_args_867_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc_ref(v_args_867_);
lean_dec_ref_known(v_code_u2081_806_, 2);
v_fvarId_868_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc(v_fvarId_868_);
v_args_869_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc_ref(v_args_869_);
lean_dec_ref_known(v_code_u2082_807_, 2);
v___x_870_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_866_, v_fvarId_868_, v_a_808_);
lean_dec(v_fvarId_868_);
lean_dec(v_fvarId_866_);
if (v___x_870_ == 0)
{
lean_dec_ref(v_args_869_);
lean_dec_ref(v_args_867_);
lean_dec(v_a_808_);
return v___x_870_;
}
else
{
uint8_t v___x_871_; 
v___x_871_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_805_, v_args_867_, v_args_869_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_args_867_);
return v___x_871_;
}
}
else
{
uint8_t v___x_872_; 
lean_dec_ref_known(v_code_u2081_806_, 2);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_872_ = 0;
return v___x_872_;
}
}
case 4:
{
if (lean_obj_tag(v_code_u2082_807_) == 4)
{
lean_object* v_cases_873_; lean_object* v_cases_874_; lean_object* v_resultType_875_; lean_object* v_discr_876_; lean_object* v_alts_877_; lean_object* v_resultType_878_; lean_object* v_discr_879_; lean_object* v_alts_880_; uint8_t v___x_881_; 
v_cases_873_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc_ref(v_cases_873_);
lean_dec_ref_known(v_code_u2081_806_, 1);
v_cases_874_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc_ref(v_cases_874_);
lean_dec_ref_known(v_code_u2082_807_, 1);
v_resultType_875_ = lean_ctor_get(v_cases_873_, 1);
lean_inc_ref(v_resultType_875_);
v_discr_876_ = lean_ctor_get(v_cases_873_, 2);
lean_inc(v_discr_876_);
v_alts_877_ = lean_ctor_get(v_cases_873_, 3);
lean_inc_ref(v_alts_877_);
lean_dec_ref(v_cases_873_);
v_resultType_878_ = lean_ctor_get(v_cases_874_, 1);
lean_inc_ref(v_resultType_878_);
v_discr_879_ = lean_ctor_get(v_cases_874_, 2);
lean_inc(v_discr_879_);
v_alts_880_ = lean_ctor_get(v_cases_874_, 3);
lean_inc_ref(v_alts_880_);
lean_dec_ref(v_cases_874_);
v___x_881_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_discr_876_, v_discr_879_, v_a_808_);
lean_dec(v_discr_879_);
lean_dec(v_discr_876_);
if (v___x_881_ == 0)
{
lean_dec_ref(v_alts_880_);
lean_dec_ref(v_resultType_878_);
lean_dec_ref(v_alts_877_);
lean_dec_ref(v_resultType_875_);
lean_dec(v_a_808_);
return v___x_881_;
}
else
{
uint8_t v___x_882_; 
v___x_882_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_resultType_875_, v_resultType_878_, v_a_808_);
lean_dec_ref(v_resultType_878_);
lean_dec_ref(v_resultType_875_);
if (v___x_882_ == 0)
{
lean_dec_ref(v_alts_880_);
lean_dec_ref(v_alts_877_);
lean_dec(v_a_808_);
return v___x_882_;
}
else
{
uint8_t v___x_883_; 
v___x_883_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_805_, v_alts_877_, v_alts_880_, v_a_808_);
lean_dec(v_a_808_);
return v___x_883_;
}
}
}
else
{
uint8_t v___x_884_; 
lean_dec_ref_known(v_code_u2081_806_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_884_ = 0;
return v___x_884_;
}
}
case 5:
{
if (lean_obj_tag(v_code_u2082_807_) == 5)
{
lean_object* v_fvarId_885_; lean_object* v_fvarId_886_; uint8_t v___x_887_; 
v_fvarId_885_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc(v_fvarId_885_);
lean_dec_ref_known(v_code_u2081_806_, 1);
v_fvarId_886_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc(v_fvarId_886_);
lean_dec_ref_known(v_code_u2082_807_, 1);
v___x_887_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_885_, v_fvarId_886_, v_a_808_);
lean_dec(v_a_808_);
lean_dec(v_fvarId_886_);
lean_dec(v_fvarId_885_);
return v___x_887_;
}
else
{
uint8_t v___x_888_; 
lean_dec_ref_known(v_code_u2081_806_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_888_ = 0;
return v___x_888_;
}
}
case 6:
{
if (lean_obj_tag(v_code_u2082_807_) == 6)
{
lean_object* v_type_889_; lean_object* v_type_890_; uint8_t v___x_891_; 
v_type_889_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc_ref(v_type_889_);
lean_dec_ref_known(v_code_u2081_806_, 1);
v_type_890_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc_ref(v_type_890_);
lean_dec_ref_known(v_code_u2082_807_, 1);
v___x_891_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_889_, v_type_890_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_type_890_);
lean_dec_ref(v_type_889_);
return v___x_891_;
}
else
{
uint8_t v___x_892_; 
lean_dec_ref_known(v_code_u2081_806_, 1);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_892_ = 0;
return v___x_892_;
}
}
case 7:
{
if (lean_obj_tag(v_code_u2082_807_) == 7)
{
lean_object* v_fvarId_893_; lean_object* v_i_894_; lean_object* v_y_895_; lean_object* v_k_896_; lean_object* v_fvarId_897_; lean_object* v_i_898_; lean_object* v_y_899_; lean_object* v_k_900_; uint8_t v___x_901_; 
v_fvarId_893_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc(v_fvarId_893_);
v_i_894_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc(v_i_894_);
v_y_895_ = lean_ctor_get(v_code_u2081_806_, 2);
lean_inc(v_y_895_);
v_k_896_ = lean_ctor_get(v_code_u2081_806_, 3);
lean_inc_ref(v_k_896_);
lean_dec_ref_known(v_code_u2081_806_, 4);
v_fvarId_897_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc(v_fvarId_897_);
v_i_898_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc(v_i_898_);
v_y_899_ = lean_ctor_get(v_code_u2082_807_, 2);
lean_inc(v_y_899_);
v_k_900_ = lean_ctor_get(v_code_u2082_807_, 3);
lean_inc_ref(v_k_900_);
lean_dec_ref_known(v_code_u2082_807_, 4);
v___x_901_ = lean_nat_dec_eq(v_i_894_, v_i_898_);
lean_dec(v_i_898_);
lean_dec(v_i_894_);
if (v___x_901_ == 0)
{
lean_dec_ref(v_k_900_);
lean_dec(v_y_899_);
lean_dec(v_fvarId_897_);
lean_dec_ref(v_k_896_);
lean_dec(v_y_895_);
lean_dec(v_fvarId_893_);
lean_dec(v_a_808_);
return v___x_901_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_893_, v_fvarId_897_, v_a_808_);
lean_dec(v_fvarId_897_);
lean_dec(v_fvarId_893_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_k_900_);
lean_dec(v_y_899_);
lean_dec_ref(v_k_896_);
lean_dec(v_y_895_);
lean_dec(v_a_808_);
return v___x_902_;
}
else
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_y_895_, v_y_899_, v_a_808_);
lean_dec(v_y_899_);
lean_dec(v_y_895_);
if (v___x_903_ == 0)
{
lean_dec_ref(v_k_900_);
lean_dec_ref(v_k_896_);
lean_dec(v_a_808_);
return v___x_903_;
}
else
{
v_code_u2081_806_ = v_k_896_;
v_code_u2082_807_ = v_k_900_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_905_; 
lean_dec_ref_known(v_code_u2081_806_, 4);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_905_ = 0;
return v___x_905_;
}
}
case 8:
{
if (lean_obj_tag(v_code_u2082_807_) == 8)
{
lean_object* v_fvarId_906_; lean_object* v_i_907_; lean_object* v_y_908_; lean_object* v_k_909_; lean_object* v_fvarId_910_; lean_object* v_i_911_; lean_object* v_y_912_; lean_object* v_k_913_; uint8_t v___x_914_; 
v_fvarId_906_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc(v_fvarId_906_);
v_i_907_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc(v_i_907_);
v_y_908_ = lean_ctor_get(v_code_u2081_806_, 2);
lean_inc(v_y_908_);
v_k_909_ = lean_ctor_get(v_code_u2081_806_, 3);
lean_inc_ref(v_k_909_);
lean_dec_ref_known(v_code_u2081_806_, 4);
v_fvarId_910_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc(v_fvarId_910_);
v_i_911_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc(v_i_911_);
v_y_912_ = lean_ctor_get(v_code_u2082_807_, 2);
lean_inc(v_y_912_);
v_k_913_ = lean_ctor_get(v_code_u2082_807_, 3);
lean_inc_ref(v_k_913_);
lean_dec_ref_known(v_code_u2082_807_, 4);
v___x_914_ = lean_nat_dec_eq(v_i_907_, v_i_911_);
lean_dec(v_i_911_);
lean_dec(v_i_907_);
if (v___x_914_ == 0)
{
lean_dec_ref(v_k_913_);
lean_dec(v_y_912_);
lean_dec(v_fvarId_910_);
lean_dec_ref(v_k_909_);
lean_dec(v_y_908_);
lean_dec(v_fvarId_906_);
lean_dec(v_a_808_);
return v___x_914_;
}
else
{
uint8_t v___x_915_; 
v___x_915_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_906_, v_fvarId_910_, v_a_808_);
lean_dec(v_fvarId_910_);
lean_dec(v_fvarId_906_);
if (v___x_915_ == 0)
{
lean_dec_ref(v_k_913_);
lean_dec(v_y_912_);
lean_dec_ref(v_k_909_);
lean_dec(v_y_908_);
lean_dec(v_a_808_);
return v___x_915_;
}
else
{
uint8_t v___x_916_; 
v___x_916_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_908_, v_y_912_, v_a_808_);
lean_dec(v_y_912_);
lean_dec(v_y_908_);
if (v___x_916_ == 0)
{
lean_dec_ref(v_k_913_);
lean_dec_ref(v_k_909_);
lean_dec(v_a_808_);
return v___x_916_;
}
else
{
v_code_u2081_806_ = v_k_909_;
v_code_u2082_807_ = v_k_913_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_918_; 
lean_dec_ref_known(v_code_u2081_806_, 4);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_918_ = 0;
return v___x_918_;
}
}
case 9:
{
if (lean_obj_tag(v_code_u2082_807_) == 9)
{
lean_object* v_fvarId_919_; lean_object* v_i_920_; lean_object* v_offset_921_; lean_object* v_y_922_; lean_object* v_ty_923_; lean_object* v_k_924_; lean_object* v_fvarId_925_; lean_object* v_i_926_; lean_object* v_offset_927_; lean_object* v_y_928_; lean_object* v_ty_929_; lean_object* v_k_930_; uint8_t v___x_931_; 
v_fvarId_919_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc(v_fvarId_919_);
v_i_920_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc(v_i_920_);
v_offset_921_ = lean_ctor_get(v_code_u2081_806_, 2);
lean_inc(v_offset_921_);
v_y_922_ = lean_ctor_get(v_code_u2081_806_, 3);
lean_inc(v_y_922_);
v_ty_923_ = lean_ctor_get(v_code_u2081_806_, 4);
lean_inc_ref(v_ty_923_);
v_k_924_ = lean_ctor_get(v_code_u2081_806_, 5);
lean_inc_ref(v_k_924_);
lean_dec_ref_known(v_code_u2081_806_, 6);
v_fvarId_925_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc(v_fvarId_925_);
v_i_926_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc(v_i_926_);
v_offset_927_ = lean_ctor_get(v_code_u2082_807_, 2);
lean_inc(v_offset_927_);
v_y_928_ = lean_ctor_get(v_code_u2082_807_, 3);
lean_inc(v_y_928_);
v_ty_929_ = lean_ctor_get(v_code_u2082_807_, 4);
lean_inc_ref(v_ty_929_);
v_k_930_ = lean_ctor_get(v_code_u2082_807_, 5);
lean_inc_ref(v_k_930_);
lean_dec_ref_known(v_code_u2082_807_, 6);
v___x_931_ = lean_nat_dec_eq(v_i_920_, v_i_926_);
lean_dec(v_i_926_);
lean_dec(v_i_920_);
if (v___x_931_ == 0)
{
lean_dec_ref(v_k_930_);
lean_dec_ref(v_ty_929_);
lean_dec(v_y_928_);
lean_dec(v_offset_927_);
lean_dec(v_fvarId_925_);
lean_dec_ref(v_k_924_);
lean_dec_ref(v_ty_923_);
lean_dec(v_y_922_);
lean_dec(v_offset_921_);
lean_dec(v_fvarId_919_);
lean_dec(v_a_808_);
return v___x_931_;
}
else
{
uint8_t v___x_932_; 
v___x_932_ = lean_nat_dec_eq(v_offset_921_, v_offset_927_);
lean_dec(v_offset_927_);
lean_dec(v_offset_921_);
if (v___x_932_ == 0)
{
lean_dec_ref(v_k_930_);
lean_dec_ref(v_ty_929_);
lean_dec(v_y_928_);
lean_dec(v_fvarId_925_);
lean_dec_ref(v_k_924_);
lean_dec_ref(v_ty_923_);
lean_dec(v_y_922_);
lean_dec(v_fvarId_919_);
lean_dec(v_a_808_);
return v___x_932_;
}
else
{
uint8_t v___x_933_; 
v___x_933_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_919_, v_fvarId_925_, v_a_808_);
lean_dec(v_fvarId_925_);
lean_dec(v_fvarId_919_);
if (v___x_933_ == 0)
{
lean_dec_ref(v_k_930_);
lean_dec_ref(v_ty_929_);
lean_dec(v_y_928_);
lean_dec_ref(v_k_924_);
lean_dec_ref(v_ty_923_);
lean_dec(v_y_922_);
lean_dec(v_a_808_);
return v___x_933_;
}
else
{
uint8_t v___x_934_; 
v___x_934_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_922_, v_y_928_, v_a_808_);
lean_dec(v_y_928_);
lean_dec(v_y_922_);
if (v___x_934_ == 0)
{
lean_dec_ref(v_k_930_);
lean_dec_ref(v_ty_929_);
lean_dec_ref(v_k_924_);
lean_dec_ref(v_ty_923_);
lean_dec(v_a_808_);
return v___x_934_;
}
else
{
uint8_t v___x_935_; 
v___x_935_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_923_, v_ty_929_, v_a_808_);
lean_dec_ref(v_ty_929_);
lean_dec_ref(v_ty_923_);
if (v___x_935_ == 0)
{
lean_dec_ref(v_k_930_);
lean_dec_ref(v_k_924_);
lean_dec(v_a_808_);
return v___x_935_;
}
else
{
v_code_u2081_806_ = v_k_924_;
v_code_u2082_807_ = v_k_930_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_937_; 
lean_dec_ref_known(v_code_u2081_806_, 6);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_937_ = 0;
return v___x_937_;
}
}
case 10:
{
if (lean_obj_tag(v_code_u2082_807_) == 10)
{
lean_object* v_fvarId_938_; lean_object* v_cidx_939_; lean_object* v_k_940_; lean_object* v_fvarId_941_; lean_object* v_cidx_942_; lean_object* v_k_943_; uint8_t v___x_944_; 
v_fvarId_938_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc(v_fvarId_938_);
v_cidx_939_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc(v_cidx_939_);
v_k_940_ = lean_ctor_get(v_code_u2081_806_, 2);
lean_inc_ref(v_k_940_);
lean_dec_ref_known(v_code_u2081_806_, 3);
v_fvarId_941_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc(v_fvarId_941_);
v_cidx_942_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc(v_cidx_942_);
v_k_943_ = lean_ctor_get(v_code_u2082_807_, 2);
lean_inc_ref(v_k_943_);
lean_dec_ref_known(v_code_u2082_807_, 3);
v___x_944_ = lean_nat_dec_eq(v_cidx_939_, v_cidx_942_);
lean_dec(v_cidx_942_);
lean_dec(v_cidx_939_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_k_943_);
lean_dec(v_fvarId_941_);
lean_dec_ref(v_k_940_);
lean_dec(v_fvarId_938_);
lean_dec(v_a_808_);
return v___x_944_;
}
else
{
uint8_t v___x_945_; 
v___x_945_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_938_, v_fvarId_941_, v_a_808_);
lean_dec(v_fvarId_941_);
lean_dec(v_fvarId_938_);
if (v___x_945_ == 0)
{
lean_dec_ref(v_k_943_);
lean_dec_ref(v_k_940_);
lean_dec(v_a_808_);
return v___x_945_;
}
else
{
v_code_u2081_806_ = v_k_940_;
v_code_u2082_807_ = v_k_943_;
goto _start;
}
}
}
else
{
uint8_t v___x_947_; 
lean_dec_ref_known(v_code_u2081_806_, 3);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_947_ = 0;
return v___x_947_;
}
}
case 11:
{
if (lean_obj_tag(v_code_u2082_807_) == 11)
{
lean_object* v_fvarId_948_; lean_object* v_n_949_; uint8_t v_check_950_; uint8_t v_persistent_951_; lean_object* v_k_952_; lean_object* v_fvarId_953_; lean_object* v_n_954_; uint8_t v_check_955_; uint8_t v_persistent_956_; lean_object* v_k_957_; uint8_t v___y_962_; uint8_t v___x_963_; 
v_fvarId_948_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc(v_fvarId_948_);
v_n_949_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc(v_n_949_);
v_check_950_ = lean_ctor_get_uint8(v_code_u2081_806_, sizeof(void*)*3);
v_persistent_951_ = lean_ctor_get_uint8(v_code_u2081_806_, sizeof(void*)*3 + 1);
v_k_952_ = lean_ctor_get(v_code_u2081_806_, 2);
lean_inc_ref(v_k_952_);
lean_dec_ref_known(v_code_u2081_806_, 3);
v_fvarId_953_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc(v_fvarId_953_);
v_n_954_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc(v_n_954_);
v_check_955_ = lean_ctor_get_uint8(v_code_u2082_807_, sizeof(void*)*3);
v_persistent_956_ = lean_ctor_get_uint8(v_code_u2082_807_, sizeof(void*)*3 + 1);
v_k_957_ = lean_ctor_get(v_code_u2082_807_, 2);
lean_inc_ref(v_k_957_);
lean_dec_ref_known(v_code_u2082_807_, 3);
v___x_963_ = lean_nat_dec_eq(v_n_949_, v_n_954_);
lean_dec(v_n_954_);
lean_dec(v_n_949_);
if (v___x_963_ == 0)
{
lean_dec_ref(v_k_957_);
lean_dec(v_fvarId_953_);
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec(v_a_808_);
return v___x_963_;
}
else
{
if (v_check_955_ == 0)
{
if (v_check_950_ == 0)
{
v___y_962_ = v___x_963_;
goto v___jp_961_;
}
else
{
lean_dec_ref(v_k_957_);
lean_dec(v_fvarId_953_);
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec(v_a_808_);
return v_check_955_;
}
}
else
{
v___y_962_ = v_check_950_;
goto v___jp_961_;
}
}
v___jp_958_:
{
uint8_t v___x_959_; 
v___x_959_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_948_, v_fvarId_953_, v_a_808_);
lean_dec(v_fvarId_953_);
lean_dec(v_fvarId_948_);
if (v___x_959_ == 0)
{
lean_dec_ref(v_k_957_);
lean_dec_ref(v_k_952_);
lean_dec(v_a_808_);
return v___x_959_;
}
else
{
v_code_u2081_806_ = v_k_952_;
v_code_u2082_807_ = v_k_957_;
goto _start;
}
}
v___jp_961_:
{
if (v___y_962_ == 0)
{
lean_dec_ref(v_k_957_);
lean_dec(v_fvarId_953_);
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec(v_a_808_);
return v___y_962_;
}
else
{
if (v_persistent_956_ == 0)
{
if (v_persistent_951_ == 0)
{
goto v___jp_958_;
}
else
{
lean_dec_ref(v_k_957_);
lean_dec(v_fvarId_953_);
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec(v_a_808_);
return v_persistent_956_;
}
}
else
{
if (v_persistent_951_ == 0)
{
lean_dec_ref(v_k_957_);
lean_dec(v_fvarId_953_);
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec(v_a_808_);
return v_persistent_951_;
}
else
{
goto v___jp_958_;
}
}
}
}
}
else
{
uint8_t v___x_964_; 
lean_dec_ref_known(v_code_u2081_806_, 3);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_964_ = 0;
return v___x_964_;
}
}
case 12:
{
if (lean_obj_tag(v_code_u2082_807_) == 12)
{
lean_object* v_fvarId_965_; lean_object* v_n_966_; uint8_t v_check_967_; uint8_t v_persistent_968_; lean_object* v_objs_x3f_969_; lean_object* v_k_970_; lean_object* v_fvarId_971_; lean_object* v_n_972_; uint8_t v_check_973_; uint8_t v_persistent_974_; lean_object* v_objs_x3f_975_; lean_object* v_k_976_; uint8_t v___y_982_; uint8_t v___x_983_; 
v_fvarId_965_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc(v_fvarId_965_);
v_n_966_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc(v_n_966_);
v_check_967_ = lean_ctor_get_uint8(v_code_u2081_806_, sizeof(void*)*4);
v_persistent_968_ = lean_ctor_get_uint8(v_code_u2081_806_, sizeof(void*)*4 + 1);
v_objs_x3f_969_ = lean_ctor_get(v_code_u2081_806_, 2);
lean_inc(v_objs_x3f_969_);
v_k_970_ = lean_ctor_get(v_code_u2081_806_, 3);
lean_inc_ref(v_k_970_);
lean_dec_ref_known(v_code_u2081_806_, 4);
v_fvarId_971_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc(v_fvarId_971_);
v_n_972_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc(v_n_972_);
v_check_973_ = lean_ctor_get_uint8(v_code_u2082_807_, sizeof(void*)*4);
v_persistent_974_ = lean_ctor_get_uint8(v_code_u2082_807_, sizeof(void*)*4 + 1);
v_objs_x3f_975_ = lean_ctor_get(v_code_u2082_807_, 2);
lean_inc(v_objs_x3f_975_);
v_k_976_ = lean_ctor_get(v_code_u2082_807_, 3);
lean_inc_ref(v_k_976_);
lean_dec_ref_known(v_code_u2082_807_, 4);
v___x_983_ = lean_nat_dec_eq(v_n_966_, v_n_972_);
lean_dec(v_n_972_);
lean_dec(v_n_966_);
if (v___x_983_ == 0)
{
lean_dec_ref(v_k_976_);
lean_dec(v_objs_x3f_975_);
lean_dec(v_fvarId_971_);
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec(v_a_808_);
return v___x_983_;
}
else
{
if (v_check_973_ == 0)
{
if (v_check_967_ == 0)
{
v___y_982_ = v___x_983_;
goto v___jp_981_;
}
else
{
lean_dec_ref(v_k_976_);
lean_dec(v_objs_x3f_975_);
lean_dec(v_fvarId_971_);
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec(v_a_808_);
return v_check_973_;
}
}
else
{
v___y_982_ = v_check_967_;
goto v___jp_981_;
}
}
v___jp_977_:
{
uint8_t v___x_978_; 
v___x_978_ = l_Option_instBEq_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(v_objs_x3f_969_, v_objs_x3f_975_);
lean_dec(v_objs_x3f_975_);
lean_dec(v_objs_x3f_969_);
if (v___x_978_ == 0)
{
lean_dec_ref(v_k_976_);
lean_dec(v_fvarId_971_);
lean_dec_ref(v_k_970_);
lean_dec(v_fvarId_965_);
lean_dec(v_a_808_);
return v___x_978_;
}
else
{
uint8_t v___x_979_; 
v___x_979_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_965_, v_fvarId_971_, v_a_808_);
lean_dec(v_fvarId_971_);
lean_dec(v_fvarId_965_);
if (v___x_979_ == 0)
{
lean_dec_ref(v_k_976_);
lean_dec_ref(v_k_970_);
lean_dec(v_a_808_);
return v___x_979_;
}
else
{
v_code_u2081_806_ = v_k_970_;
v_code_u2082_807_ = v_k_976_;
goto _start;
}
}
}
v___jp_981_:
{
if (v___y_982_ == 0)
{
lean_dec_ref(v_k_976_);
lean_dec(v_objs_x3f_975_);
lean_dec(v_fvarId_971_);
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec(v_a_808_);
return v___y_982_;
}
else
{
if (v_persistent_974_ == 0)
{
if (v_persistent_968_ == 0)
{
goto v___jp_977_;
}
else
{
lean_dec_ref(v_k_976_);
lean_dec(v_objs_x3f_975_);
lean_dec(v_fvarId_971_);
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec(v_a_808_);
return v_persistent_974_;
}
}
else
{
if (v_persistent_968_ == 0)
{
lean_dec_ref(v_k_976_);
lean_dec(v_objs_x3f_975_);
lean_dec(v_fvarId_971_);
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec(v_a_808_);
return v_persistent_968_;
}
else
{
goto v___jp_977_;
}
}
}
}
}
else
{
uint8_t v___x_984_; 
lean_dec_ref_known(v_code_u2081_806_, 4);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_984_ = 0;
return v___x_984_;
}
}
default: 
{
if (lean_obj_tag(v_code_u2082_807_) == 13)
{
lean_object* v_fvarId_985_; lean_object* v_k_986_; lean_object* v_fvarId_987_; lean_object* v_k_988_; uint8_t v___x_989_; 
v_fvarId_985_ = lean_ctor_get(v_code_u2081_806_, 0);
lean_inc(v_fvarId_985_);
v_k_986_ = lean_ctor_get(v_code_u2081_806_, 1);
lean_inc_ref(v_k_986_);
lean_dec_ref_known(v_code_u2081_806_, 2);
v_fvarId_987_ = lean_ctor_get(v_code_u2082_807_, 0);
lean_inc(v_fvarId_987_);
v_k_988_ = lean_ctor_get(v_code_u2082_807_, 1);
lean_inc_ref(v_k_988_);
lean_dec_ref_known(v_code_u2082_807_, 2);
v___x_989_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_985_, v_fvarId_987_, v_a_808_);
lean_dec(v_fvarId_987_);
lean_dec(v_fvarId_985_);
if (v___x_989_ == 0)
{
lean_dec_ref(v_k_988_);
lean_dec_ref(v_k_986_);
lean_dec(v_a_808_);
return v___x_989_;
}
else
{
v_code_u2081_806_ = v_k_986_;
v_code_u2082_807_ = v_k_988_;
goto _start;
}
}
else
{
uint8_t v___x_991_; 
lean_dec_ref_known(v_code_u2081_806_, 2);
lean_dec(v_a_808_);
lean_dec_ref(v_code_u2082_807_);
v___x_991_ = 0;
return v___x_991_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(uint8_t v_pu_992_, lean_object* v_code_993_, lean_object* v_code_994_, lean_object* v_params_u2081_995_, lean_object* v_params_u2082_996_, lean_object* v_i_997_, lean_object* v_a_998_){
_start:
{
lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_999_ = lean_array_get_size(v_params_u2081_995_);
v___x_1000_ = lean_nat_dec_lt(v_i_997_, v___x_999_);
if (v___x_1000_ == 0)
{
uint8_t v___x_1001_; 
lean_dec(v_i_997_);
v___x_1001_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_992_, v_code_993_, v_code_994_, v_a_998_);
return v___x_1001_;
}
else
{
lean_object* v_p_u2081_1002_; lean_object* v_fvarId_1003_; lean_object* v_type_1004_; lean_object* v_p_u2082_1005_; lean_object* v_fvarId_1006_; lean_object* v_type_1007_; uint8_t v___x_1008_; 
v_p_u2081_1002_ = lean_array_fget_borrowed(v_params_u2081_995_, v_i_997_);
v_fvarId_1003_ = lean_ctor_get(v_p_u2081_1002_, 0);
v_type_1004_ = lean_ctor_get(v_p_u2081_1002_, 2);
v_p_u2082_1005_ = lean_array_fget_borrowed(v_params_u2082_996_, v_i_997_);
v_fvarId_1006_ = lean_ctor_get(v_p_u2082_1005_, 0);
v_type_1007_ = lean_ctor_get(v_p_u2082_1005_, 2);
v___x_1008_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_1004_, v_type_1007_, v_a_998_);
if (v___x_1008_ == 0)
{
lean_dec(v_a_998_);
lean_dec(v_i_997_);
lean_dec_ref(v_code_994_);
lean_dec_ref(v_code_993_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_add(v_i_997_, v___x_1009_);
lean_dec(v_i_997_);
lean_inc(v_fvarId_1003_);
lean_inc(v_fvarId_1006_);
v___x_1011_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1006_, v_fvarId_1003_, v_a_998_);
v_i_997_ = v___x_1010_;
v_a_998_ = v___x_1011_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg___boxed(lean_object* v_pu_1013_, lean_object* v_code_1014_, lean_object* v_code_1015_, lean_object* v_params_u2081_1016_, lean_object* v_params_u2082_1017_, lean_object* v_i_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_pu_boxed_1020_; uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_pu_boxed_1020_ = lean_unbox(v_pu_1013_);
v_res_1021_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_boxed_1020_, v_code_1014_, v_code_1015_, v_params_u2081_1016_, v_params_u2082_1017_, v_i_1018_, v_a_1019_);
lean_dec_ref(v_params_u2082_1017_);
lean_dec_ref(v_params_u2081_1016_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts___boxed(lean_object* v_pu_1023_, lean_object* v_alts_u2081_1024_, lean_object* v_alts_u2082_1025_, lean_object* v_a_1026_){
_start:
{
uint8_t v_pu_boxed_1027_; uint8_t v_res_1028_; lean_object* v_r_1029_; 
v_pu_boxed_1027_ = lean_unbox(v_pu_1023_);
v_res_1028_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_boxed_1027_, v_alts_u2081_1024_, v_alts_u2082_1025_, v_a_1026_);
lean_dec(v_a_1026_);
v_r_1029_ = lean_box(v_res_1028_);
return v_r_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___boxed(lean_object* v_pu_1030_, lean_object* v_as_1031_, lean_object* v_sz_1032_, lean_object* v_i_1033_, lean_object* v_b_1034_, lean_object* v___y_1035_){
_start:
{
uint8_t v_pu_boxed_1036_; size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_pu_boxed_1036_ = lean_unbox(v_pu_1030_);
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1032_);
lean_dec(v_sz_1032_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1033_);
lean_dec(v_i_1033_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_boxed_1036_, v_as_1031_, v_sz_boxed_1037_, v_i_boxed_1038_, v_b_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v_as_1031_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqv___boxed(lean_object* v_pu_1040_, lean_object* v_code_u2081_1041_, lean_object* v_code_u2082_1042_, lean_object* v_a_1043_){
_start:
{
uint8_t v_pu_boxed_1044_; uint8_t v_res_1045_; lean_object* v_r_1046_; 
v_pu_boxed_1044_ = lean_unbox(v_pu_1040_);
v_res_1045_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_boxed_1044_, v_code_u2081_1041_, v_code_u2082_1042_, v_a_1043_);
v_r_1046_ = lean_box(v_res_1045_);
return v_r_1046_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(uint8_t v_pu_1047_, lean_object* v_code_1048_, lean_object* v_code_1049_, uint8_t v_pu_1050_, lean_object* v_params_u2081_1051_, lean_object* v_params_u2082_1052_, lean_object* v_h_1053_, lean_object* v_i_1054_, lean_object* v_a_1055_){
_start:
{
uint8_t v___x_1056_; 
lean_inc(v_a_1055_);
v___x_1056_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_1047_, v_code_1048_, v_code_1049_, v_params_u2081_1051_, v_params_u2082_1052_, v_i_1054_, v_a_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___boxed(lean_object* v_pu_1057_, lean_object* v_code_1058_, lean_object* v_code_1059_, lean_object* v_pu_1060_, lean_object* v_params_u2081_1061_, lean_object* v_params_u2082_1062_, lean_object* v_h_1063_, lean_object* v_i_1064_, lean_object* v_a_1065_){
_start:
{
uint8_t v_pu_boxed_1066_; uint8_t v_pu_boxed_1067_; uint8_t v_res_1068_; lean_object* v_r_1069_; 
v_pu_boxed_1066_ = lean_unbox(v_pu_1057_);
v_pu_boxed_1067_ = lean_unbox(v_pu_1060_);
v_res_1068_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(v_pu_boxed_1066_, v_code_1058_, v_code_1059_, v_pu_boxed_1067_, v_params_u2081_1061_, v_params_u2082_1062_, v_h_1063_, v_i_1064_, v_a_1065_);
lean_dec(v_a_1065_);
lean_dec_ref(v_params_u2082_1062_);
lean_dec_ref(v_params_u2081_1061_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t v_pu_1070_, lean_object* v_c_u2081_1071_, lean_object* v_c_u2082_1072_){
_start:
{
lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1073_ = lean_box(1);
v___x_1074_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_1070_, v_c_u2081_1071_, v_c_u2082_1072_, v___x_1073_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_alphaEqv___boxed(lean_object* v_pu_1075_, lean_object* v_c_u2081_1076_, lean_object* v_c_u2082_1077_){
_start:
{
uint8_t v_pu_boxed_1078_; uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_pu_boxed_1078_ = lean_unbox(v_pu_1075_);
v_res_1079_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v_pu_boxed_1078_, v_c_u2081_1076_, v_c_u2082_1077_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
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
