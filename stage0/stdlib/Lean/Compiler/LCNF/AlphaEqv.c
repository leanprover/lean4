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
lean_object* v_typeName_303_; lean_object* v_idx_304_; lean_object* v_struct_305_; lean_object* v_typeName_306_; lean_object* v_idx_307_; lean_object* v_struct_308_; uint8_t v___x_309_; 
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
v___x_309_ = lean_name_eq(v_typeName_303_, v_typeName_306_);
lean_dec(v_typeName_306_);
if (v___x_309_ == 0)
{
lean_dec(v_struct_308_);
lean_dec(v_idx_307_);
return v___x_309_;
}
else
{
uint8_t v___x_310_; 
v___x_310_ = lean_nat_dec_eq(v_idx_304_, v_idx_307_);
lean_dec(v_idx_307_);
if (v___x_310_ == 0)
{
lean_dec(v_struct_308_);
return v___x_310_;
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
uint8_t v___x_312_; 
lean_dec(v_e_u2082_279_);
v___x_312_ = 0;
return v___x_312_;
}
}
case 3:
{
if (lean_obj_tag(v_e_u2082_279_) == 3)
{
lean_object* v_declName_313_; lean_object* v_us_314_; lean_object* v_args_315_; lean_object* v_declName_316_; lean_object* v_us_317_; lean_object* v_args_318_; uint8_t v___x_319_; 
v_declName_313_ = lean_ctor_get(v_e_u2081_278_, 0);
v_us_314_ = lean_ctor_get(v_e_u2081_278_, 1);
v_args_315_ = lean_ctor_get(v_e_u2081_278_, 2);
v_declName_316_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_declName_316_);
v_us_317_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_us_317_);
v_args_318_ = lean_ctor_get(v_e_u2082_279_, 2);
lean_inc_ref(v_args_318_);
lean_dec_ref_known(v_e_u2082_279_, 3);
v___x_319_ = lean_name_eq(v_declName_313_, v_declName_316_);
lean_dec(v_declName_316_);
if (v___x_319_ == 0)
{
lean_dec_ref(v_args_318_);
lean_dec(v_us_317_);
return v___x_319_;
}
else
{
uint8_t v___x_320_; 
v___x_320_ = l_List_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqvLetValue_spec__0(v_us_314_, v_us_317_);
lean_dec(v_us_317_);
if (v___x_320_ == 0)
{
lean_dec_ref(v_args_318_);
return v___x_320_;
}
else
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_args_315_, v_args_318_, v_a_280_);
return v___x_321_;
}
}
}
else
{
uint8_t v___x_322_; 
lean_dec(v_e_u2082_279_);
v___x_322_ = 0;
return v___x_322_;
}
}
case 4:
{
if (lean_obj_tag(v_e_u2082_279_) == 4)
{
lean_object* v_fvarId_323_; lean_object* v_args_324_; lean_object* v_fvarId_325_; lean_object* v_args_326_; uint8_t v___x_327_; 
v_fvarId_323_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_324_ = lean_ctor_get(v_e_u2081_278_, 1);
v_fvarId_325_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fvarId_325_);
v_args_326_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_326_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v___x_327_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_323_, v_fvarId_325_, v_a_280_);
lean_dec(v_fvarId_325_);
if (v___x_327_ == 0)
{
lean_dec_ref(v_args_326_);
return v___x_327_;
}
else
{
uint8_t v___x_328_; 
v___x_328_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_args_324_, v_args_326_, v_a_280_);
return v___x_328_;
}
}
else
{
uint8_t v___x_329_; 
lean_dec(v_e_u2082_279_);
v___x_329_ = 0;
return v___x_329_;
}
}
case 5:
{
if (lean_obj_tag(v_e_u2082_279_) == 5)
{
lean_object* v_i_330_; lean_object* v_args_331_; lean_object* v_i_332_; lean_object* v_args_333_; uint8_t v___x_334_; 
v_i_330_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_331_ = lean_ctor_get(v_e_u2081_278_, 1);
v_i_332_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc_ref(v_i_332_);
v_args_333_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_333_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v___x_334_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_i_330_, v_i_332_);
lean_dec_ref(v_i_332_);
if (v___x_334_ == 0)
{
lean_dec_ref(v_args_333_);
return v___x_334_;
}
else
{
uint8_t v___x_335_; 
v___x_335_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_args_331_, v_args_333_, v_a_280_);
return v___x_335_;
}
}
else
{
uint8_t v___x_336_; 
lean_dec(v_e_u2082_279_);
v___x_336_ = 0;
return v___x_336_;
}
}
case 6:
{
if (lean_obj_tag(v_e_u2082_279_) == 6)
{
lean_object* v_i_337_; lean_object* v_var_338_; lean_object* v_i_339_; lean_object* v_var_340_; 
v_i_337_ = lean_ctor_get(v_e_u2081_278_, 0);
v_var_338_ = lean_ctor_get(v_e_u2081_278_, 1);
v_i_339_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_i_339_);
v_var_340_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_var_340_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_i_u2081_290_ = v_i_337_;
v_v_u2081_291_ = v_var_338_;
v_i_u2082_292_ = v_i_339_;
v_v_u2082_293_ = v_var_340_;
v___y_294_ = v_a_280_;
goto v___jp_289_;
}
else
{
uint8_t v___x_341_; 
lean_dec(v_e_u2082_279_);
v___x_341_ = 0;
return v___x_341_;
}
}
case 7:
{
if (lean_obj_tag(v_e_u2082_279_) == 7)
{
lean_object* v_i_342_; lean_object* v_var_343_; lean_object* v_i_344_; lean_object* v_var_345_; 
v_i_342_ = lean_ctor_get(v_e_u2081_278_, 0);
v_var_343_ = lean_ctor_get(v_e_u2081_278_, 1);
v_i_344_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_i_344_);
v_var_345_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_var_345_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_i_u2081_290_ = v_i_342_;
v_v_u2081_291_ = v_var_343_;
v_i_u2082_292_ = v_i_344_;
v_v_u2082_293_ = v_var_345_;
v___y_294_ = v_a_280_;
goto v___jp_289_;
}
else
{
uint8_t v___x_346_; 
lean_dec(v_e_u2082_279_);
v___x_346_ = 0;
return v___x_346_;
}
}
case 8:
{
if (lean_obj_tag(v_e_u2082_279_) == 8)
{
lean_object* v_n_347_; lean_object* v_offset_348_; lean_object* v_var_349_; lean_object* v_n_350_; lean_object* v_offset_351_; lean_object* v_var_352_; uint8_t v___x_353_; 
v_n_347_ = lean_ctor_get(v_e_u2081_278_, 0);
v_offset_348_ = lean_ctor_get(v_e_u2081_278_, 1);
v_var_349_ = lean_ctor_get(v_e_u2081_278_, 2);
v_n_350_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_n_350_);
v_offset_351_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_offset_351_);
v_var_352_ = lean_ctor_get(v_e_u2082_279_, 2);
lean_inc(v_var_352_);
lean_dec_ref_known(v_e_u2082_279_, 3);
v___x_353_ = lean_nat_dec_eq(v_n_347_, v_n_350_);
lean_dec(v_n_350_);
if (v___x_353_ == 0)
{
lean_dec(v_var_352_);
lean_dec(v_offset_351_);
return v___x_353_;
}
else
{
uint8_t v___x_354_; 
v___x_354_ = lean_nat_dec_eq(v_offset_348_, v_offset_351_);
lean_dec(v_offset_351_);
if (v___x_354_ == 0)
{
lean_dec(v_var_352_);
return v___x_354_;
}
else
{
uint8_t v___x_355_; 
v___x_355_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_var_349_, v_var_352_, v_a_280_);
lean_dec(v_var_352_);
return v___x_355_;
}
}
}
else
{
uint8_t v___x_356_; 
lean_dec(v_e_u2082_279_);
v___x_356_ = 0;
return v___x_356_;
}
}
case 9:
{
if (lean_obj_tag(v_e_u2082_279_) == 9)
{
lean_object* v_fn_357_; lean_object* v_args_358_; lean_object* v_fn_359_; lean_object* v_args_360_; 
v_fn_357_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_358_ = lean_ctor_get(v_e_u2081_278_, 1);
v_fn_359_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fn_359_);
v_args_360_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_360_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_f_u2081_282_ = v_fn_357_;
v_as_u2081_283_ = v_args_358_;
v_f_u2082_284_ = v_fn_359_;
v_as_u2082_285_ = v_args_360_;
v___y_286_ = v_a_280_;
goto v___jp_281_;
}
else
{
uint8_t v___x_361_; 
lean_dec(v_e_u2082_279_);
v___x_361_ = 0;
return v___x_361_;
}
}
case 10:
{
if (lean_obj_tag(v_e_u2082_279_) == 10)
{
lean_object* v_fn_362_; lean_object* v_args_363_; lean_object* v_fn_364_; lean_object* v_args_365_; 
v_fn_362_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_363_ = lean_ctor_get(v_e_u2081_278_, 1);
v_fn_364_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fn_364_);
v_args_365_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_365_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_f_u2081_282_ = v_fn_362_;
v_as_u2081_283_ = v_args_363_;
v_f_u2082_284_ = v_fn_364_;
v_as_u2082_285_ = v_args_365_;
v___y_286_ = v_a_280_;
goto v___jp_281_;
}
else
{
uint8_t v___x_366_; 
lean_dec(v_e_u2082_279_);
v___x_366_ = 0;
return v___x_366_;
}
}
case 11:
{
if (lean_obj_tag(v_e_u2082_279_) == 11)
{
lean_object* v_n_367_; lean_object* v_var_368_; lean_object* v_n_369_; lean_object* v_var_370_; 
v_n_367_ = lean_ctor_get(v_e_u2081_278_, 0);
v_var_368_ = lean_ctor_get(v_e_u2081_278_, 1);
v_n_369_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_n_369_);
v_var_370_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_var_370_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v_i_u2081_290_ = v_n_367_;
v_v_u2081_291_ = v_var_368_;
v_i_u2082_292_ = v_n_369_;
v_v_u2082_293_ = v_var_370_;
v___y_294_ = v_a_280_;
goto v___jp_289_;
}
else
{
uint8_t v___x_371_; 
lean_dec(v_e_u2082_279_);
v___x_371_ = 0;
return v___x_371_;
}
}
case 12:
{
if (lean_obj_tag(v_e_u2082_279_) == 12)
{
lean_object* v_var_372_; lean_object* v_i_373_; uint8_t v_updateHeader_374_; lean_object* v_args_375_; lean_object* v_var_376_; lean_object* v_i_377_; uint8_t v_updateHeader_378_; lean_object* v_args_379_; uint8_t v___x_383_; 
v_var_372_ = lean_ctor_get(v_e_u2081_278_, 0);
v_i_373_ = lean_ctor_get(v_e_u2081_278_, 1);
v_updateHeader_374_ = lean_ctor_get_uint8(v_e_u2081_278_, sizeof(void*)*3);
v_args_375_ = lean_ctor_get(v_e_u2081_278_, 2);
v_var_376_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_var_376_);
v_i_377_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_i_377_);
v_updateHeader_378_ = lean_ctor_get_uint8(v_e_u2082_279_, sizeof(void*)*3);
v_args_379_ = lean_ctor_get(v_e_u2082_279_, 2);
lean_inc_ref(v_args_379_);
lean_dec_ref_known(v_e_u2082_279_, 3);
v___x_383_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_i_373_, v_i_377_);
lean_dec_ref(v_i_377_);
if (v___x_383_ == 0)
{
lean_dec_ref(v_args_379_);
lean_dec(v_var_376_);
return v___x_383_;
}
else
{
if (v_updateHeader_378_ == 0)
{
if (v_updateHeader_374_ == 0)
{
goto v___jp_380_;
}
else
{
lean_dec_ref(v_args_379_);
lean_dec(v_var_376_);
return v_updateHeader_378_;
}
}
else
{
if (v_updateHeader_374_ == 0)
{
lean_dec_ref(v_args_379_);
lean_dec(v_var_376_);
return v_updateHeader_374_;
}
else
{
goto v___jp_380_;
}
}
}
v___jp_380_:
{
uint8_t v___x_381_; 
v___x_381_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_var_372_, v_var_376_, v_a_280_);
lean_dec(v_var_376_);
if (v___x_381_ == 0)
{
lean_dec_ref(v_args_379_);
return v___x_381_;
}
else
{
uint8_t v___x_382_; 
v___x_382_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_args_375_, v_args_379_, v_a_280_);
return v___x_382_;
}
}
}
else
{
uint8_t v___x_384_; 
lean_dec(v_e_u2082_279_);
v___x_384_ = 0;
return v___x_384_;
}
}
case 13:
{
if (lean_obj_tag(v_e_u2082_279_) == 13)
{
lean_object* v_ty_385_; lean_object* v_fvarId_386_; lean_object* v_ty_387_; lean_object* v_fvarId_388_; uint8_t v___x_389_; 
v_ty_385_ = lean_ctor_get(v_e_u2081_278_, 0);
v_fvarId_386_ = lean_ctor_get(v_e_u2081_278_, 1);
v_ty_387_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc_ref(v_ty_387_);
v_fvarId_388_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_fvarId_388_);
lean_dec_ref_known(v_e_u2082_279_, 2);
v___x_389_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_385_, v_ty_387_, v_a_280_);
lean_dec_ref(v_ty_387_);
if (v___x_389_ == 0)
{
lean_dec(v_fvarId_388_);
return v___x_389_;
}
else
{
uint8_t v___x_390_; 
v___x_390_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_386_, v_fvarId_388_, v_a_280_);
lean_dec(v_fvarId_388_);
return v___x_390_;
}
}
else
{
uint8_t v___x_391_; 
lean_dec(v_e_u2082_279_);
v___x_391_ = 0;
return v___x_391_;
}
}
case 14:
{
if (lean_obj_tag(v_e_u2082_279_) == 14)
{
lean_object* v_fvarId_392_; lean_object* v_fvarId_393_; uint8_t v___x_394_; 
v_fvarId_392_ = lean_ctor_get(v_e_u2081_278_, 0);
v_fvarId_393_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fvarId_393_);
lean_dec_ref_known(v_e_u2082_279_, 1);
v___x_394_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_392_, v_fvarId_393_, v_a_280_);
lean_dec(v_fvarId_393_);
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
lean_dec(v_e_u2082_279_);
v___x_395_ = 0;
return v___x_395_;
}
}
default: 
{
if (lean_obj_tag(v_e_u2082_279_) == 15)
{
lean_object* v_fvarId_396_; lean_object* v_fvarId_397_; uint8_t v___x_398_; 
v_fvarId_396_ = lean_ctor_get(v_e_u2081_278_, 0);
v_fvarId_397_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fvarId_397_);
lean_dec_ref_known(v_e_u2082_279_, 1);
v___x_398_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_396_, v_fvarId_397_, v_a_280_);
lean_dec(v_fvarId_397_);
return v___x_398_;
}
else
{
uint8_t v___x_399_; 
lean_dec(v_e_u2082_279_);
v___x_399_ = 0;
return v___x_399_;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue___boxed(lean_object* v_pu_400_, lean_object* v_e_u2081_401_, lean_object* v_e_u2082_402_, lean_object* v_a_403_){
_start:
{
uint8_t v_pu_boxed_404_; uint8_t v_res_405_; lean_object* v_r_406_; 
v_pu_boxed_404_ = lean_unbox(v_pu_400_);
v_res_405_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_boxed_404_, v_e_u2081_401_, v_e_u2082_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec(v_e_u2081_401_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(lean_object* v_fvarId_u2081_407_, lean_object* v_fvarId_u2082_408_, lean_object* v_x_409_, lean_object* v_a_410_){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_inc(v_a_410_);
v___x_411_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_408_, v_fvarId_u2081_407_, v_a_410_);
v___x_412_ = lean_apply_1(v_x_409_, v___x_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg___boxed(lean_object* v_fvarId_u2081_413_, lean_object* v_fvarId_u2082_414_, lean_object* v_x_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(v_fvarId_u2081_413_, v_fvarId_u2082_414_, v_x_415_, v_a_416_);
lean_dec(v_a_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar(lean_object* v_00_u03b1_418_, lean_object* v_fvarId_u2081_419_, lean_object* v_fvarId_u2082_420_, lean_object* v_x_421_, lean_object* v_a_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_inc(v_a_422_);
v___x_423_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_420_, v_fvarId_u2081_419_, v_a_422_);
v___x_424_ = lean_apply_1(v_x_421_, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___boxed(lean_object* v_00_u03b1_425_, lean_object* v_fvarId_u2081_426_, lean_object* v_fvarId_u2082_427_, lean_object* v_x_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar(v_00_u03b1_425_, v_fvarId_u2081_426_, v_fvarId_u2082_427_, v_x_428_, v_a_429_);
lean_dec(v_a_429_);
return v_res_430_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(lean_object* v_params_u2081_431_, lean_object* v_params_u2082_432_, lean_object* v_x_433_, lean_object* v_i_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_436_ = lean_array_get_size(v_params_u2081_431_);
v___x_437_ = lean_nat_dec_lt(v_i_434_, v___x_436_);
if (v___x_437_ == 0)
{
lean_object* v___x_438_; uint8_t v___x_439_; 
lean_dec(v_i_434_);
v___x_438_ = lean_apply_1(v_x_433_, v_a_435_);
v___x_439_ = lean_unbox(v___x_438_);
return v___x_439_;
}
else
{
lean_object* v_p_u2081_440_; lean_object* v_fvarId_441_; lean_object* v_type_442_; lean_object* v_p_u2082_443_; lean_object* v_fvarId_444_; lean_object* v_type_445_; uint8_t v___x_446_; 
v_p_u2081_440_ = lean_array_fget_borrowed(v_params_u2081_431_, v_i_434_);
v_fvarId_441_ = lean_ctor_get(v_p_u2081_440_, 0);
v_type_442_ = lean_ctor_get(v_p_u2081_440_, 2);
v_p_u2082_443_ = lean_array_fget_borrowed(v_params_u2082_432_, v_i_434_);
v_fvarId_444_ = lean_ctor_get(v_p_u2082_443_, 0);
v_type_445_ = lean_ctor_get(v_p_u2082_443_, 2);
v___x_446_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_442_, v_type_445_, v_a_435_);
if (v___x_446_ == 0)
{
lean_dec(v_a_435_);
lean_dec(v_i_434_);
lean_dec_ref(v_x_433_);
return v___x_446_;
}
else
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v_i_434_, v___x_447_);
lean_dec(v_i_434_);
lean_inc(v_fvarId_441_);
lean_inc(v_fvarId_444_);
v___x_449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_444_, v_fvarId_441_, v_a_435_);
v_i_434_ = v___x_448_;
v_a_435_ = v___x_449_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg___boxed(lean_object* v_params_u2081_451_, lean_object* v_params_u2082_452_, lean_object* v_x_453_, lean_object* v_i_454_, lean_object* v_a_455_){
_start:
{
uint8_t v_res_456_; lean_object* v_r_457_; 
v_res_456_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_451_, v_params_u2082_452_, v_x_453_, v_i_454_, v_a_455_);
lean_dec_ref(v_params_u2082_452_);
lean_dec_ref(v_params_u2081_451_);
v_r_457_ = lean_box(v_res_456_);
return v_r_457_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(uint8_t v_pu_458_, lean_object* v_params_u2081_459_, lean_object* v_params_u2082_460_, lean_object* v_x_461_, lean_object* v_h_462_, lean_object* v_i_463_, lean_object* v_a_464_){
_start:
{
uint8_t v___x_465_; 
lean_inc(v_a_464_);
v___x_465_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_459_, v_params_u2082_460_, v_x_461_, v_i_463_, v_a_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___boxed(lean_object* v_pu_466_, lean_object* v_params_u2081_467_, lean_object* v_params_u2082_468_, lean_object* v_x_469_, lean_object* v_h_470_, lean_object* v_i_471_, lean_object* v_a_472_){
_start:
{
uint8_t v_pu_boxed_473_; uint8_t v_res_474_; lean_object* v_r_475_; 
v_pu_boxed_473_ = lean_unbox(v_pu_466_);
v_res_474_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(v_pu_boxed_473_, v_params_u2081_467_, v_params_u2082_468_, v_x_469_, v_h_470_, v_i_471_, v_a_472_);
lean_dec(v_a_472_);
lean_dec_ref(v_params_u2082_468_);
lean_dec_ref(v_params_u2081_467_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(lean_object* v_params_u2081_476_, lean_object* v_params_u2082_477_, lean_object* v_x_478_, lean_object* v_a_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; uint8_t v___x_482_; 
v___x_480_ = lean_array_get_size(v_params_u2082_477_);
v___x_481_ = lean_array_get_size(v_params_u2081_476_);
v___x_482_ = lean_nat_dec_eq(v___x_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_dec_ref(v_x_478_);
return v___x_482_;
}
else
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_479_);
v___x_484_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_476_, v_params_u2082_477_, v_x_478_, v___x_483_, v_a_479_);
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg___boxed(lean_object* v_params_u2081_485_, lean_object* v_params_u2082_486_, lean_object* v_x_487_, lean_object* v_a_488_){
_start:
{
uint8_t v_res_489_; lean_object* v_r_490_; 
v_res_489_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(v_params_u2081_485_, v_params_u2082_486_, v_x_487_, v_a_488_);
lean_dec(v_a_488_);
lean_dec_ref(v_params_u2082_486_);
lean_dec_ref(v_params_u2081_485_);
v_r_490_ = lean_box(v_res_489_);
return v_r_490_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams(uint8_t v_pu_491_, lean_object* v_params_u2081_492_, lean_object* v_params_u2082_493_, lean_object* v_x_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_496_ = lean_array_get_size(v_params_u2082_493_);
v___x_497_ = lean_array_get_size(v_params_u2081_492_);
v___x_498_ = lean_nat_dec_eq(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_dec_ref(v_x_494_);
return v___x_498_;
}
else
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_495_);
v___x_500_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_492_, v_params_u2082_493_, v_x_494_, v___x_499_, v_a_495_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___boxed(lean_object* v_pu_501_, lean_object* v_params_u2081_502_, lean_object* v_params_u2082_503_, lean_object* v_x_504_, lean_object* v_a_505_){
_start:
{
uint8_t v_pu_boxed_506_; uint8_t v_res_507_; lean_object* v_r_508_; 
v_pu_boxed_506_ = lean_unbox(v_pu_501_);
v_res_507_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams(v_pu_boxed_506_, v_params_u2081_502_, v_params_u2082_503_, v_x_504_, v_a_505_);
lean_dec(v_a_505_);
lean_dec_ref(v_params_u2082_503_);
lean_dec_ref(v_params_u2081_502_);
v_r_508_ = lean_box(v_res_507_);
return v_r_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(lean_object* v_hi_509_, lean_object* v_pivot_510_, lean_object* v_as_511_, lean_object* v_i_512_, lean_object* v_k_513_){
_start:
{
uint8_t v___y_525_; uint8_t v___x_526_; 
v___x_526_ = lean_nat_dec_lt(v_k_513_, v_hi_509_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; lean_object* v___x_528_; 
lean_dec(v_k_513_);
v___x_527_ = lean_array_fswap(v_as_511_, v_i_512_, v_hi_509_);
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v_i_512_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
else
{
lean_object* v___x_529_; 
v___x_529_ = lean_array_fget_borrowed(v_as_511_, v_k_513_);
switch(lean_obj_tag(v___x_529_))
{
case 0:
{
switch(lean_obj_tag(v_pivot_510_))
{
case 2:
{
goto v___jp_518_;
}
case 0:
{
lean_object* v_ctorName_530_; lean_object* v_ctorName_531_; uint8_t v___x_532_; 
v_ctorName_530_ = lean_ctor_get(v___x_529_, 0);
v_ctorName_531_ = lean_ctor_get(v_pivot_510_, 0);
v___x_532_ = l_Lean_Name_lt(v_ctorName_530_, v_ctorName_531_);
v___y_525_ = v___x_532_;
goto v___jp_524_;
}
default: 
{
goto v___jp_514_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_pivot_510_))
{
case 2:
{
goto v___jp_518_;
}
case 1:
{
lean_object* v_info_533_; lean_object* v_info_534_; lean_object* v_name_535_; lean_object* v_name_536_; uint8_t v___x_537_; 
v_info_533_ = lean_ctor_get(v___x_529_, 0);
v_info_534_ = lean_ctor_get(v_pivot_510_, 0);
v_name_535_ = lean_ctor_get(v_info_533_, 0);
v_name_536_ = lean_ctor_get(v_info_534_, 0);
v___x_537_ = l_Lean_Name_lt(v_name_535_, v_name_536_);
v___y_525_ = v___x_537_;
goto v___jp_524_;
}
default: 
{
goto v___jp_514_;
}
}
}
default: 
{
goto v___jp_514_;
}
}
}
v___jp_514_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_k_513_, v___x_515_);
lean_dec(v_k_513_);
v_k_513_ = v___x_516_;
goto _start;
}
v___jp_518_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_519_ = lean_array_fswap(v_as_511_, v_i_512_, v_k_513_);
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_add(v_i_512_, v___x_520_);
lean_dec(v_i_512_);
v___x_522_ = lean_nat_add(v_k_513_, v___x_520_);
lean_dec(v_k_513_);
v_as_511_ = v___x_519_;
v_i_512_ = v___x_521_;
v_k_513_ = v___x_522_;
goto _start;
}
v___jp_524_:
{
if (v___y_525_ == 0)
{
goto v___jp_514_;
}
else
{
goto v___jp_518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg___boxed(lean_object* v_hi_538_, lean_object* v_pivot_539_, lean_object* v_as_540_, lean_object* v_i_541_, lean_object* v_k_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_538_, v_pivot_539_, v_as_540_, v_i_541_, v_k_542_);
lean_dec_ref(v_pivot_539_);
lean_dec(v_hi_538_);
return v_res_543_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(uint8_t v___x_544_, lean_object* v_x_545_, lean_object* v_x_546_){
_start:
{
switch(lean_obj_tag(v_x_545_))
{
case 0:
{
switch(lean_obj_tag(v_x_546_))
{
case 2:
{
return v___x_544_;
}
case 0:
{
lean_object* v_ctorName_547_; lean_object* v_ctorName_548_; uint8_t v___x_549_; 
v_ctorName_547_ = lean_ctor_get(v_x_545_, 0);
v_ctorName_548_ = lean_ctor_get(v_x_546_, 0);
v___x_549_ = l_Lean_Name_lt(v_ctorName_547_, v_ctorName_548_);
return v___x_549_;
}
default: 
{
uint8_t v___x_550_; 
v___x_550_ = 0;
return v___x_550_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_546_))
{
case 2:
{
return v___x_544_;
}
case 1:
{
lean_object* v_info_551_; lean_object* v_info_552_; lean_object* v_name_553_; lean_object* v_name_554_; uint8_t v___x_555_; 
v_info_551_ = lean_ctor_get(v_x_545_, 0);
v_info_552_ = lean_ctor_get(v_x_546_, 0);
v_name_553_ = lean_ctor_get(v_info_551_, 0);
v_name_554_ = lean_ctor_get(v_info_552_, 0);
v___x_555_ = l_Lean_Name_lt(v_name_553_, v_name_554_);
return v___x_555_;
}
default: 
{
uint8_t v___x_556_; 
v___x_556_ = 0;
return v___x_556_;
}
}
}
default: 
{
uint8_t v___x_557_; 
v___x_557_ = 0;
return v___x_557_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed(lean_object* v___x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
uint8_t v___x_426__boxed_561_; uint8_t v_res_562_; lean_object* v_r_563_; 
v___x_426__boxed_561_ = lean_unbox(v___x_558_);
v_res_562_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_426__boxed_561_, v_x_559_, v_x_560_);
lean_dec_ref(v_x_560_);
lean_dec_ref(v_x_559_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(lean_object* v_n_564_, lean_object* v_as_565_, lean_object* v_lo_566_, lean_object* v_hi_567_){
_start:
{
lean_object* v___y_569_; uint8_t v___x_579_; 
v___x_579_ = lean_nat_dec_lt(v_lo_566_, v_hi_567_);
if (v___x_579_ == 0)
{
lean_dec(v_lo_566_);
return v_as_565_;
}
else
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v_mid_582_; lean_object* v___y_584_; lean_object* v___y_590_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v___x_580_ = lean_nat_add(v_lo_566_, v_hi_567_);
v___x_581_ = lean_unsigned_to_nat(1u);
v_mid_582_ = lean_nat_shiftr(v___x_580_, v___x_581_);
lean_dec(v___x_580_);
v___x_595_ = lean_array_fget_borrowed(v_as_565_, v_mid_582_);
v___x_596_ = lean_array_fget_borrowed(v_as_565_, v_lo_566_);
v___x_597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_579_, v___x_595_, v___x_596_);
if (v___x_597_ == 0)
{
v___y_590_ = v_as_565_;
goto v___jp_589_;
}
else
{
lean_object* v___x_598_; 
v___x_598_ = lean_array_fswap(v_as_565_, v_lo_566_, v_mid_582_);
v___y_590_ = v___x_598_;
goto v___jp_589_;
}
v___jp_583_:
{
lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_585_ = lean_array_fget_borrowed(v___y_584_, v_mid_582_);
v___x_586_ = lean_array_fget_borrowed(v___y_584_, v_hi_567_);
v___x_587_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_579_, v___x_585_, v___x_586_);
if (v___x_587_ == 0)
{
lean_dec(v_mid_582_);
v___y_569_ = v___y_584_;
goto v___jp_568_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = lean_array_fswap(v___y_584_, v_mid_582_, v_hi_567_);
lean_dec(v_mid_582_);
v___y_569_ = v___x_588_;
goto v___jp_568_;
}
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_591_ = lean_array_fget_borrowed(v___y_590_, v_hi_567_);
v___x_592_ = lean_array_fget_borrowed(v___y_590_, v_lo_566_);
v___x_593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_579_, v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
v___y_584_ = v___y_590_;
goto v___jp_583_;
}
else
{
lean_object* v___x_594_; 
v___x_594_ = lean_array_fswap(v___y_590_, v_lo_566_, v_hi_567_);
v___y_584_ = v___x_594_;
goto v___jp_583_;
}
}
}
v___jp_568_:
{
lean_object* v_pivot_570_; lean_object* v___x_571_; lean_object* v_fst_572_; lean_object* v_snd_573_; uint8_t v___x_574_; 
v_pivot_570_ = lean_array_fget(v___y_569_, v_hi_567_);
lean_inc_n(v_lo_566_, 2);
v___x_571_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_567_, v_pivot_570_, v___y_569_, v_lo_566_, v_lo_566_);
lean_dec(v_pivot_570_);
v_fst_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_fst_572_);
v_snd_573_ = lean_ctor_get(v___x_571_, 1);
lean_inc(v_snd_573_);
lean_dec_ref(v___x_571_);
v___x_574_ = lean_nat_dec_le(v_hi_567_, v_fst_572_);
if (v___x_574_ == 0)
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_564_, v_snd_573_, v_lo_566_, v_fst_572_);
v___x_576_ = lean_unsigned_to_nat(1u);
v___x_577_ = lean_nat_add(v_fst_572_, v___x_576_);
lean_dec(v_fst_572_);
v_as_565_ = v___x_575_;
v_lo_566_ = v___x_577_;
goto _start;
}
else
{
lean_dec(v_fst_572_);
lean_dec(v_lo_566_);
return v_snd_573_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___boxed(lean_object* v_n_599_, lean_object* v_as_600_, lean_object* v_lo_601_, lean_object* v_hi_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_599_, v_as_600_, v_lo_601_, v_hi_602_);
lean_dec(v_hi_602_);
lean_dec(v_n_599_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(lean_object* v_alts_604_){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_605_ = lean_array_get_size(v_alts_604_);
v___x_606_ = lean_unsigned_to_nat(0u);
v___x_607_ = lean_nat_dec_eq(v___x_605_, v___x_606_);
if (v___x_607_ == 0)
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___y_611_; uint8_t v___x_615_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_sub(v___x_605_, v___x_608_);
v___x_615_ = lean_nat_dec_le(v___x_606_, v___x_609_);
if (v___x_615_ == 0)
{
lean_inc(v___x_609_);
v___y_611_ = v___x_609_;
goto v___jp_610_;
}
else
{
v___y_611_ = v___x_606_;
goto v___jp_610_;
}
v___jp_610_:
{
uint8_t v___x_612_; 
v___x_612_ = lean_nat_dec_le(v___y_611_, v___x_609_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
lean_dec(v___x_609_);
lean_inc(v___y_611_);
v___x_613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_605_, v_alts_604_, v___y_611_, v___y_611_);
lean_dec(v___y_611_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_605_, v_alts_604_, v___y_611_, v___x_609_);
lean_dec(v___x_609_);
return v___x_614_;
}
}
}
else
{
return v_alts_604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(uint8_t v_pu_616_, lean_object* v_alts_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___boxed(lean_object* v_pu_619_, lean_object* v_alts_620_){
_start:
{
uint8_t v_pu_boxed_621_; lean_object* v_res_622_; 
v_pu_boxed_621_ = lean_unbox(v_pu_619_);
v_res_622_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(v_pu_boxed_621_, v_alts_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(lean_object* v_n_623_, lean_object* v_as_624_, lean_object* v_lo_625_, lean_object* v_hi_626_, lean_object* v_w_627_, lean_object* v_hlo_628_, lean_object* v_hhi_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_623_, v_as_624_, v_lo_625_, v_hi_626_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___boxed(lean_object* v_n_631_, lean_object* v_as_632_, lean_object* v_lo_633_, lean_object* v_hi_634_, lean_object* v_w_635_, lean_object* v_hlo_636_, lean_object* v_hhi_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(v_n_631_, v_as_632_, v_lo_633_, v_hi_634_, v_w_635_, v_hlo_636_, v_hhi_637_);
lean_dec(v_hi_634_);
lean_dec(v_n_631_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(lean_object* v_n_639_, lean_object* v_lo_640_, lean_object* v_hi_641_, lean_object* v_hhi_642_, lean_object* v_pivot_643_, lean_object* v_as_644_, lean_object* v_i_645_, lean_object* v_k_646_, lean_object* v_ilo_647_, lean_object* v_ik_648_, lean_object* v_w_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_641_, v_pivot_643_, v_as_644_, v_i_645_, v_k_646_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___boxed(lean_object* v_n_651_, lean_object* v_lo_652_, lean_object* v_hi_653_, lean_object* v_hhi_654_, lean_object* v_pivot_655_, lean_object* v_as_656_, lean_object* v_i_657_, lean_object* v_k_658_, lean_object* v_ilo_659_, lean_object* v_ik_660_, lean_object* v_w_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(v_n_651_, v_lo_652_, v_hi_653_, v_hhi_654_, v_pivot_655_, v_as_656_, v_i_657_, v_k_658_, v_ilo_659_, v_ik_660_, v_w_661_);
lean_dec_ref(v_pivot_655_);
lean_dec(v_hi_653_);
lean_dec(v_lo_652_);
lean_dec(v_n_651_);
return v_res_662_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
if (lean_obj_tag(v_x_663_) == 0)
{
if (lean_obj_tag(v_x_664_) == 0)
{
uint8_t v___x_665_; 
v___x_665_ = 1;
return v___x_665_;
}
else
{
uint8_t v___x_666_; 
v___x_666_ = 0;
return v___x_666_;
}
}
else
{
if (lean_obj_tag(v_x_664_) == 0)
{
uint8_t v___x_667_; 
v___x_667_ = 0;
return v___x_667_;
}
else
{
lean_object* v_val_668_; lean_object* v_val_669_; uint8_t v___x_670_; 
v_val_668_ = lean_ctor_get(v_x_663_, 0);
v_val_669_ = lean_ctor_get(v_x_664_, 0);
v___x_670_ = lean_nat_dec_eq(v_val_668_, v_val_669_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3___boxed(lean_object* v_x_671_, lean_object* v_x_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(v_x_671_, v_x_672_);
lean_dec(v_x_672_);
lean_dec(v_x_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(uint8_t v_pu_678_, lean_object* v_as_679_, size_t v_sz_680_, size_t v_i_681_, lean_object* v_b_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_a_685_; uint8_t v___x_689_; 
v___x_689_ = lean_usize_dec_lt(v_i_681_, v_sz_680_);
if (v___x_689_ == 0)
{
return v_b_682_;
}
else
{
lean_object* v_snd_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_778_; 
v_snd_690_ = lean_ctor_get(v_b_682_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_b_682_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_b_682_, 0);
lean_dec(v_unused_779_);
v___x_692_ = v_b_682_;
v_isShared_693_ = v_isSharedCheck_778_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_snd_690_);
lean_dec(v_b_682_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_778_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v_array_694_; lean_object* v_start_695_; lean_object* v_stop_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_array_694_ = lean_ctor_get(v_snd_690_, 0);
v_start_695_ = lean_ctor_get(v_snd_690_, 1);
v_stop_696_ = lean_ctor_get(v_snd_690_, 2);
v___x_697_ = lean_box(0);
v___x_698_ = lean_nat_dec_lt(v_start_695_, v_stop_696_);
if (v___x_698_ == 0)
{
lean_object* v___x_700_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_697_);
v___x_700_ = v___x_692_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_snd_690_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
else
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_774_; 
lean_inc(v_stop_696_);
lean_inc(v_start_695_);
lean_inc_ref(v_array_694_);
v_isSharedCheck_774_ = !lean_is_exclusive(v_snd_690_);
if (v_isSharedCheck_774_ == 0)
{
lean_object* v_unused_775_; lean_object* v_unused_776_; lean_object* v_unused_777_; 
v_unused_775_ = lean_ctor_get(v_snd_690_, 2);
lean_dec(v_unused_775_);
v_unused_776_ = lean_ctor_get(v_snd_690_, 1);
lean_dec(v_unused_776_);
v_unused_777_ = lean_ctor_get(v_snd_690_, 0);
lean_dec(v_unused_777_);
v___x_703_ = v_snd_690_;
v_isShared_704_ = v_isSharedCheck_774_;
goto v_resetjp_702_;
}
else
{
lean_dec(v_snd_690_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_774_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_a_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v_a_705_ = lean_array_uget_borrowed(v_as_679_, v_i_681_);
v___x_706_ = lean_array_fget(v_array_694_, v_start_695_);
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_add(v_start_695_, v___x_707_);
lean_dec(v_start_695_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 1, v___x_708_);
v___x_710_ = v___x_703_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_array_694_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_stop_696_);
v___x_710_ = v_reuseFailAlloc_773_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
uint8_t v___y_712_; 
switch(lean_obj_tag(v_a_705_))
{
case 0:
{
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_ctorName_721_; lean_object* v_params_722_; lean_object* v_code_723_; lean_object* v_ctorName_724_; lean_object* v_params_725_; lean_object* v_code_726_; uint8_t v___x_727_; 
v_ctorName_721_ = lean_ctor_get(v_a_705_, 0);
v_params_722_ = lean_ctor_get(v_a_705_, 1);
v_code_723_ = lean_ctor_get(v_a_705_, 2);
v_ctorName_724_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_ctorName_724_);
v_params_725_ = lean_ctor_get(v___x_706_, 1);
lean_inc_ref(v_params_725_);
v_code_726_ = lean_ctor_get(v___x_706_, 2);
lean_inc_ref(v_code_726_);
lean_dec_ref_known(v___x_706_, 3);
v___x_727_ = lean_name_eq(v_ctorName_721_, v_ctorName_724_);
lean_dec(v_ctorName_724_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v_code_726_);
lean_dec_ref(v_params_725_);
lean_del_object(v___x_692_);
v___x_728_ = lean_box(v___x_727_);
v___x_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_729_, 0, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_710_);
return v___x_730_;
}
else
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = lean_array_get_size(v_params_725_);
v___x_732_ = lean_array_get_size(v_params_722_);
v___x_733_ = lean_nat_dec_eq(v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_dec_ref(v_code_726_);
lean_dec_ref(v_params_725_);
v___y_712_ = v___x_733_;
goto v___jp_711_;
}
else
{
lean_object* v___x_734_; uint8_t v___x_735_; 
v___x_734_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_683_);
lean_inc_ref(v_code_723_);
v___x_735_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_678_, v_code_723_, v_code_726_, v_params_722_, v_params_725_, v___x_734_, v___y_683_);
lean_dec_ref(v_params_725_);
if (v___x_735_ == 0)
{
v___y_712_ = v___x_735_;
goto v___jp_711_;
}
else
{
lean_object* v___x_736_; 
lean_del_object(v___x_692_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_697_);
lean_ctor_set(v___x_736_, 1, v___x_710_);
v_a_685_ = v___x_736_;
goto v___jp_684_;
}
}
}
}
else
{
lean_dec(v___x_706_);
lean_del_object(v___x_692_);
goto v___jp_718_;
}
}
case 1:
{
lean_del_object(v___x_692_);
if (lean_obj_tag(v___x_706_) == 1)
{
lean_object* v_info_737_; lean_object* v_code_738_; lean_object* v_info_739_; lean_object* v_code_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_759_; 
v_info_737_ = lean_ctor_get(v_a_705_, 0);
v_code_738_ = lean_ctor_get(v_a_705_, 1);
v_info_739_ = lean_ctor_get(v___x_706_, 0);
v_code_740_ = lean_ctor_get(v___x_706_, 1);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_759_ == 0)
{
v___x_742_ = v___x_706_;
v_isShared_743_ = v_isSharedCheck_759_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_code_740_);
lean_inc(v_info_739_);
lean_dec(v___x_706_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_759_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
uint8_t v___x_744_; 
v___x_744_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_info_737_, v_info_739_);
lean_dec_ref(v_info_739_);
if (v___x_744_ == 0)
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_748_; 
lean_dec_ref(v_code_740_);
v___x_745_ = lean_box(v___x_744_);
v___x_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 0);
lean_ctor_set(v___x_742_, 1, v___x_710_);
lean_ctor_set(v___x_742_, 0, v___x_746_);
v___x_748_ = v___x_742_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_710_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
else
{
uint8_t v___x_750_; 
lean_inc(v___y_683_);
lean_inc_ref(v_code_738_);
v___x_750_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_678_, v_code_738_, v_code_740_, v___y_683_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_751_ = lean_box(v___x_750_);
v___x_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_752_, 0, v___x_751_);
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 0);
lean_ctor_set(v___x_742_, 1, v___x_710_);
lean_ctor_set(v___x_742_, 0, v___x_752_);
v___x_754_ = v___x_742_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v___x_710_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
else
{
lean_object* v___x_757_; 
if (v_isShared_743_ == 0)
{
lean_ctor_set_tag(v___x_742_, 0);
lean_ctor_set(v___x_742_, 1, v___x_710_);
lean_ctor_set(v___x_742_, 0, v___x_697_);
v___x_757_ = v___x_742_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_710_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
v_a_685_ = v___x_757_;
goto v___jp_684_;
}
}
}
}
}
else
{
lean_dec(v___x_706_);
goto v___jp_718_;
}
}
default: 
{
lean_del_object(v___x_692_);
if (lean_obj_tag(v___x_706_) == 2)
{
lean_object* v_code_760_; lean_object* v_code_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_772_; 
v_code_760_ = lean_ctor_get(v_a_705_, 0);
v_code_761_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_772_ == 0)
{
v___x_763_ = v___x_706_;
v_isShared_764_ = v_isSharedCheck_772_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_code_761_);
lean_dec(v___x_706_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_772_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
uint8_t v___x_765_; 
lean_inc(v___y_683_);
lean_inc_ref(v_code_760_);
v___x_765_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_678_, v_code_760_, v_code_761_, v___y_683_);
if (v___x_765_ == 0)
{
lean_object* v___x_766_; lean_object* v___x_768_; 
v___x_766_ = lean_box(v___x_765_);
if (v_isShared_764_ == 0)
{
lean_ctor_set_tag(v___x_763_, 1);
lean_ctor_set(v___x_763_, 0, v___x_766_);
v___x_768_ = v___x_763_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_770_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
lean_ctor_set(v___x_769_, 1, v___x_710_);
return v___x_769_;
}
}
else
{
lean_object* v___x_771_; 
lean_del_object(v___x_763_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v___x_697_);
lean_ctor_set(v___x_771_, 1, v___x_710_);
v_a_685_ = v___x_771_;
goto v___jp_684_;
}
}
}
else
{
lean_dec(v___x_706_);
goto v___jp_718_;
}
}
}
v___jp_711_:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_box(v___y_712_);
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 1, v___x_710_);
lean_ctor_set(v___x_692_, 0, v___x_714_);
v___x_716_ = v___x_692_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_710_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
v___jp_718_:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0));
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
lean_ctor_set(v___x_720_, 1, v___x_710_);
return v___x_720_;
}
}
}
}
}
}
v___jp_684_:
{
size_t v___x_686_; size_t v___x_687_; 
v___x_686_ = ((size_t)1ULL);
v___x_687_ = lean_usize_add(v_i_681_, v___x_686_);
v_i_681_ = v___x_687_;
v_b_682_ = v_a_685_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(uint8_t v_pu_780_, lean_object* v_alts_u2081_781_, lean_object* v_alts_u2082_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_784_; lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_784_ = lean_array_get_size(v_alts_u2081_781_);
v___x_785_ = lean_array_get_size(v_alts_u2082_782_);
v___x_786_ = lean_nat_dec_eq(v___x_784_, v___x_785_);
if (v___x_786_ == 0)
{
lean_dec_ref(v_alts_u2082_782_);
lean_dec_ref(v_alts_u2081_781_);
return v___x_786_;
}
else
{
lean_object* v_alts_u2081_787_; lean_object* v_alts_u2082_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; size_t v_sz_794_; size_t v___x_795_; lean_object* v___x_796_; lean_object* v_fst_797_; 
v_alts_u2081_787_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2081_781_);
v_alts_u2082_788_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2082_782_);
v___x_789_ = lean_unsigned_to_nat(0u);
v___x_790_ = lean_array_get_size(v_alts_u2082_788_);
v___x_791_ = l_Array_toSubarray___redArg(v_alts_u2082_788_, v___x_789_, v___x_790_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v___x_791_);
v_sz_794_ = lean_array_size(v_alts_u2081_787_);
v___x_795_ = ((size_t)0ULL);
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_780_, v_alts_u2081_787_, v_sz_794_, v___x_795_, v___x_793_, v_a_783_);
lean_dec_ref(v_alts_u2081_787_);
v_fst_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_fst_797_);
lean_dec_ref(v___x_796_);
if (lean_obj_tag(v_fst_797_) == 0)
{
return v___x_786_;
}
else
{
lean_object* v_val_798_; uint8_t v___x_799_; 
v_val_798_ = lean_ctor_get(v_fst_797_, 0);
lean_inc(v_val_798_);
lean_dec_ref_known(v_fst_797_, 1);
v___x_799_ = lean_unbox(v_val_798_);
lean_dec(v_val_798_);
return v___x_799_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqv(uint8_t v_pu_800_, lean_object* v_code_u2081_801_, lean_object* v_code_u2082_802_, lean_object* v_a_803_){
_start:
{
switch(lean_obj_tag(v_code_u2081_801_))
{
case 0:
{
if (lean_obj_tag(v_code_u2082_802_) == 0)
{
lean_object* v_decl_804_; lean_object* v_decl_805_; lean_object* v_k_806_; lean_object* v_k_807_; lean_object* v_fvarId_808_; lean_object* v_type_809_; lean_object* v_value_810_; lean_object* v_fvarId_811_; lean_object* v_type_812_; lean_object* v_value_813_; uint8_t v___x_814_; 
v_decl_804_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc_ref(v_decl_804_);
v_decl_805_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc_ref(v_decl_805_);
v_k_806_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc_ref(v_k_806_);
lean_dec_ref_known(v_code_u2081_801_, 2);
v_k_807_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc_ref(v_k_807_);
lean_dec_ref_known(v_code_u2082_802_, 2);
v_fvarId_808_ = lean_ctor_get(v_decl_804_, 0);
lean_inc(v_fvarId_808_);
v_type_809_ = lean_ctor_get(v_decl_804_, 2);
lean_inc_ref(v_type_809_);
v_value_810_ = lean_ctor_get(v_decl_804_, 3);
lean_inc(v_value_810_);
lean_dec_ref(v_decl_804_);
v_fvarId_811_ = lean_ctor_get(v_decl_805_, 0);
lean_inc(v_fvarId_811_);
v_type_812_ = lean_ctor_get(v_decl_805_, 2);
lean_inc_ref(v_type_812_);
v_value_813_ = lean_ctor_get(v_decl_805_, 3);
lean_inc(v_value_813_);
lean_dec_ref(v_decl_805_);
v___x_814_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_809_, v_type_812_, v_a_803_);
lean_dec_ref(v_type_812_);
lean_dec_ref(v_type_809_);
if (v___x_814_ == 0)
{
lean_dec(v_value_813_);
lean_dec(v_fvarId_811_);
lean_dec(v_value_810_);
lean_dec(v_fvarId_808_);
lean_dec_ref(v_k_807_);
lean_dec_ref(v_k_806_);
lean_dec(v_a_803_);
return v___x_814_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_800_, v_value_810_, v_value_813_, v_a_803_);
lean_dec(v_value_810_);
if (v___x_815_ == 0)
{
lean_dec(v_fvarId_811_);
lean_dec(v_fvarId_808_);
lean_dec_ref(v_k_807_);
lean_dec_ref(v_k_806_);
lean_dec(v_a_803_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; 
v___x_816_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_811_, v_fvarId_808_, v_a_803_);
v_code_u2081_801_ = v_k_806_;
v_code_u2082_802_ = v_k_807_;
v_a_803_ = v___x_816_;
goto _start;
}
}
}
else
{
uint8_t v___x_818_; 
lean_dec_ref_known(v_code_u2081_801_, 2);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_818_ = 0;
return v___x_818_;
}
}
case 1:
{
if (lean_obj_tag(v_code_u2082_802_) == 1)
{
lean_object* v_decl_819_; lean_object* v_decl_820_; lean_object* v_k_821_; lean_object* v_k_822_; lean_object* v_fvarId_823_; lean_object* v_params_824_; lean_object* v_type_825_; lean_object* v_value_826_; lean_object* v_fvarId_827_; lean_object* v_params_828_; lean_object* v_type_829_; lean_object* v_value_830_; uint8_t v___x_831_; 
v_decl_819_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc_ref(v_decl_819_);
v_decl_820_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc_ref(v_decl_820_);
v_k_821_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc_ref(v_k_821_);
lean_dec_ref_known(v_code_u2081_801_, 2);
v_k_822_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc_ref(v_k_822_);
lean_dec_ref_known(v_code_u2082_802_, 2);
v_fvarId_823_ = lean_ctor_get(v_decl_819_, 0);
lean_inc(v_fvarId_823_);
v_params_824_ = lean_ctor_get(v_decl_819_, 2);
lean_inc_ref(v_params_824_);
v_type_825_ = lean_ctor_get(v_decl_819_, 3);
lean_inc_ref(v_type_825_);
v_value_826_ = lean_ctor_get(v_decl_819_, 4);
lean_inc_ref(v_value_826_);
lean_dec_ref(v_decl_819_);
v_fvarId_827_ = lean_ctor_get(v_decl_820_, 0);
lean_inc(v_fvarId_827_);
v_params_828_ = lean_ctor_get(v_decl_820_, 2);
lean_inc_ref(v_params_828_);
v_type_829_ = lean_ctor_get(v_decl_820_, 3);
lean_inc_ref(v_type_829_);
v_value_830_ = lean_ctor_get(v_decl_820_, 4);
lean_inc_ref(v_value_830_);
lean_dec_ref(v_decl_820_);
v___x_831_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_825_, v_type_829_, v_a_803_);
lean_dec_ref(v_type_829_);
lean_dec_ref(v_type_825_);
if (v___x_831_ == 0)
{
lean_dec_ref(v_value_830_);
lean_dec_ref(v_params_828_);
lean_dec(v_fvarId_827_);
lean_dec_ref(v_value_826_);
lean_dec_ref(v_params_824_);
lean_dec(v_fvarId_823_);
lean_dec_ref(v_k_822_);
lean_dec_ref(v_k_821_);
lean_dec(v_a_803_);
return v___x_831_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_832_ = lean_array_get_size(v_params_828_);
v___x_833_ = lean_array_get_size(v_params_824_);
v___x_834_ = lean_nat_dec_eq(v___x_832_, v___x_833_);
if (v___x_834_ == 0)
{
lean_dec_ref(v_value_830_);
lean_dec_ref(v_params_828_);
lean_dec(v_fvarId_827_);
lean_dec_ref(v_value_826_);
lean_dec_ref(v_params_824_);
lean_dec(v_fvarId_823_);
lean_dec_ref(v_k_822_);
lean_dec_ref(v_k_821_);
lean_dec(v_a_803_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_835_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_803_);
v___x_836_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_800_, v_value_826_, v_value_830_, v_params_824_, v_params_828_, v___x_835_, v_a_803_);
lean_dec_ref(v_params_828_);
lean_dec_ref(v_params_824_);
if (v___x_836_ == 0)
{
lean_dec(v_fvarId_827_);
lean_dec(v_fvarId_823_);
lean_dec_ref(v_k_822_);
lean_dec_ref(v_k_821_);
lean_dec(v_a_803_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_827_, v_fvarId_823_, v_a_803_);
v_code_u2081_801_ = v_k_821_;
v_code_u2082_802_ = v_k_822_;
v_a_803_ = v___x_837_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_839_; 
lean_dec_ref_known(v_code_u2081_801_, 2);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_839_ = 0;
return v___x_839_;
}
}
case 2:
{
if (lean_obj_tag(v_code_u2082_802_) == 2)
{
lean_object* v_decl_840_; lean_object* v_decl_841_; lean_object* v_k_842_; lean_object* v_k_843_; lean_object* v_fvarId_844_; lean_object* v_params_845_; lean_object* v_type_846_; lean_object* v_value_847_; lean_object* v_fvarId_848_; lean_object* v_params_849_; lean_object* v_type_850_; lean_object* v_value_851_; uint8_t v___x_852_; 
v_decl_840_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc_ref(v_decl_840_);
v_decl_841_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc_ref(v_decl_841_);
v_k_842_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc_ref(v_k_842_);
lean_dec_ref_known(v_code_u2081_801_, 2);
v_k_843_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc_ref(v_k_843_);
lean_dec_ref_known(v_code_u2082_802_, 2);
v_fvarId_844_ = lean_ctor_get(v_decl_840_, 0);
lean_inc(v_fvarId_844_);
v_params_845_ = lean_ctor_get(v_decl_840_, 2);
lean_inc_ref(v_params_845_);
v_type_846_ = lean_ctor_get(v_decl_840_, 3);
lean_inc_ref(v_type_846_);
v_value_847_ = lean_ctor_get(v_decl_840_, 4);
lean_inc_ref(v_value_847_);
lean_dec_ref(v_decl_840_);
v_fvarId_848_ = lean_ctor_get(v_decl_841_, 0);
lean_inc(v_fvarId_848_);
v_params_849_ = lean_ctor_get(v_decl_841_, 2);
lean_inc_ref(v_params_849_);
v_type_850_ = lean_ctor_get(v_decl_841_, 3);
lean_inc_ref(v_type_850_);
v_value_851_ = lean_ctor_get(v_decl_841_, 4);
lean_inc_ref(v_value_851_);
lean_dec_ref(v_decl_841_);
v___x_852_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_846_, v_type_850_, v_a_803_);
lean_dec_ref(v_type_850_);
lean_dec_ref(v_type_846_);
if (v___x_852_ == 0)
{
lean_dec_ref(v_value_851_);
lean_dec_ref(v_params_849_);
lean_dec(v_fvarId_848_);
lean_dec_ref(v_value_847_);
lean_dec_ref(v_params_845_);
lean_dec(v_fvarId_844_);
lean_dec_ref(v_k_843_);
lean_dec_ref(v_k_842_);
lean_dec(v_a_803_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v___x_853_ = lean_array_get_size(v_params_849_);
v___x_854_ = lean_array_get_size(v_params_845_);
v___x_855_ = lean_nat_dec_eq(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
lean_dec_ref(v_value_851_);
lean_dec_ref(v_params_849_);
lean_dec(v_fvarId_848_);
lean_dec_ref(v_value_847_);
lean_dec_ref(v_params_845_);
lean_dec(v_fvarId_844_);
lean_dec_ref(v_k_843_);
lean_dec_ref(v_k_842_);
lean_dec(v_a_803_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; uint8_t v___x_857_; 
v___x_856_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_803_);
v___x_857_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_800_, v_value_847_, v_value_851_, v_params_845_, v_params_849_, v___x_856_, v_a_803_);
lean_dec_ref(v_params_849_);
lean_dec_ref(v_params_845_);
if (v___x_857_ == 0)
{
lean_dec(v_fvarId_848_);
lean_dec(v_fvarId_844_);
lean_dec_ref(v_k_843_);
lean_dec_ref(v_k_842_);
lean_dec(v_a_803_);
return v___x_857_;
}
else
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_848_, v_fvarId_844_, v_a_803_);
v_code_u2081_801_ = v_k_842_;
v_code_u2082_802_ = v_k_843_;
v_a_803_ = v___x_858_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_860_; 
lean_dec_ref_known(v_code_u2081_801_, 2);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_860_ = 0;
return v___x_860_;
}
}
case 3:
{
if (lean_obj_tag(v_code_u2082_802_) == 3)
{
lean_object* v_fvarId_861_; lean_object* v_args_862_; lean_object* v_fvarId_863_; lean_object* v_args_864_; uint8_t v___x_865_; 
v_fvarId_861_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc(v_fvarId_861_);
v_args_862_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc_ref(v_args_862_);
lean_dec_ref_known(v_code_u2081_801_, 2);
v_fvarId_863_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc(v_fvarId_863_);
v_args_864_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc_ref(v_args_864_);
lean_dec_ref_known(v_code_u2082_802_, 2);
v___x_865_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_861_, v_fvarId_863_, v_a_803_);
lean_dec(v_fvarId_863_);
lean_dec(v_fvarId_861_);
if (v___x_865_ == 0)
{
lean_dec_ref(v_args_864_);
lean_dec_ref(v_args_862_);
lean_dec(v_a_803_);
return v___x_865_;
}
else
{
uint8_t v___x_866_; 
v___x_866_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_800_, v_args_862_, v_args_864_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_args_862_);
return v___x_866_;
}
}
else
{
uint8_t v___x_867_; 
lean_dec_ref_known(v_code_u2081_801_, 2);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_867_ = 0;
return v___x_867_;
}
}
case 4:
{
if (lean_obj_tag(v_code_u2082_802_) == 4)
{
lean_object* v_cases_868_; lean_object* v_cases_869_; lean_object* v_resultType_870_; lean_object* v_discr_871_; lean_object* v_alts_872_; lean_object* v_resultType_873_; lean_object* v_discr_874_; lean_object* v_alts_875_; uint8_t v___x_876_; 
v_cases_868_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc_ref(v_cases_868_);
lean_dec_ref_known(v_code_u2081_801_, 1);
v_cases_869_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc_ref(v_cases_869_);
lean_dec_ref_known(v_code_u2082_802_, 1);
v_resultType_870_ = lean_ctor_get(v_cases_868_, 1);
lean_inc_ref(v_resultType_870_);
v_discr_871_ = lean_ctor_get(v_cases_868_, 2);
lean_inc(v_discr_871_);
v_alts_872_ = lean_ctor_get(v_cases_868_, 3);
lean_inc_ref(v_alts_872_);
lean_dec_ref(v_cases_868_);
v_resultType_873_ = lean_ctor_get(v_cases_869_, 1);
lean_inc_ref(v_resultType_873_);
v_discr_874_ = lean_ctor_get(v_cases_869_, 2);
lean_inc(v_discr_874_);
v_alts_875_ = lean_ctor_get(v_cases_869_, 3);
lean_inc_ref(v_alts_875_);
lean_dec_ref(v_cases_869_);
v___x_876_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_discr_871_, v_discr_874_, v_a_803_);
lean_dec(v_discr_874_);
lean_dec(v_discr_871_);
if (v___x_876_ == 0)
{
lean_dec_ref(v_alts_875_);
lean_dec_ref(v_resultType_873_);
lean_dec_ref(v_alts_872_);
lean_dec_ref(v_resultType_870_);
lean_dec(v_a_803_);
return v___x_876_;
}
else
{
uint8_t v___x_877_; 
v___x_877_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_resultType_870_, v_resultType_873_, v_a_803_);
lean_dec_ref(v_resultType_873_);
lean_dec_ref(v_resultType_870_);
if (v___x_877_ == 0)
{
lean_dec_ref(v_alts_875_);
lean_dec_ref(v_alts_872_);
lean_dec(v_a_803_);
return v___x_877_;
}
else
{
uint8_t v___x_878_; 
v___x_878_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_800_, v_alts_872_, v_alts_875_, v_a_803_);
lean_dec(v_a_803_);
return v___x_878_;
}
}
}
else
{
uint8_t v___x_879_; 
lean_dec_ref_known(v_code_u2081_801_, 1);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_879_ = 0;
return v___x_879_;
}
}
case 5:
{
if (lean_obj_tag(v_code_u2082_802_) == 5)
{
lean_object* v_fvarId_880_; lean_object* v_fvarId_881_; uint8_t v___x_882_; 
v_fvarId_880_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc(v_fvarId_880_);
lean_dec_ref_known(v_code_u2081_801_, 1);
v_fvarId_881_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc(v_fvarId_881_);
lean_dec_ref_known(v_code_u2082_802_, 1);
v___x_882_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_880_, v_fvarId_881_, v_a_803_);
lean_dec(v_a_803_);
lean_dec(v_fvarId_881_);
lean_dec(v_fvarId_880_);
return v___x_882_;
}
else
{
uint8_t v___x_883_; 
lean_dec_ref_known(v_code_u2081_801_, 1);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_883_ = 0;
return v___x_883_;
}
}
case 6:
{
if (lean_obj_tag(v_code_u2082_802_) == 6)
{
lean_object* v_type_884_; lean_object* v_type_885_; uint8_t v___x_886_; 
v_type_884_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc_ref(v_type_884_);
lean_dec_ref_known(v_code_u2081_801_, 1);
v_type_885_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc_ref(v_type_885_);
lean_dec_ref_known(v_code_u2082_802_, 1);
v___x_886_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_884_, v_type_885_, v_a_803_);
lean_dec(v_a_803_);
lean_dec_ref(v_type_885_);
lean_dec_ref(v_type_884_);
return v___x_886_;
}
else
{
uint8_t v___x_887_; 
lean_dec_ref_known(v_code_u2081_801_, 1);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_887_ = 0;
return v___x_887_;
}
}
case 7:
{
if (lean_obj_tag(v_code_u2082_802_) == 7)
{
lean_object* v_fvarId_888_; lean_object* v_i_889_; lean_object* v_y_890_; lean_object* v_k_891_; lean_object* v_fvarId_892_; lean_object* v_i_893_; lean_object* v_y_894_; lean_object* v_k_895_; uint8_t v___x_896_; 
v_fvarId_888_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc(v_fvarId_888_);
v_i_889_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc(v_i_889_);
v_y_890_ = lean_ctor_get(v_code_u2081_801_, 2);
lean_inc(v_y_890_);
v_k_891_ = lean_ctor_get(v_code_u2081_801_, 3);
lean_inc_ref(v_k_891_);
lean_dec_ref_known(v_code_u2081_801_, 4);
v_fvarId_892_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc(v_fvarId_892_);
v_i_893_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc(v_i_893_);
v_y_894_ = lean_ctor_get(v_code_u2082_802_, 2);
lean_inc(v_y_894_);
v_k_895_ = lean_ctor_get(v_code_u2082_802_, 3);
lean_inc_ref(v_k_895_);
lean_dec_ref_known(v_code_u2082_802_, 4);
v___x_896_ = lean_nat_dec_eq(v_i_889_, v_i_893_);
lean_dec(v_i_893_);
lean_dec(v_i_889_);
if (v___x_896_ == 0)
{
lean_dec_ref(v_k_895_);
lean_dec(v_y_894_);
lean_dec(v_fvarId_892_);
lean_dec_ref(v_k_891_);
lean_dec(v_y_890_);
lean_dec(v_fvarId_888_);
lean_dec(v_a_803_);
return v___x_896_;
}
else
{
uint8_t v___x_897_; 
v___x_897_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_888_, v_fvarId_892_, v_a_803_);
lean_dec(v_fvarId_892_);
lean_dec(v_fvarId_888_);
if (v___x_897_ == 0)
{
lean_dec_ref(v_k_895_);
lean_dec(v_y_894_);
lean_dec_ref(v_k_891_);
lean_dec(v_y_890_);
lean_dec(v_a_803_);
return v___x_897_;
}
else
{
uint8_t v___x_898_; 
v___x_898_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_y_890_, v_y_894_, v_a_803_);
lean_dec(v_y_894_);
lean_dec(v_y_890_);
if (v___x_898_ == 0)
{
lean_dec_ref(v_k_895_);
lean_dec_ref(v_k_891_);
lean_dec(v_a_803_);
return v___x_898_;
}
else
{
v_code_u2081_801_ = v_k_891_;
v_code_u2082_802_ = v_k_895_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_900_; 
lean_dec_ref_known(v_code_u2081_801_, 4);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_900_ = 0;
return v___x_900_;
}
}
case 8:
{
if (lean_obj_tag(v_code_u2082_802_) == 8)
{
lean_object* v_fvarId_901_; lean_object* v_i_902_; lean_object* v_y_903_; lean_object* v_k_904_; lean_object* v_fvarId_905_; lean_object* v_i_906_; lean_object* v_y_907_; lean_object* v_k_908_; uint8_t v___x_909_; 
v_fvarId_901_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc(v_fvarId_901_);
v_i_902_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc(v_i_902_);
v_y_903_ = lean_ctor_get(v_code_u2081_801_, 2);
lean_inc(v_y_903_);
v_k_904_ = lean_ctor_get(v_code_u2081_801_, 3);
lean_inc_ref(v_k_904_);
lean_dec_ref_known(v_code_u2081_801_, 4);
v_fvarId_905_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc(v_fvarId_905_);
v_i_906_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc(v_i_906_);
v_y_907_ = lean_ctor_get(v_code_u2082_802_, 2);
lean_inc(v_y_907_);
v_k_908_ = lean_ctor_get(v_code_u2082_802_, 3);
lean_inc_ref(v_k_908_);
lean_dec_ref_known(v_code_u2082_802_, 4);
v___x_909_ = lean_nat_dec_eq(v_i_902_, v_i_906_);
lean_dec(v_i_906_);
lean_dec(v_i_902_);
if (v___x_909_ == 0)
{
lean_dec_ref(v_k_908_);
lean_dec(v_y_907_);
lean_dec(v_fvarId_905_);
lean_dec_ref(v_k_904_);
lean_dec(v_y_903_);
lean_dec(v_fvarId_901_);
lean_dec(v_a_803_);
return v___x_909_;
}
else
{
uint8_t v___x_910_; 
v___x_910_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_901_, v_fvarId_905_, v_a_803_);
lean_dec(v_fvarId_905_);
lean_dec(v_fvarId_901_);
if (v___x_910_ == 0)
{
lean_dec_ref(v_k_908_);
lean_dec(v_y_907_);
lean_dec_ref(v_k_904_);
lean_dec(v_y_903_);
lean_dec(v_a_803_);
return v___x_910_;
}
else
{
uint8_t v___x_911_; 
v___x_911_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_903_, v_y_907_, v_a_803_);
lean_dec(v_y_907_);
lean_dec(v_y_903_);
if (v___x_911_ == 0)
{
lean_dec_ref(v_k_908_);
lean_dec_ref(v_k_904_);
lean_dec(v_a_803_);
return v___x_911_;
}
else
{
v_code_u2081_801_ = v_k_904_;
v_code_u2082_802_ = v_k_908_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_913_; 
lean_dec_ref_known(v_code_u2081_801_, 4);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_913_ = 0;
return v___x_913_;
}
}
case 9:
{
if (lean_obj_tag(v_code_u2082_802_) == 9)
{
lean_object* v_fvarId_914_; lean_object* v_i_915_; lean_object* v_offset_916_; lean_object* v_y_917_; lean_object* v_ty_918_; lean_object* v_k_919_; lean_object* v_fvarId_920_; lean_object* v_i_921_; lean_object* v_offset_922_; lean_object* v_y_923_; lean_object* v_ty_924_; lean_object* v_k_925_; uint8_t v___x_926_; 
v_fvarId_914_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc(v_fvarId_914_);
v_i_915_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc(v_i_915_);
v_offset_916_ = lean_ctor_get(v_code_u2081_801_, 2);
lean_inc(v_offset_916_);
v_y_917_ = lean_ctor_get(v_code_u2081_801_, 3);
lean_inc(v_y_917_);
v_ty_918_ = lean_ctor_get(v_code_u2081_801_, 4);
lean_inc_ref(v_ty_918_);
v_k_919_ = lean_ctor_get(v_code_u2081_801_, 5);
lean_inc_ref(v_k_919_);
lean_dec_ref_known(v_code_u2081_801_, 6);
v_fvarId_920_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc(v_fvarId_920_);
v_i_921_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc(v_i_921_);
v_offset_922_ = lean_ctor_get(v_code_u2082_802_, 2);
lean_inc(v_offset_922_);
v_y_923_ = lean_ctor_get(v_code_u2082_802_, 3);
lean_inc(v_y_923_);
v_ty_924_ = lean_ctor_get(v_code_u2082_802_, 4);
lean_inc_ref(v_ty_924_);
v_k_925_ = lean_ctor_get(v_code_u2082_802_, 5);
lean_inc_ref(v_k_925_);
lean_dec_ref_known(v_code_u2082_802_, 6);
v___x_926_ = lean_nat_dec_eq(v_i_915_, v_i_921_);
lean_dec(v_i_921_);
lean_dec(v_i_915_);
if (v___x_926_ == 0)
{
lean_dec_ref(v_k_925_);
lean_dec_ref(v_ty_924_);
lean_dec(v_y_923_);
lean_dec(v_offset_922_);
lean_dec(v_fvarId_920_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v_ty_918_);
lean_dec(v_y_917_);
lean_dec(v_offset_916_);
lean_dec(v_fvarId_914_);
lean_dec(v_a_803_);
return v___x_926_;
}
else
{
uint8_t v___x_927_; 
v___x_927_ = lean_nat_dec_eq(v_offset_916_, v_offset_922_);
lean_dec(v_offset_922_);
lean_dec(v_offset_916_);
if (v___x_927_ == 0)
{
lean_dec_ref(v_k_925_);
lean_dec_ref(v_ty_924_);
lean_dec(v_y_923_);
lean_dec(v_fvarId_920_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v_ty_918_);
lean_dec(v_y_917_);
lean_dec(v_fvarId_914_);
lean_dec(v_a_803_);
return v___x_927_;
}
else
{
uint8_t v___x_928_; 
v___x_928_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_914_, v_fvarId_920_, v_a_803_);
lean_dec(v_fvarId_920_);
lean_dec(v_fvarId_914_);
if (v___x_928_ == 0)
{
lean_dec_ref(v_k_925_);
lean_dec_ref(v_ty_924_);
lean_dec(v_y_923_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v_ty_918_);
lean_dec(v_y_917_);
lean_dec(v_a_803_);
return v___x_928_;
}
else
{
uint8_t v___x_929_; 
v___x_929_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_917_, v_y_923_, v_a_803_);
lean_dec(v_y_923_);
lean_dec(v_y_917_);
if (v___x_929_ == 0)
{
lean_dec_ref(v_k_925_);
lean_dec_ref(v_ty_924_);
lean_dec_ref(v_k_919_);
lean_dec_ref(v_ty_918_);
lean_dec(v_a_803_);
return v___x_929_;
}
else
{
uint8_t v___x_930_; 
v___x_930_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_918_, v_ty_924_, v_a_803_);
lean_dec_ref(v_ty_924_);
lean_dec_ref(v_ty_918_);
if (v___x_930_ == 0)
{
lean_dec_ref(v_k_925_);
lean_dec_ref(v_k_919_);
lean_dec(v_a_803_);
return v___x_930_;
}
else
{
v_code_u2081_801_ = v_k_919_;
v_code_u2082_802_ = v_k_925_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_932_; 
lean_dec_ref_known(v_code_u2081_801_, 6);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_932_ = 0;
return v___x_932_;
}
}
case 10:
{
if (lean_obj_tag(v_code_u2082_802_) == 10)
{
lean_object* v_fvarId_933_; lean_object* v_cidx_934_; lean_object* v_k_935_; lean_object* v_fvarId_936_; lean_object* v_cidx_937_; lean_object* v_k_938_; uint8_t v___x_939_; 
v_fvarId_933_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc(v_fvarId_933_);
v_cidx_934_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc(v_cidx_934_);
v_k_935_ = lean_ctor_get(v_code_u2081_801_, 2);
lean_inc_ref(v_k_935_);
lean_dec_ref_known(v_code_u2081_801_, 3);
v_fvarId_936_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc(v_fvarId_936_);
v_cidx_937_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc(v_cidx_937_);
v_k_938_ = lean_ctor_get(v_code_u2082_802_, 2);
lean_inc_ref(v_k_938_);
lean_dec_ref_known(v_code_u2082_802_, 3);
v___x_939_ = lean_nat_dec_eq(v_cidx_934_, v_cidx_937_);
lean_dec(v_cidx_937_);
lean_dec(v_cidx_934_);
if (v___x_939_ == 0)
{
lean_dec_ref(v_k_938_);
lean_dec(v_fvarId_936_);
lean_dec_ref(v_k_935_);
lean_dec(v_fvarId_933_);
lean_dec(v_a_803_);
return v___x_939_;
}
else
{
uint8_t v___x_940_; 
v___x_940_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_933_, v_fvarId_936_, v_a_803_);
lean_dec(v_fvarId_936_);
lean_dec(v_fvarId_933_);
if (v___x_940_ == 0)
{
lean_dec_ref(v_k_938_);
lean_dec_ref(v_k_935_);
lean_dec(v_a_803_);
return v___x_940_;
}
else
{
v_code_u2081_801_ = v_k_935_;
v_code_u2082_802_ = v_k_938_;
goto _start;
}
}
}
else
{
uint8_t v___x_942_; 
lean_dec_ref_known(v_code_u2081_801_, 3);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_942_ = 0;
return v___x_942_;
}
}
case 11:
{
if (lean_obj_tag(v_code_u2082_802_) == 11)
{
lean_object* v_fvarId_943_; lean_object* v_n_944_; uint8_t v_check_945_; uint8_t v_persistent_946_; lean_object* v_k_947_; lean_object* v_fvarId_948_; lean_object* v_n_949_; uint8_t v_check_950_; uint8_t v_persistent_951_; lean_object* v_k_952_; uint8_t v___x_957_; 
v_fvarId_943_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc(v_fvarId_943_);
v_n_944_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc(v_n_944_);
v_check_945_ = lean_ctor_get_uint8(v_code_u2081_801_, sizeof(void*)*3);
v_persistent_946_ = lean_ctor_get_uint8(v_code_u2081_801_, sizeof(void*)*3 + 1);
v_k_947_ = lean_ctor_get(v_code_u2081_801_, 2);
lean_inc_ref(v_k_947_);
lean_dec_ref_known(v_code_u2081_801_, 3);
v_fvarId_948_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc(v_fvarId_948_);
v_n_949_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc(v_n_949_);
v_check_950_ = lean_ctor_get_uint8(v_code_u2082_802_, sizeof(void*)*3);
v_persistent_951_ = lean_ctor_get_uint8(v_code_u2082_802_, sizeof(void*)*3 + 1);
v_k_952_ = lean_ctor_get(v_code_u2082_802_, 2);
lean_inc_ref(v_k_952_);
lean_dec_ref_known(v_code_u2082_802_, 3);
v___x_957_ = lean_nat_dec_eq(v_n_944_, v_n_949_);
lean_dec(v_n_949_);
lean_dec(v_n_944_);
if (v___x_957_ == 0)
{
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec_ref(v_k_947_);
lean_dec(v_fvarId_943_);
lean_dec(v_a_803_);
return v___x_957_;
}
else
{
if (v_check_950_ == 0)
{
if (v_check_945_ == 0)
{
goto v___jp_956_;
}
else
{
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec_ref(v_k_947_);
lean_dec(v_fvarId_943_);
lean_dec(v_a_803_);
return v_check_950_;
}
}
else
{
if (v_check_945_ == 0)
{
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec_ref(v_k_947_);
lean_dec(v_fvarId_943_);
lean_dec(v_a_803_);
return v_check_945_;
}
else
{
goto v___jp_956_;
}
}
}
v___jp_953_:
{
uint8_t v___x_954_; 
v___x_954_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_943_, v_fvarId_948_, v_a_803_);
lean_dec(v_fvarId_948_);
lean_dec(v_fvarId_943_);
if (v___x_954_ == 0)
{
lean_dec_ref(v_k_952_);
lean_dec_ref(v_k_947_);
lean_dec(v_a_803_);
return v___x_954_;
}
else
{
v_code_u2081_801_ = v_k_947_;
v_code_u2082_802_ = v_k_952_;
goto _start;
}
}
v___jp_956_:
{
if (v_persistent_951_ == 0)
{
if (v_persistent_946_ == 0)
{
goto v___jp_953_;
}
else
{
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec_ref(v_k_947_);
lean_dec(v_fvarId_943_);
lean_dec(v_a_803_);
return v_persistent_951_;
}
}
else
{
if (v_persistent_946_ == 0)
{
lean_dec_ref(v_k_952_);
lean_dec(v_fvarId_948_);
lean_dec_ref(v_k_947_);
lean_dec(v_fvarId_943_);
lean_dec(v_a_803_);
return v_persistent_946_;
}
else
{
goto v___jp_953_;
}
}
}
}
else
{
uint8_t v___x_958_; 
lean_dec_ref_known(v_code_u2081_801_, 3);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_958_ = 0;
return v___x_958_;
}
}
case 12:
{
if (lean_obj_tag(v_code_u2082_802_) == 12)
{
lean_object* v_fvarId_959_; lean_object* v_n_960_; uint8_t v_check_961_; uint8_t v_persistent_962_; lean_object* v_objs_x3f_963_; lean_object* v_k_964_; lean_object* v_fvarId_965_; lean_object* v_n_966_; uint8_t v_check_967_; uint8_t v_persistent_968_; lean_object* v_objs_x3f_969_; lean_object* v_k_970_; uint8_t v___x_976_; 
v_fvarId_959_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc(v_fvarId_959_);
v_n_960_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc(v_n_960_);
v_check_961_ = lean_ctor_get_uint8(v_code_u2081_801_, sizeof(void*)*4);
v_persistent_962_ = lean_ctor_get_uint8(v_code_u2081_801_, sizeof(void*)*4 + 1);
v_objs_x3f_963_ = lean_ctor_get(v_code_u2081_801_, 2);
lean_inc(v_objs_x3f_963_);
v_k_964_ = lean_ctor_get(v_code_u2081_801_, 3);
lean_inc_ref(v_k_964_);
lean_dec_ref_known(v_code_u2081_801_, 4);
v_fvarId_965_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc(v_fvarId_965_);
v_n_966_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc(v_n_966_);
v_check_967_ = lean_ctor_get_uint8(v_code_u2082_802_, sizeof(void*)*4);
v_persistent_968_ = lean_ctor_get_uint8(v_code_u2082_802_, sizeof(void*)*4 + 1);
v_objs_x3f_969_ = lean_ctor_get(v_code_u2082_802_, 2);
lean_inc(v_objs_x3f_969_);
v_k_970_ = lean_ctor_get(v_code_u2082_802_, 3);
lean_inc_ref(v_k_970_);
lean_dec_ref_known(v_code_u2082_802_, 4);
v___x_976_ = lean_nat_dec_eq(v_n_960_, v_n_966_);
lean_dec(v_n_966_);
lean_dec(v_n_960_);
if (v___x_976_ == 0)
{
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec_ref(v_k_964_);
lean_dec(v_objs_x3f_963_);
lean_dec(v_fvarId_959_);
lean_dec(v_a_803_);
return v___x_976_;
}
else
{
if (v_check_967_ == 0)
{
if (v_check_961_ == 0)
{
goto v___jp_975_;
}
else
{
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec_ref(v_k_964_);
lean_dec(v_objs_x3f_963_);
lean_dec(v_fvarId_959_);
lean_dec(v_a_803_);
return v_check_967_;
}
}
else
{
if (v_check_961_ == 0)
{
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec_ref(v_k_964_);
lean_dec(v_objs_x3f_963_);
lean_dec(v_fvarId_959_);
lean_dec(v_a_803_);
return v_check_961_;
}
else
{
goto v___jp_975_;
}
}
}
v___jp_971_:
{
uint8_t v___x_972_; 
v___x_972_ = l_instBEqOption_beq___at___00Lean_Compiler_LCNF_AlphaEqv_eqv_spec__3(v_objs_x3f_963_, v_objs_x3f_969_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_objs_x3f_963_);
if (v___x_972_ == 0)
{
lean_dec_ref(v_k_970_);
lean_dec(v_fvarId_965_);
lean_dec_ref(v_k_964_);
lean_dec(v_fvarId_959_);
lean_dec(v_a_803_);
return v___x_972_;
}
else
{
uint8_t v___x_973_; 
v___x_973_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_959_, v_fvarId_965_, v_a_803_);
lean_dec(v_fvarId_965_);
lean_dec(v_fvarId_959_);
if (v___x_973_ == 0)
{
lean_dec_ref(v_k_970_);
lean_dec_ref(v_k_964_);
lean_dec(v_a_803_);
return v___x_973_;
}
else
{
v_code_u2081_801_ = v_k_964_;
v_code_u2082_802_ = v_k_970_;
goto _start;
}
}
}
v___jp_975_:
{
if (v_persistent_968_ == 0)
{
if (v_persistent_962_ == 0)
{
goto v___jp_971_;
}
else
{
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec_ref(v_k_964_);
lean_dec(v_objs_x3f_963_);
lean_dec(v_fvarId_959_);
lean_dec(v_a_803_);
return v_persistent_968_;
}
}
else
{
if (v_persistent_962_ == 0)
{
lean_dec_ref(v_k_970_);
lean_dec(v_objs_x3f_969_);
lean_dec(v_fvarId_965_);
lean_dec_ref(v_k_964_);
lean_dec(v_objs_x3f_963_);
lean_dec(v_fvarId_959_);
lean_dec(v_a_803_);
return v_persistent_962_;
}
else
{
goto v___jp_971_;
}
}
}
}
else
{
uint8_t v___x_977_; 
lean_dec_ref_known(v_code_u2081_801_, 4);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_977_ = 0;
return v___x_977_;
}
}
default: 
{
if (lean_obj_tag(v_code_u2082_802_) == 13)
{
lean_object* v_fvarId_978_; lean_object* v_k_979_; lean_object* v_fvarId_980_; lean_object* v_k_981_; uint8_t v___x_982_; 
v_fvarId_978_ = lean_ctor_get(v_code_u2081_801_, 0);
lean_inc(v_fvarId_978_);
v_k_979_ = lean_ctor_get(v_code_u2081_801_, 1);
lean_inc_ref(v_k_979_);
lean_dec_ref_known(v_code_u2081_801_, 2);
v_fvarId_980_ = lean_ctor_get(v_code_u2082_802_, 0);
lean_inc(v_fvarId_980_);
v_k_981_ = lean_ctor_get(v_code_u2082_802_, 1);
lean_inc_ref(v_k_981_);
lean_dec_ref_known(v_code_u2082_802_, 2);
v___x_982_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_978_, v_fvarId_980_, v_a_803_);
lean_dec(v_fvarId_980_);
lean_dec(v_fvarId_978_);
if (v___x_982_ == 0)
{
lean_dec_ref(v_k_981_);
lean_dec_ref(v_k_979_);
lean_dec(v_a_803_);
return v___x_982_;
}
else
{
v_code_u2081_801_ = v_k_979_;
v_code_u2082_802_ = v_k_981_;
goto _start;
}
}
else
{
uint8_t v___x_984_; 
lean_dec_ref_known(v_code_u2081_801_, 2);
lean_dec(v_a_803_);
lean_dec_ref(v_code_u2082_802_);
v___x_984_ = 0;
return v___x_984_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(uint8_t v_pu_985_, lean_object* v_code_986_, lean_object* v_code_987_, lean_object* v_params_u2081_988_, lean_object* v_params_u2082_989_, lean_object* v_i_990_, lean_object* v_a_991_){
_start:
{
lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_992_ = lean_array_get_size(v_params_u2081_988_);
v___x_993_ = lean_nat_dec_lt(v_i_990_, v___x_992_);
if (v___x_993_ == 0)
{
uint8_t v___x_994_; 
lean_dec(v_i_990_);
v___x_994_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_985_, v_code_986_, v_code_987_, v_a_991_);
return v___x_994_;
}
else
{
lean_object* v_p_u2081_995_; lean_object* v_fvarId_996_; lean_object* v_type_997_; lean_object* v_p_u2082_998_; lean_object* v_fvarId_999_; lean_object* v_type_1000_; uint8_t v___x_1001_; 
v_p_u2081_995_ = lean_array_fget_borrowed(v_params_u2081_988_, v_i_990_);
v_fvarId_996_ = lean_ctor_get(v_p_u2081_995_, 0);
v_type_997_ = lean_ctor_get(v_p_u2081_995_, 2);
v_p_u2082_998_ = lean_array_fget_borrowed(v_params_u2082_989_, v_i_990_);
v_fvarId_999_ = lean_ctor_get(v_p_u2082_998_, 0);
v_type_1000_ = lean_ctor_get(v_p_u2082_998_, 2);
v___x_1001_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_997_, v_type_1000_, v_a_991_);
if (v___x_1001_ == 0)
{
lean_dec(v_a_991_);
lean_dec(v_i_990_);
lean_dec_ref(v_code_987_);
lean_dec_ref(v_code_986_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v_i_990_, v___x_1002_);
lean_dec(v_i_990_);
lean_inc(v_fvarId_996_);
lean_inc(v_fvarId_999_);
v___x_1004_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_999_, v_fvarId_996_, v_a_991_);
v_i_990_ = v___x_1003_;
v_a_991_ = v___x_1004_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg___boxed(lean_object* v_pu_1006_, lean_object* v_code_1007_, lean_object* v_code_1008_, lean_object* v_params_u2081_1009_, lean_object* v_params_u2082_1010_, lean_object* v_i_1011_, lean_object* v_a_1012_){
_start:
{
uint8_t v_pu_boxed_1013_; uint8_t v_res_1014_; lean_object* v_r_1015_; 
v_pu_boxed_1013_ = lean_unbox(v_pu_1006_);
v_res_1014_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_boxed_1013_, v_code_1007_, v_code_1008_, v_params_u2081_1009_, v_params_u2082_1010_, v_i_1011_, v_a_1012_);
lean_dec_ref(v_params_u2082_1010_);
lean_dec_ref(v_params_u2081_1009_);
v_r_1015_ = lean_box(v_res_1014_);
return v_r_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts___boxed(lean_object* v_pu_1016_, lean_object* v_alts_u2081_1017_, lean_object* v_alts_u2082_1018_, lean_object* v_a_1019_){
_start:
{
uint8_t v_pu_boxed_1020_; uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_pu_boxed_1020_ = lean_unbox(v_pu_1016_);
v_res_1021_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_boxed_1020_, v_alts_u2081_1017_, v_alts_u2082_1018_, v_a_1019_);
lean_dec(v_a_1019_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___boxed(lean_object* v_pu_1023_, lean_object* v_as_1024_, lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_){
_start:
{
uint8_t v_pu_boxed_1029_; size_t v_sz_boxed_1030_; size_t v_i_boxed_1031_; lean_object* v_res_1032_; 
v_pu_boxed_1029_ = lean_unbox(v_pu_1023_);
v_sz_boxed_1030_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1031_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_boxed_1029_, v_as_1024_, v_sz_boxed_1030_, v_i_boxed_1031_, v_b_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v_as_1024_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqv___boxed(lean_object* v_pu_1033_, lean_object* v_code_u2081_1034_, lean_object* v_code_u2082_1035_, lean_object* v_a_1036_){
_start:
{
uint8_t v_pu_boxed_1037_; uint8_t v_res_1038_; lean_object* v_r_1039_; 
v_pu_boxed_1037_ = lean_unbox(v_pu_1033_);
v_res_1038_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_boxed_1037_, v_code_u2081_1034_, v_code_u2082_1035_, v_a_1036_);
v_r_1039_ = lean_box(v_res_1038_);
return v_r_1039_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(uint8_t v_pu_1040_, lean_object* v_code_1041_, lean_object* v_code_1042_, uint8_t v_pu_1043_, lean_object* v_params_u2081_1044_, lean_object* v_params_u2082_1045_, lean_object* v_h_1046_, lean_object* v_i_1047_, lean_object* v_a_1048_){
_start:
{
uint8_t v___x_1049_; 
lean_inc(v_a_1048_);
v___x_1049_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_1040_, v_code_1041_, v_code_1042_, v_params_u2081_1044_, v_params_u2082_1045_, v_i_1047_, v_a_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___boxed(lean_object* v_pu_1050_, lean_object* v_code_1051_, lean_object* v_code_1052_, lean_object* v_pu_1053_, lean_object* v_params_u2081_1054_, lean_object* v_params_u2082_1055_, lean_object* v_h_1056_, lean_object* v_i_1057_, lean_object* v_a_1058_){
_start:
{
uint8_t v_pu_boxed_1059_; uint8_t v_pu_boxed_1060_; uint8_t v_res_1061_; lean_object* v_r_1062_; 
v_pu_boxed_1059_ = lean_unbox(v_pu_1050_);
v_pu_boxed_1060_ = lean_unbox(v_pu_1053_);
v_res_1061_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(v_pu_boxed_1059_, v_code_1051_, v_code_1052_, v_pu_boxed_1060_, v_params_u2081_1054_, v_params_u2082_1055_, v_h_1056_, v_i_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_params_u2082_1055_);
lean_dec_ref(v_params_u2081_1054_);
v_r_1062_ = lean_box(v_res_1061_);
return v_r_1062_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t v_pu_1063_, lean_object* v_c_u2081_1064_, lean_object* v_c_u2082_1065_){
_start:
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = lean_box(1);
v___x_1067_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_1063_, v_c_u2081_1064_, v_c_u2082_1065_, v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_alphaEqv___boxed(lean_object* v_pu_1068_, lean_object* v_c_u2081_1069_, lean_object* v_c_u2082_1070_){
_start:
{
uint8_t v_pu_boxed_1071_; uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_pu_boxed_1071_ = lean_unbox(v_pu_1068_);
v_res_1072_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v_pu_boxed_1071_, v_c_u2081_1069_, v_c_u2082_1070_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
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
