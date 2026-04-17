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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_dec_ref(v___x_18_);
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
lean_dec_ref(v_fst_129_);
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
lean_dec_ref(v_fst_235_);
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
lean_object* v_i_u2081_282_; lean_object* v_v_u2081_283_; lean_object* v_i_u2082_284_; lean_object* v_v_u2082_285_; lean_object* v___y_286_; lean_object* v_f_u2081_290_; lean_object* v_as_u2081_291_; lean_object* v_f_u2082_292_; lean_object* v_as_u2082_293_; lean_object* v___y_294_; 
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
lean_dec_ref(v_e_u2082_279_);
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
lean_dec_ref(v_e_u2082_279_);
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
lean_dec_ref(v_e_u2082_279_);
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
lean_dec_ref(v_e_u2082_279_);
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
lean_dec_ref(v_e_u2082_279_);
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
lean_dec_ref(v_e_u2082_279_);
v_i_u2081_282_ = v_i_341_;
v_v_u2081_283_ = v_var_342_;
v_i_u2082_284_ = v_i_343_;
v_v_u2082_285_ = v_var_344_;
v___y_286_ = v_a_280_;
goto v___jp_281_;
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
lean_dec_ref(v_e_u2082_279_);
v_i_u2081_282_ = v_i_346_;
v_v_u2081_283_ = v_var_347_;
v_i_u2082_284_ = v_i_348_;
v_v_u2082_285_ = v_var_349_;
v___y_286_ = v_a_280_;
goto v___jp_281_;
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
lean_object* v_n_351_; lean_object* v_offset_352_; lean_object* v_var_353_; lean_object* v_n_354_; lean_object* v_offset_355_; lean_object* v_var_356_; uint8_t v___y_358_; uint8_t v___x_360_; 
v_n_351_ = lean_ctor_get(v_e_u2081_278_, 0);
v_offset_352_ = lean_ctor_get(v_e_u2081_278_, 1);
v_var_353_ = lean_ctor_get(v_e_u2081_278_, 2);
v_n_354_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_n_354_);
v_offset_355_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_offset_355_);
v_var_356_ = lean_ctor_get(v_e_u2082_279_, 2);
lean_inc(v_var_356_);
lean_dec_ref(v_e_u2082_279_);
v___x_360_ = lean_nat_dec_eq(v_n_351_, v_n_354_);
lean_dec(v_n_354_);
if (v___x_360_ == 0)
{
lean_dec(v_offset_355_);
v___y_358_ = v___x_360_;
goto v___jp_357_;
}
else
{
uint8_t v___x_361_; 
v___x_361_ = lean_nat_dec_eq(v_offset_352_, v_offset_355_);
lean_dec(v_offset_355_);
v___y_358_ = v___x_361_;
goto v___jp_357_;
}
v___jp_357_:
{
if (v___y_358_ == 0)
{
lean_dec(v_var_356_);
return v___y_358_;
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
uint8_t v___x_362_; 
lean_dec(v_e_u2082_279_);
v___x_362_ = 0;
return v___x_362_;
}
}
case 9:
{
if (lean_obj_tag(v_e_u2082_279_) == 9)
{
lean_object* v_fn_363_; lean_object* v_args_364_; lean_object* v_fn_365_; lean_object* v_args_366_; 
v_fn_363_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_364_ = lean_ctor_get(v_e_u2081_278_, 1);
v_fn_365_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fn_365_);
v_args_366_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_366_);
lean_dec_ref(v_e_u2082_279_);
v_f_u2081_290_ = v_fn_363_;
v_as_u2081_291_ = v_args_364_;
v_f_u2082_292_ = v_fn_365_;
v_as_u2082_293_ = v_args_366_;
v___y_294_ = v_a_280_;
goto v___jp_289_;
}
else
{
uint8_t v___x_367_; 
lean_dec(v_e_u2082_279_);
v___x_367_ = 0;
return v___x_367_;
}
}
case 10:
{
if (lean_obj_tag(v_e_u2082_279_) == 10)
{
lean_object* v_fn_368_; lean_object* v_args_369_; lean_object* v_fn_370_; lean_object* v_args_371_; 
v_fn_368_ = lean_ctor_get(v_e_u2081_278_, 0);
v_args_369_ = lean_ctor_get(v_e_u2081_278_, 1);
v_fn_370_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fn_370_);
v_args_371_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_args_371_);
lean_dec_ref(v_e_u2082_279_);
v_f_u2081_290_ = v_fn_368_;
v_as_u2081_291_ = v_args_369_;
v_f_u2082_292_ = v_fn_370_;
v_as_u2082_293_ = v_args_371_;
v___y_294_ = v_a_280_;
goto v___jp_289_;
}
else
{
uint8_t v___x_372_; 
lean_dec(v_e_u2082_279_);
v___x_372_ = 0;
return v___x_372_;
}
}
case 11:
{
if (lean_obj_tag(v_e_u2082_279_) == 11)
{
lean_object* v_n_373_; lean_object* v_var_374_; lean_object* v_n_375_; lean_object* v_var_376_; 
v_n_373_ = lean_ctor_get(v_e_u2081_278_, 0);
v_var_374_ = lean_ctor_get(v_e_u2081_278_, 1);
v_n_375_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_n_375_);
v_var_376_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_var_376_);
lean_dec_ref(v_e_u2082_279_);
v_i_u2081_282_ = v_n_373_;
v_v_u2081_283_ = v_var_374_;
v_i_u2082_284_ = v_n_375_;
v_v_u2082_285_ = v_var_376_;
v___y_286_ = v_a_280_;
goto v___jp_281_;
}
else
{
uint8_t v___x_377_; 
lean_dec(v_e_u2082_279_);
v___x_377_ = 0;
return v___x_377_;
}
}
case 12:
{
if (lean_obj_tag(v_e_u2082_279_) == 12)
{
lean_object* v_var_378_; lean_object* v_i_379_; uint8_t v_updateHeader_380_; lean_object* v_args_381_; lean_object* v_var_382_; lean_object* v_i_383_; uint8_t v_updateHeader_384_; lean_object* v_args_385_; uint8_t v___y_387_; uint8_t v___x_390_; 
v_var_378_ = lean_ctor_get(v_e_u2081_278_, 0);
v_i_379_ = lean_ctor_get(v_e_u2081_278_, 1);
v_updateHeader_380_ = lean_ctor_get_uint8(v_e_u2081_278_, sizeof(void*)*3);
v_args_381_ = lean_ctor_get(v_e_u2081_278_, 2);
v_var_382_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_var_382_);
v_i_383_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc_ref(v_i_383_);
v_updateHeader_384_ = lean_ctor_get_uint8(v_e_u2082_279_, sizeof(void*)*3);
v_args_385_ = lean_ctor_get(v_e_u2082_279_, 2);
lean_inc_ref(v_args_385_);
lean_dec_ref(v_e_u2082_279_);
v___x_390_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_i_379_, v_i_383_);
lean_dec_ref(v_i_383_);
if (v___x_390_ == 0)
{
v___y_387_ = v___x_390_;
goto v___jp_386_;
}
else
{
if (v_updateHeader_380_ == 0)
{
if (v_updateHeader_384_ == 0)
{
v___y_387_ = v___x_390_;
goto v___jp_386_;
}
else
{
lean_dec_ref(v_args_385_);
lean_dec(v_var_382_);
return v_updateHeader_380_;
}
}
else
{
v___y_387_ = v_updateHeader_384_;
goto v___jp_386_;
}
}
v___jp_386_:
{
if (v___y_387_ == 0)
{
lean_dec_ref(v_args_385_);
lean_dec(v_var_382_);
return v___y_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_var_378_, v_var_382_, v_a_280_);
lean_dec(v_var_382_);
if (v___x_388_ == 0)
{
lean_dec_ref(v_args_385_);
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_args_381_, v_args_385_, v_a_280_);
return v___x_389_;
}
}
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
case 13:
{
if (lean_obj_tag(v_e_u2082_279_) == 13)
{
lean_object* v_ty_392_; lean_object* v_fvarId_393_; lean_object* v_ty_394_; lean_object* v_fvarId_395_; uint8_t v___x_396_; 
v_ty_392_ = lean_ctor_get(v_e_u2081_278_, 0);
v_fvarId_393_ = lean_ctor_get(v_e_u2081_278_, 1);
v_ty_394_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc_ref(v_ty_394_);
v_fvarId_395_ = lean_ctor_get(v_e_u2082_279_, 1);
lean_inc(v_fvarId_395_);
lean_dec_ref(v_e_u2082_279_);
v___x_396_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_392_, v_ty_394_, v_a_280_);
lean_dec_ref(v_ty_394_);
if (v___x_396_ == 0)
{
lean_dec(v_fvarId_395_);
return v___x_396_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_393_, v_fvarId_395_, v_a_280_);
lean_dec(v_fvarId_395_);
return v___x_397_;
}
}
else
{
uint8_t v___x_398_; 
lean_dec(v_e_u2082_279_);
v___x_398_ = 0;
return v___x_398_;
}
}
case 14:
{
if (lean_obj_tag(v_e_u2082_279_) == 14)
{
lean_object* v_fvarId_399_; lean_object* v_fvarId_400_; uint8_t v___x_401_; 
v_fvarId_399_ = lean_ctor_get(v_e_u2081_278_, 0);
v_fvarId_400_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fvarId_400_);
lean_dec_ref(v_e_u2082_279_);
v___x_401_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_399_, v_fvarId_400_, v_a_280_);
lean_dec(v_fvarId_400_);
return v___x_401_;
}
else
{
uint8_t v___x_402_; 
lean_dec(v_e_u2082_279_);
v___x_402_ = 0;
return v___x_402_;
}
}
default: 
{
if (lean_obj_tag(v_e_u2082_279_) == 15)
{
lean_object* v_fvarId_403_; lean_object* v_fvarId_404_; uint8_t v___x_405_; 
v_fvarId_403_ = lean_ctor_get(v_e_u2081_278_, 0);
v_fvarId_404_ = lean_ctor_get(v_e_u2082_279_, 0);
lean_inc(v_fvarId_404_);
lean_dec_ref(v_e_u2082_279_);
v___x_405_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_403_, v_fvarId_404_, v_a_280_);
lean_dec(v_fvarId_404_);
return v___x_405_;
}
else
{
uint8_t v___x_406_; 
lean_dec(v_e_u2082_279_);
v___x_406_ = 0;
return v___x_406_;
}
}
}
v___jp_281_:
{
uint8_t v___x_287_; 
v___x_287_ = lean_nat_dec_eq(v_i_u2081_282_, v_i_u2082_284_);
lean_dec(v_i_u2082_284_);
if (v___x_287_ == 0)
{
lean_dec(v_v_u2082_285_);
return v___x_287_;
}
else
{
uint8_t v___x_288_; 
v___x_288_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_v_u2081_283_, v_v_u2082_285_, v___y_286_);
lean_dec(v_v_u2082_285_);
return v___x_288_;
}
}
v___jp_289_:
{
uint8_t v___x_295_; 
v___x_295_ = lean_name_eq(v_f_u2081_290_, v_f_u2082_292_);
lean_dec(v_f_u2082_292_);
if (v___x_295_ == 0)
{
lean_dec_ref(v_as_u2082_293_);
return v___x_295_;
}
else
{
uint8_t v___x_296_; 
v___x_296_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_277_, v_as_u2081_291_, v_as_u2082_293_, v___y_294_);
return v___x_296_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue___boxed(lean_object* v_pu_407_, lean_object* v_e_u2081_408_, lean_object* v_e_u2082_409_, lean_object* v_a_410_){
_start:
{
uint8_t v_pu_boxed_411_; uint8_t v_res_412_; lean_object* v_r_413_; 
v_pu_boxed_411_ = lean_unbox(v_pu_407_);
v_res_412_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_boxed_411_, v_e_u2081_408_, v_e_u2082_409_, v_a_410_);
lean_dec(v_a_410_);
lean_dec(v_e_u2081_408_);
v_r_413_ = lean_box(v_res_412_);
return v_r_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(lean_object* v_fvarId_u2081_414_, lean_object* v_fvarId_u2082_415_, lean_object* v_x_416_, lean_object* v_a_417_){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_inc(v_a_417_);
v___x_418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_415_, v_fvarId_u2081_414_, v_a_417_);
v___x_419_ = lean_apply_1(v_x_416_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg___boxed(lean_object* v_fvarId_u2081_420_, lean_object* v_fvarId_u2082_421_, lean_object* v_x_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar___redArg(v_fvarId_u2081_420_, v_fvarId_u2082_421_, v_x_422_, v_a_423_);
lean_dec(v_a_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar(lean_object* v_00_u03b1_425_, lean_object* v_fvarId_u2081_426_, lean_object* v_fvarId_u2082_427_, lean_object* v_x_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_inc(v_a_429_);
v___x_430_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_u2082_427_, v_fvarId_u2081_426_, v_a_429_);
v___x_431_ = lean_apply_1(v_x_428_, v___x_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar___boxed(lean_object* v_00_u03b1_432_, lean_object* v_fvarId_u2081_433_, lean_object* v_fvarId_u2082_434_, lean_object* v_x_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Lean_Compiler_LCNF_AlphaEqv_withFVar(v_00_u03b1_432_, v_fvarId_u2081_433_, v_fvarId_u2082_434_, v_x_435_, v_a_436_);
lean_dec(v_a_436_);
return v_res_437_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(lean_object* v_params_u2081_438_, lean_object* v_params_u2082_439_, lean_object* v_x_440_, lean_object* v_i_441_, lean_object* v_a_442_){
_start:
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = lean_array_get_size(v_params_u2081_438_);
v___x_444_ = lean_nat_dec_lt(v_i_441_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; uint8_t v___x_446_; 
lean_dec(v_i_441_);
v___x_445_ = lean_apply_1(v_x_440_, v_a_442_);
v___x_446_ = lean_unbox(v___x_445_);
return v___x_446_;
}
else
{
lean_object* v_p_u2081_447_; lean_object* v_fvarId_448_; lean_object* v_type_449_; lean_object* v_p_u2082_450_; lean_object* v_fvarId_451_; lean_object* v_type_452_; uint8_t v___x_453_; 
v_p_u2081_447_ = lean_array_fget_borrowed(v_params_u2081_438_, v_i_441_);
v_fvarId_448_ = lean_ctor_get(v_p_u2081_447_, 0);
v_type_449_ = lean_ctor_get(v_p_u2081_447_, 2);
v_p_u2082_450_ = lean_array_fget_borrowed(v_params_u2082_439_, v_i_441_);
v_fvarId_451_ = lean_ctor_get(v_p_u2082_450_, 0);
v_type_452_ = lean_ctor_get(v_p_u2082_450_, 2);
v___x_453_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_449_, v_type_452_, v_a_442_);
if (v___x_453_ == 0)
{
lean_dec(v_a_442_);
lean_dec(v_i_441_);
lean_dec_ref(v_x_440_);
return v___x_453_;
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_add(v_i_441_, v___x_454_);
lean_dec(v_i_441_);
lean_inc(v_fvarId_448_);
lean_inc(v_fvarId_451_);
v___x_456_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_451_, v_fvarId_448_, v_a_442_);
v_i_441_ = v___x_455_;
v_a_442_ = v___x_456_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg___boxed(lean_object* v_params_u2081_458_, lean_object* v_params_u2082_459_, lean_object* v_x_460_, lean_object* v_i_461_, lean_object* v_a_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_458_, v_params_u2082_459_, v_x_460_, v_i_461_, v_a_462_);
lean_dec_ref(v_params_u2082_459_);
lean_dec_ref(v_params_u2081_458_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(uint8_t v_pu_465_, lean_object* v_params_u2081_466_, lean_object* v_params_u2082_467_, lean_object* v_x_468_, lean_object* v_h_469_, lean_object* v_i_470_, lean_object* v_a_471_){
_start:
{
uint8_t v___x_472_; 
lean_inc(v_a_471_);
v___x_472_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_466_, v_params_u2082_467_, v_x_468_, v_i_470_, v_a_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___boxed(lean_object* v_pu_473_, lean_object* v_params_u2081_474_, lean_object* v_params_u2082_475_, lean_object* v_x_476_, lean_object* v_h_477_, lean_object* v_i_478_, lean_object* v_a_479_){
_start:
{
uint8_t v_pu_boxed_480_; uint8_t v_res_481_; lean_object* v_r_482_; 
v_pu_boxed_480_ = lean_unbox(v_pu_473_);
v_res_481_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(v_pu_boxed_480_, v_params_u2081_474_, v_params_u2082_475_, v_x_476_, v_h_477_, v_i_478_, v_a_479_);
lean_dec(v_a_479_);
lean_dec_ref(v_params_u2082_475_);
lean_dec_ref(v_params_u2081_474_);
v_r_482_ = lean_box(v_res_481_);
return v_r_482_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(lean_object* v_params_u2081_483_, lean_object* v_params_u2082_484_, lean_object* v_x_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v___x_487_ = lean_array_get_size(v_params_u2082_484_);
v___x_488_ = lean_array_get_size(v_params_u2081_483_);
v___x_489_ = lean_nat_dec_eq(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
lean_dec_ref(v_x_485_);
return v___x_489_;
}
else
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_486_);
v___x_491_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_483_, v_params_u2082_484_, v_x_485_, v___x_490_, v_a_486_);
return v___x_491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg___boxed(lean_object* v_params_u2081_492_, lean_object* v_params_u2082_493_, lean_object* v_x_494_, lean_object* v_a_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(v_params_u2081_492_, v_params_u2082_493_, v_x_494_, v_a_495_);
lean_dec(v_a_495_);
lean_dec_ref(v_params_u2082_493_);
lean_dec_ref(v_params_u2081_492_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams(uint8_t v_pu_498_, lean_object* v_params_u2081_499_, lean_object* v_params_u2082_500_, lean_object* v_x_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_503_ = lean_array_get_size(v_params_u2082_500_);
v___x_504_ = lean_array_get_size(v_params_u2081_499_);
v___x_505_ = lean_nat_dec_eq(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_dec_ref(v_x_501_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_506_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_502_);
v___x_507_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_499_, v_params_u2082_500_, v_x_501_, v___x_506_, v_a_502_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___boxed(lean_object* v_pu_508_, lean_object* v_params_u2081_509_, lean_object* v_params_u2082_510_, lean_object* v_x_511_, lean_object* v_a_512_){
_start:
{
uint8_t v_pu_boxed_513_; uint8_t v_res_514_; lean_object* v_r_515_; 
v_pu_boxed_513_ = lean_unbox(v_pu_508_);
v_res_514_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams(v_pu_boxed_513_, v_params_u2081_509_, v_params_u2082_510_, v_x_511_, v_a_512_);
lean_dec(v_a_512_);
lean_dec_ref(v_params_u2082_510_);
lean_dec_ref(v_params_u2081_509_);
v_r_515_ = lean_box(v_res_514_);
return v_r_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(lean_object* v_hi_516_, lean_object* v_pivot_517_, lean_object* v_as_518_, lean_object* v_i_519_, lean_object* v_k_520_){
_start:
{
uint8_t v___y_532_; uint8_t v___x_533_; 
v___x_533_ = lean_nat_dec_lt(v_k_520_, v_hi_516_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v_k_520_);
v___x_534_ = lean_array_fswap(v_as_518_, v_i_519_, v_hi_516_);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_i_519_);
lean_ctor_set(v___x_535_, 1, v___x_534_);
return v___x_535_;
}
else
{
lean_object* v___x_536_; 
v___x_536_ = lean_array_fget_borrowed(v_as_518_, v_k_520_);
switch(lean_obj_tag(v___x_536_))
{
case 0:
{
switch(lean_obj_tag(v_pivot_517_))
{
case 2:
{
goto v___jp_525_;
}
case 0:
{
lean_object* v_ctorName_537_; lean_object* v_ctorName_538_; uint8_t v___x_539_; 
v_ctorName_537_ = lean_ctor_get(v___x_536_, 0);
v_ctorName_538_ = lean_ctor_get(v_pivot_517_, 0);
v___x_539_ = l_Lean_Name_lt(v_ctorName_537_, v_ctorName_538_);
v___y_532_ = v___x_539_;
goto v___jp_531_;
}
default: 
{
goto v___jp_521_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_pivot_517_))
{
case 2:
{
goto v___jp_525_;
}
case 1:
{
lean_object* v_info_540_; lean_object* v_info_541_; lean_object* v_name_542_; lean_object* v_name_543_; uint8_t v___x_544_; 
v_info_540_ = lean_ctor_get(v___x_536_, 0);
v_info_541_ = lean_ctor_get(v_pivot_517_, 0);
v_name_542_ = lean_ctor_get(v_info_540_, 0);
v_name_543_ = lean_ctor_get(v_info_541_, 0);
v___x_544_ = l_Lean_Name_lt(v_name_542_, v_name_543_);
v___y_532_ = v___x_544_;
goto v___jp_531_;
}
default: 
{
goto v___jp_521_;
}
}
}
default: 
{
goto v___jp_521_;
}
}
}
v___jp_521_:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(1u);
v___x_523_ = lean_nat_add(v_k_520_, v___x_522_);
lean_dec(v_k_520_);
v_k_520_ = v___x_523_;
goto _start;
}
v___jp_525_:
{
lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
v___x_526_ = lean_array_fswap(v_as_518_, v_i_519_, v_k_520_);
v___x_527_ = lean_unsigned_to_nat(1u);
v___x_528_ = lean_nat_add(v_i_519_, v___x_527_);
lean_dec(v_i_519_);
v___x_529_ = lean_nat_add(v_k_520_, v___x_527_);
lean_dec(v_k_520_);
v_as_518_ = v___x_526_;
v_i_519_ = v___x_528_;
v_k_520_ = v___x_529_;
goto _start;
}
v___jp_531_:
{
if (v___y_532_ == 0)
{
goto v___jp_521_;
}
else
{
goto v___jp_525_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg___boxed(lean_object* v_hi_545_, lean_object* v_pivot_546_, lean_object* v_as_547_, lean_object* v_i_548_, lean_object* v_k_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_545_, v_pivot_546_, v_as_547_, v_i_548_, v_k_549_);
lean_dec_ref(v_pivot_546_);
lean_dec(v_hi_545_);
return v_res_550_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(uint8_t v___x_551_, lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
switch(lean_obj_tag(v_x_552_))
{
case 0:
{
switch(lean_obj_tag(v_x_553_))
{
case 2:
{
return v___x_551_;
}
case 0:
{
lean_object* v_ctorName_554_; lean_object* v_ctorName_555_; uint8_t v___x_556_; 
v_ctorName_554_ = lean_ctor_get(v_x_552_, 0);
v_ctorName_555_ = lean_ctor_get(v_x_553_, 0);
v___x_556_ = l_Lean_Name_lt(v_ctorName_554_, v_ctorName_555_);
return v___x_556_;
}
default: 
{
uint8_t v___x_557_; 
v___x_557_ = 0;
return v___x_557_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_553_))
{
case 2:
{
return v___x_551_;
}
case 1:
{
lean_object* v_info_558_; lean_object* v_info_559_; lean_object* v_name_560_; lean_object* v_name_561_; uint8_t v___x_562_; 
v_info_558_ = lean_ctor_get(v_x_552_, 0);
v_info_559_ = lean_ctor_get(v_x_553_, 0);
v_name_560_ = lean_ctor_get(v_info_558_, 0);
v_name_561_ = lean_ctor_get(v_info_559_, 0);
v___x_562_ = l_Lean_Name_lt(v_name_560_, v_name_561_);
return v___x_562_;
}
default: 
{
uint8_t v___x_563_; 
v___x_563_ = 0;
return v___x_563_;
}
}
}
default: 
{
uint8_t v___x_564_; 
v___x_564_ = 0;
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed(lean_object* v___x_565_, lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint8_t v___x_429__boxed_568_; uint8_t v_res_569_; lean_object* v_r_570_; 
v___x_429__boxed_568_ = lean_unbox(v___x_565_);
v_res_569_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_429__boxed_568_, v_x_566_, v_x_567_);
lean_dec_ref(v_x_567_);
lean_dec_ref(v_x_566_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(lean_object* v_n_571_, lean_object* v_as_572_, lean_object* v_lo_573_, lean_object* v_hi_574_){
_start:
{
lean_object* v___y_576_; uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_lt(v_lo_573_, v_hi_574_);
if (v___x_586_ == 0)
{
lean_dec(v_lo_573_);
return v_as_572_;
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v_mid_589_; lean_object* v___y_591_; lean_object* v___y_597_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_587_ = lean_nat_add(v_lo_573_, v_hi_574_);
v___x_588_ = lean_unsigned_to_nat(1u);
v_mid_589_ = lean_nat_shiftr(v___x_587_, v___x_588_);
lean_dec(v___x_587_);
v___x_602_ = lean_array_fget_borrowed(v_as_572_, v_mid_589_);
v___x_603_ = lean_array_fget_borrowed(v_as_572_, v_lo_573_);
v___x_604_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_586_, v___x_602_, v___x_603_);
if (v___x_604_ == 0)
{
v___y_597_ = v_as_572_;
goto v___jp_596_;
}
else
{
lean_object* v___x_605_; 
v___x_605_ = lean_array_fswap(v_as_572_, v_lo_573_, v_mid_589_);
v___y_597_ = v___x_605_;
goto v___jp_596_;
}
v___jp_590_:
{
lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_592_ = lean_array_fget_borrowed(v___y_591_, v_mid_589_);
v___x_593_ = lean_array_fget_borrowed(v___y_591_, v_hi_574_);
v___x_594_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_586_, v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v_mid_589_);
v___y_576_ = v___y_591_;
goto v___jp_575_;
}
else
{
lean_object* v___x_595_; 
v___x_595_ = lean_array_fswap(v___y_591_, v_mid_589_, v_hi_574_);
lean_dec(v_mid_589_);
v___y_576_ = v___x_595_;
goto v___jp_575_;
}
}
v___jp_596_:
{
lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v___x_598_ = lean_array_fget_borrowed(v___y_597_, v_hi_574_);
v___x_599_ = lean_array_fget_borrowed(v___y_597_, v_lo_573_);
v___x_600_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_586_, v___x_598_, v___x_599_);
if (v___x_600_ == 0)
{
v___y_591_ = v___y_597_;
goto v___jp_590_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = lean_array_fswap(v___y_597_, v_lo_573_, v_hi_574_);
v___y_591_ = v___x_601_;
goto v___jp_590_;
}
}
}
v___jp_575_:
{
lean_object* v_pivot_577_; lean_object* v___x_578_; lean_object* v_fst_579_; lean_object* v_snd_580_; uint8_t v___x_581_; 
v_pivot_577_ = lean_array_fget(v___y_576_, v_hi_574_);
lean_inc_n(v_lo_573_, 2);
v___x_578_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_574_, v_pivot_577_, v___y_576_, v_lo_573_, v_lo_573_);
lean_dec(v_pivot_577_);
v_fst_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_fst_579_);
v_snd_580_ = lean_ctor_get(v___x_578_, 1);
lean_inc(v_snd_580_);
lean_dec_ref(v___x_578_);
v___x_581_ = lean_nat_dec_le(v_hi_574_, v_fst_579_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_571_, v_snd_580_, v_lo_573_, v_fst_579_);
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_fst_579_, v___x_583_);
lean_dec(v_fst_579_);
v_as_572_ = v___x_582_;
v_lo_573_ = v___x_584_;
goto _start;
}
else
{
lean_dec(v_fst_579_);
lean_dec(v_lo_573_);
return v_snd_580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___boxed(lean_object* v_n_606_, lean_object* v_as_607_, lean_object* v_lo_608_, lean_object* v_hi_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_606_, v_as_607_, v_lo_608_, v_hi_609_);
lean_dec(v_hi_609_);
lean_dec(v_n_606_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(lean_object* v_alts_611_){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_612_ = lean_array_get_size(v_alts_611_);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_nat_dec_eq(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___y_618_; uint8_t v___x_622_; 
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_sub(v___x_612_, v___x_615_);
v___x_622_ = lean_nat_dec_le(v___x_613_, v___x_616_);
if (v___x_622_ == 0)
{
lean_inc(v___x_616_);
v___y_618_ = v___x_616_;
goto v___jp_617_;
}
else
{
v___y_618_ = v___x_613_;
goto v___jp_617_;
}
v___jp_617_:
{
uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_le(v___y_618_, v___x_616_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; 
lean_dec(v___x_616_);
lean_inc(v___y_618_);
v___x_620_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_612_, v_alts_611_, v___y_618_, v___y_618_);
lean_dec(v___y_618_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; 
v___x_621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v___x_612_, v_alts_611_, v___y_618_, v___x_616_);
lean_dec(v___x_616_);
return v___x_621_;
}
}
}
else
{
return v_alts_611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(uint8_t v_pu_623_, lean_object* v_alts_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___boxed(lean_object* v_pu_626_, lean_object* v_alts_627_){
_start:
{
uint8_t v_pu_boxed_628_; lean_object* v_res_629_; 
v_pu_boxed_628_ = lean_unbox(v_pu_626_);
v_res_629_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(v_pu_boxed_628_, v_alts_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(lean_object* v_n_630_, lean_object* v_as_631_, lean_object* v_lo_632_, lean_object* v_hi_633_, lean_object* v_w_634_, lean_object* v_hlo_635_, lean_object* v_hhi_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_n_630_, v_as_631_, v_lo_632_, v_hi_633_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___boxed(lean_object* v_n_638_, lean_object* v_as_639_, lean_object* v_lo_640_, lean_object* v_hi_641_, lean_object* v_w_642_, lean_object* v_hlo_643_, lean_object* v_hhi_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(v_n_638_, v_as_639_, v_lo_640_, v_hi_641_, v_w_642_, v_hlo_643_, v_hhi_644_);
lean_dec(v_hi_641_);
lean_dec(v_n_638_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(lean_object* v_n_646_, lean_object* v_lo_647_, lean_object* v_hi_648_, lean_object* v_hhi_649_, lean_object* v_pivot_650_, lean_object* v_as_651_, lean_object* v_i_652_, lean_object* v_k_653_, lean_object* v_ilo_654_, lean_object* v_ik_655_, lean_object* v_w_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___redArg(v_hi_648_, v_pivot_650_, v_as_651_, v_i_652_, v_k_653_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0___boxed(lean_object* v_n_658_, lean_object* v_lo_659_, lean_object* v_hi_660_, lean_object* v_hhi_661_, lean_object* v_pivot_662_, lean_object* v_as_663_, lean_object* v_i_664_, lean_object* v_k_665_, lean_object* v_ilo_666_, lean_object* v_ik_667_, lean_object* v_w_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0_spec__0(v_n_658_, v_lo_659_, v_hi_660_, v_hhi_661_, v_pivot_662_, v_as_663_, v_i_664_, v_k_665_, v_ilo_666_, v_ik_667_, v_w_668_);
lean_dec_ref(v_pivot_662_);
lean_dec(v_hi_660_);
lean_dec(v_lo_659_);
lean_dec(v_n_658_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(uint8_t v_pu_673_, lean_object* v_as_674_, size_t v_sz_675_, size_t v_i_676_, lean_object* v_b_677_, lean_object* v___y_678_){
_start:
{
lean_object* v_a_680_; uint8_t v___x_684_; 
v___x_684_ = lean_usize_dec_lt(v_i_676_, v_sz_675_);
if (v___x_684_ == 0)
{
return v_b_677_;
}
else
{
lean_object* v_snd_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_773_; 
v_snd_685_ = lean_ctor_get(v_b_677_, 1);
v_isSharedCheck_773_ = !lean_is_exclusive(v_b_677_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; 
v_unused_774_ = lean_ctor_get(v_b_677_, 0);
lean_dec(v_unused_774_);
v___x_687_ = v_b_677_;
v_isShared_688_ = v_isSharedCheck_773_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_snd_685_);
lean_dec(v_b_677_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_773_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_array_689_; lean_object* v_start_690_; lean_object* v_stop_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_array_689_ = lean_ctor_get(v_snd_685_, 0);
v_start_690_ = lean_ctor_get(v_snd_685_, 1);
v_stop_691_ = lean_ctor_get(v_snd_685_, 2);
v___x_692_ = lean_box(0);
v___x_693_ = lean_nat_dec_lt(v_start_690_, v_stop_691_);
if (v___x_693_ == 0)
{
lean_object* v___x_695_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_692_);
v___x_695_ = v___x_687_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_snd_685_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
else
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_769_; 
lean_inc(v_stop_691_);
lean_inc(v_start_690_);
lean_inc_ref(v_array_689_);
v_isSharedCheck_769_ = !lean_is_exclusive(v_snd_685_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; lean_object* v_unused_771_; lean_object* v_unused_772_; 
v_unused_770_ = lean_ctor_get(v_snd_685_, 2);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_snd_685_, 1);
lean_dec(v_unused_771_);
v_unused_772_ = lean_ctor_get(v_snd_685_, 0);
lean_dec(v_unused_772_);
v___x_698_ = v_snd_685_;
v_isShared_699_ = v_isSharedCheck_769_;
goto v_resetjp_697_;
}
else
{
lean_dec(v_snd_685_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_769_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v_a_700_ = lean_array_uget_borrowed(v_as_674_, v_i_676_);
v___x_701_ = lean_array_fget(v_array_689_, v_start_690_);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_add(v_start_690_, v___x_702_);
lean_dec(v_start_690_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_703_);
v___x_705_ = v___x_698_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_array_689_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v_stop_691_);
v___x_705_ = v_reuseFailAlloc_768_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
uint8_t v___y_707_; 
switch(lean_obj_tag(v_a_700_))
{
case 0:
{
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_ctorName_716_; lean_object* v_params_717_; lean_object* v_code_718_; lean_object* v_ctorName_719_; lean_object* v_params_720_; lean_object* v_code_721_; uint8_t v___x_722_; 
v_ctorName_716_ = lean_ctor_get(v_a_700_, 0);
v_params_717_ = lean_ctor_get(v_a_700_, 1);
v_code_718_ = lean_ctor_get(v_a_700_, 2);
v_ctorName_719_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_ctorName_719_);
v_params_720_ = lean_ctor_get(v___x_701_, 1);
lean_inc_ref(v_params_720_);
v_code_721_ = lean_ctor_get(v___x_701_, 2);
lean_inc_ref(v_code_721_);
lean_dec_ref(v___x_701_);
v___x_722_ = lean_name_eq(v_ctorName_716_, v_ctorName_719_);
lean_dec(v_ctorName_719_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
lean_dec_ref(v_code_721_);
lean_dec_ref(v_params_720_);
lean_del_object(v___x_687_);
v___x_723_ = lean_box(v___x_722_);
v___x_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v___x_724_);
lean_ctor_set(v___x_725_, 1, v___x_705_);
return v___x_725_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_726_ = lean_array_get_size(v_params_720_);
v___x_727_ = lean_array_get_size(v_params_717_);
v___x_728_ = lean_nat_dec_eq(v___x_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_dec_ref(v_code_721_);
lean_dec_ref(v_params_720_);
v___y_707_ = v___x_728_;
goto v___jp_706_;
}
else
{
lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_729_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_678_);
lean_inc_ref(v_code_718_);
v___x_730_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_673_, v_code_718_, v_code_721_, v_params_717_, v_params_720_, v___x_729_, v___y_678_);
lean_dec_ref(v_params_720_);
if (v___x_730_ == 0)
{
v___y_707_ = v___x_730_;
goto v___jp_706_;
}
else
{
lean_object* v___x_731_; 
lean_del_object(v___x_687_);
v___x_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_692_);
lean_ctor_set(v___x_731_, 1, v___x_705_);
v_a_680_ = v___x_731_;
goto v___jp_679_;
}
}
}
}
else
{
lean_dec(v___x_701_);
lean_del_object(v___x_687_);
goto v___jp_713_;
}
}
case 1:
{
lean_del_object(v___x_687_);
if (lean_obj_tag(v___x_701_) == 1)
{
lean_object* v_info_732_; lean_object* v_code_733_; lean_object* v_info_734_; lean_object* v_code_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_754_; 
v_info_732_ = lean_ctor_get(v_a_700_, 0);
v_code_733_ = lean_ctor_get(v_a_700_, 1);
v_info_734_ = lean_ctor_get(v___x_701_, 0);
v_code_735_ = lean_ctor_get(v___x_701_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_754_ == 0)
{
v___x_737_ = v___x_701_;
v_isShared_738_ = v_isSharedCheck_754_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_code_735_);
lean_inc(v_info_734_);
lean_dec(v___x_701_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_754_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
uint8_t v___x_739_; 
v___x_739_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_info_732_, v_info_734_);
lean_dec_ref(v_info_734_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
lean_dec_ref(v_code_735_);
v___x_740_ = lean_box(v___x_739_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 0);
lean_ctor_set(v___x_737_, 1, v___x_705_);
lean_ctor_set(v___x_737_, 0, v___x_741_);
v___x_743_ = v___x_737_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v___x_705_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
else
{
uint8_t v___x_745_; 
lean_inc(v___y_678_);
lean_inc_ref(v_code_733_);
v___x_745_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_673_, v_code_733_, v_code_735_, v___y_678_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = lean_box(v___x_745_);
v___x_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 0);
lean_ctor_set(v___x_737_, 1, v___x_705_);
lean_ctor_set(v___x_737_, 0, v___x_747_);
v___x_749_ = v___x_737_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v___x_705_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
else
{
lean_object* v___x_752_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 0);
lean_ctor_set(v___x_737_, 1, v___x_705_);
lean_ctor_set(v___x_737_, 0, v___x_692_);
v___x_752_ = v___x_737_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_705_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
v_a_680_ = v___x_752_;
goto v___jp_679_;
}
}
}
}
}
else
{
lean_dec(v___x_701_);
goto v___jp_713_;
}
}
default: 
{
lean_del_object(v___x_687_);
if (lean_obj_tag(v___x_701_) == 2)
{
lean_object* v_code_755_; lean_object* v_code_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_767_; 
v_code_755_ = lean_ctor_get(v_a_700_, 0);
v_code_756_ = lean_ctor_get(v___x_701_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_767_ == 0)
{
v___x_758_ = v___x_701_;
v_isShared_759_ = v_isSharedCheck_767_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_code_756_);
lean_dec(v___x_701_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_767_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
uint8_t v___x_760_; 
lean_inc(v___y_678_);
lean_inc_ref(v_code_755_);
v___x_760_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_673_, v_code_755_, v_code_756_, v___y_678_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_box(v___x_760_);
if (v_isShared_759_ == 0)
{
lean_ctor_set_tag(v___x_758_, 1);
lean_ctor_set(v___x_758_, 0, v___x_761_);
v___x_763_ = v___x_758_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_765_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; 
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_763_);
lean_ctor_set(v___x_764_, 1, v___x_705_);
return v___x_764_;
}
}
else
{
lean_object* v___x_766_; 
lean_del_object(v___x_758_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_692_);
lean_ctor_set(v___x_766_, 1, v___x_705_);
v_a_680_ = v___x_766_;
goto v___jp_679_;
}
}
}
else
{
lean_dec(v___x_701_);
goto v___jp_713_;
}
}
}
v___jp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_708_ = lean_box(v___y_707_);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v___x_708_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 1, v___x_705_);
lean_ctor_set(v___x_687_, 0, v___x_709_);
v___x_711_ = v___x_687_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v___x_705_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
v___jp_713_:
{
lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0));
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_705_);
return v___x_715_;
}
}
}
}
}
}
v___jp_679_:
{
size_t v___x_681_; size_t v___x_682_; 
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_676_, v___x_681_);
v_i_676_ = v___x_682_;
v_b_677_ = v_a_680_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(uint8_t v_pu_775_, lean_object* v_alts_u2081_776_, lean_object* v_alts_u2082_777_, lean_object* v_a_778_){
_start:
{
lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_779_ = lean_array_get_size(v_alts_u2081_776_);
v___x_780_ = lean_array_get_size(v_alts_u2082_777_);
v___x_781_ = lean_nat_dec_eq(v___x_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_dec_ref(v_alts_u2082_777_);
lean_dec_ref(v_alts_u2081_776_);
return v___x_781_;
}
else
{
lean_object* v_alts_u2081_782_; lean_object* v_alts_u2082_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; size_t v_sz_789_; size_t v___x_790_; lean_object* v___x_791_; lean_object* v_fst_792_; 
v_alts_u2081_782_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2081_776_);
v_alts_u2082_783_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2082_777_);
v___x_784_ = lean_unsigned_to_nat(0u);
v___x_785_ = lean_array_get_size(v_alts_u2082_783_);
v___x_786_ = l_Array_toSubarray___redArg(v_alts_u2082_783_, v___x_784_, v___x_785_);
v___x_787_ = lean_box(0);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v___x_786_);
v_sz_789_ = lean_array_size(v_alts_u2081_782_);
v___x_790_ = ((size_t)0ULL);
v___x_791_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_775_, v_alts_u2081_782_, v_sz_789_, v___x_790_, v___x_788_, v_a_778_);
lean_dec_ref(v_alts_u2081_782_);
v_fst_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_fst_792_);
lean_dec_ref(v___x_791_);
if (lean_obj_tag(v_fst_792_) == 0)
{
return v___x_781_;
}
else
{
lean_object* v_val_793_; uint8_t v___x_794_; 
v_val_793_ = lean_ctor_get(v_fst_792_, 0);
lean_inc(v_val_793_);
lean_dec_ref(v_fst_792_);
v___x_794_ = lean_unbox(v_val_793_);
lean_dec(v_val_793_);
return v___x_794_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqv(uint8_t v_pu_795_, lean_object* v_code_u2081_796_, lean_object* v_code_u2082_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; lean_object* v___y_804_; uint8_t v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; uint8_t v___y_814_; uint8_t v___y_815_; lean_object* v_fvarId_u2081_817_; lean_object* v_n_u2081_818_; uint8_t v_c_u2081_819_; uint8_t v_p_u2081_820_; lean_object* v_k_u2081_821_; lean_object* v_fvarId_u2082_822_; lean_object* v_n_u2082_823_; uint8_t v_c_u2082_824_; uint8_t v_p_u2082_825_; lean_object* v_k_u2082_826_; lean_object* v___y_827_; 
switch(lean_obj_tag(v_code_u2081_796_))
{
case 0:
{
if (lean_obj_tag(v_code_u2082_797_) == 0)
{
lean_object* v_decl_829_; lean_object* v_decl_830_; lean_object* v_k_831_; lean_object* v_k_832_; lean_object* v_fvarId_833_; lean_object* v_type_834_; lean_object* v_value_835_; lean_object* v_fvarId_836_; lean_object* v_type_837_; lean_object* v_value_838_; uint8_t v___x_839_; 
v_decl_829_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc_ref(v_decl_829_);
v_decl_830_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc_ref(v_decl_830_);
v_k_831_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc_ref(v_k_831_);
lean_dec_ref(v_code_u2081_796_);
v_k_832_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc_ref(v_k_832_);
lean_dec_ref(v_code_u2082_797_);
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
v___x_839_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_834_, v_type_837_, v_a_798_);
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
lean_dec(v_a_798_);
return v___x_839_;
}
else
{
uint8_t v___x_840_; 
v___x_840_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_795_, v_value_835_, v_value_838_, v_a_798_);
lean_dec(v_value_835_);
if (v___x_840_ == 0)
{
lean_dec(v_fvarId_836_);
lean_dec(v_fvarId_833_);
lean_dec_ref(v_k_832_);
lean_dec_ref(v_k_831_);
lean_dec(v_a_798_);
return v___x_840_;
}
else
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_836_, v_fvarId_833_, v_a_798_);
v_code_u2081_796_ = v_k_831_;
v_code_u2082_797_ = v_k_832_;
v_a_798_ = v___x_841_;
goto _start;
}
}
}
else
{
uint8_t v___x_843_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_843_ = 0;
return v___x_843_;
}
}
case 1:
{
if (lean_obj_tag(v_code_u2082_797_) == 1)
{
lean_object* v_decl_844_; lean_object* v_decl_845_; lean_object* v_k_846_; lean_object* v_k_847_; lean_object* v_fvarId_848_; lean_object* v_params_849_; lean_object* v_type_850_; lean_object* v_value_851_; lean_object* v_fvarId_852_; lean_object* v_params_853_; lean_object* v_type_854_; lean_object* v_value_855_; uint8_t v___x_856_; 
v_decl_844_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc_ref(v_decl_844_);
v_decl_845_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc_ref(v_decl_845_);
v_k_846_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc_ref(v_k_846_);
lean_dec_ref(v_code_u2081_796_);
v_k_847_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc_ref(v_k_847_);
lean_dec_ref(v_code_u2082_797_);
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
v___x_856_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_850_, v_type_854_, v_a_798_);
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
lean_dec(v_a_798_);
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
lean_dec(v_a_798_);
return v___x_859_;
}
else
{
lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_860_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_798_);
v___x_861_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_795_, v_value_851_, v_value_855_, v_params_849_, v_params_853_, v___x_860_, v_a_798_);
lean_dec_ref(v_params_853_);
lean_dec_ref(v_params_849_);
if (v___x_861_ == 0)
{
lean_dec(v_fvarId_852_);
lean_dec(v_fvarId_848_);
lean_dec_ref(v_k_847_);
lean_dec_ref(v_k_846_);
lean_dec(v_a_798_);
return v___x_861_;
}
else
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_852_, v_fvarId_848_, v_a_798_);
v_code_u2081_796_ = v_k_846_;
v_code_u2082_797_ = v_k_847_;
v_a_798_ = v___x_862_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_864_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_864_ = 0;
return v___x_864_;
}
}
case 2:
{
if (lean_obj_tag(v_code_u2082_797_) == 2)
{
lean_object* v_decl_865_; lean_object* v_decl_866_; lean_object* v_k_867_; lean_object* v_k_868_; lean_object* v_fvarId_869_; lean_object* v_params_870_; lean_object* v_type_871_; lean_object* v_value_872_; lean_object* v_fvarId_873_; lean_object* v_params_874_; lean_object* v_type_875_; lean_object* v_value_876_; uint8_t v___x_877_; 
v_decl_865_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc_ref(v_decl_865_);
v_decl_866_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc_ref(v_decl_866_);
v_k_867_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc_ref(v_k_867_);
lean_dec_ref(v_code_u2081_796_);
v_k_868_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc_ref(v_k_868_);
lean_dec_ref(v_code_u2082_797_);
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
v___x_877_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_871_, v_type_875_, v_a_798_);
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
lean_dec(v_a_798_);
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
lean_dec(v_a_798_);
return v___x_880_;
}
else
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_798_);
v___x_882_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_795_, v_value_872_, v_value_876_, v_params_870_, v_params_874_, v___x_881_, v_a_798_);
lean_dec_ref(v_params_874_);
lean_dec_ref(v_params_870_);
if (v___x_882_ == 0)
{
lean_dec(v_fvarId_873_);
lean_dec(v_fvarId_869_);
lean_dec_ref(v_k_868_);
lean_dec_ref(v_k_867_);
lean_dec(v_a_798_);
return v___x_882_;
}
else
{
lean_object* v___x_883_; 
v___x_883_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_873_, v_fvarId_869_, v_a_798_);
v_code_u2081_796_ = v_k_867_;
v_code_u2082_797_ = v_k_868_;
v_a_798_ = v___x_883_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_885_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_885_ = 0;
return v___x_885_;
}
}
case 3:
{
if (lean_obj_tag(v_code_u2082_797_) == 3)
{
lean_object* v_fvarId_886_; lean_object* v_args_887_; lean_object* v_fvarId_888_; lean_object* v_args_889_; uint8_t v___x_890_; 
v_fvarId_886_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc(v_fvarId_886_);
v_args_887_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc_ref(v_args_887_);
lean_dec_ref(v_code_u2081_796_);
v_fvarId_888_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc(v_fvarId_888_);
v_args_889_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc_ref(v_args_889_);
lean_dec_ref(v_code_u2082_797_);
v___x_890_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_886_, v_fvarId_888_, v_a_798_);
lean_dec(v_fvarId_888_);
lean_dec(v_fvarId_886_);
if (v___x_890_ == 0)
{
lean_dec_ref(v_args_889_);
lean_dec_ref(v_args_887_);
lean_dec(v_a_798_);
return v___x_890_;
}
else
{
uint8_t v___x_891_; 
v___x_891_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_795_, v_args_887_, v_args_889_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_args_887_);
return v___x_891_;
}
}
else
{
uint8_t v___x_892_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_892_ = 0;
return v___x_892_;
}
}
case 4:
{
if (lean_obj_tag(v_code_u2082_797_) == 4)
{
lean_object* v_cases_893_; lean_object* v_cases_894_; lean_object* v_resultType_895_; lean_object* v_discr_896_; lean_object* v_alts_897_; lean_object* v_resultType_898_; lean_object* v_discr_899_; lean_object* v_alts_900_; uint8_t v___x_901_; 
v_cases_893_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc_ref(v_cases_893_);
lean_dec_ref(v_code_u2081_796_);
v_cases_894_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc_ref(v_cases_894_);
lean_dec_ref(v_code_u2082_797_);
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
v___x_901_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_discr_896_, v_discr_899_, v_a_798_);
lean_dec(v_discr_899_);
lean_dec(v_discr_896_);
if (v___x_901_ == 0)
{
lean_dec_ref(v_alts_900_);
lean_dec_ref(v_resultType_898_);
lean_dec_ref(v_alts_897_);
lean_dec_ref(v_resultType_895_);
lean_dec(v_a_798_);
return v___x_901_;
}
else
{
uint8_t v___x_902_; 
v___x_902_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_resultType_895_, v_resultType_898_, v_a_798_);
lean_dec_ref(v_resultType_898_);
lean_dec_ref(v_resultType_895_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_alts_900_);
lean_dec_ref(v_alts_897_);
lean_dec(v_a_798_);
return v___x_902_;
}
else
{
uint8_t v___x_903_; 
v___x_903_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_795_, v_alts_897_, v_alts_900_, v_a_798_);
lean_dec(v_a_798_);
return v___x_903_;
}
}
}
else
{
uint8_t v___x_904_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_904_ = 0;
return v___x_904_;
}
}
case 5:
{
if (lean_obj_tag(v_code_u2082_797_) == 5)
{
lean_object* v_fvarId_905_; lean_object* v_fvarId_906_; uint8_t v___x_907_; 
v_fvarId_905_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc(v_fvarId_905_);
lean_dec_ref(v_code_u2081_796_);
v_fvarId_906_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc(v_fvarId_906_);
lean_dec_ref(v_code_u2082_797_);
v___x_907_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_905_, v_fvarId_906_, v_a_798_);
lean_dec(v_a_798_);
lean_dec(v_fvarId_906_);
lean_dec(v_fvarId_905_);
return v___x_907_;
}
else
{
uint8_t v___x_908_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_908_ = 0;
return v___x_908_;
}
}
case 6:
{
if (lean_obj_tag(v_code_u2082_797_) == 6)
{
lean_object* v_type_909_; lean_object* v_type_910_; uint8_t v___x_911_; 
v_type_909_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc_ref(v_type_909_);
lean_dec_ref(v_code_u2081_796_);
v_type_910_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc_ref(v_type_910_);
lean_dec_ref(v_code_u2082_797_);
v___x_911_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_909_, v_type_910_, v_a_798_);
lean_dec(v_a_798_);
lean_dec_ref(v_type_910_);
lean_dec_ref(v_type_909_);
return v___x_911_;
}
else
{
uint8_t v___x_912_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_912_ = 0;
return v___x_912_;
}
}
case 7:
{
if (lean_obj_tag(v_code_u2082_797_) == 7)
{
lean_object* v_fvarId_913_; lean_object* v_i_914_; lean_object* v_y_915_; lean_object* v_k_916_; lean_object* v_fvarId_917_; lean_object* v_i_918_; lean_object* v_y_919_; lean_object* v_k_920_; uint8_t v___x_921_; 
v_fvarId_913_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc(v_fvarId_913_);
v_i_914_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc(v_i_914_);
v_y_915_ = lean_ctor_get(v_code_u2081_796_, 2);
lean_inc(v_y_915_);
v_k_916_ = lean_ctor_get(v_code_u2081_796_, 3);
lean_inc_ref(v_k_916_);
lean_dec_ref(v_code_u2081_796_);
v_fvarId_917_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc(v_fvarId_917_);
v_i_918_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc(v_i_918_);
v_y_919_ = lean_ctor_get(v_code_u2082_797_, 2);
lean_inc(v_y_919_);
v_k_920_ = lean_ctor_get(v_code_u2082_797_, 3);
lean_inc_ref(v_k_920_);
lean_dec_ref(v_code_u2082_797_);
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
lean_dec(v_a_798_);
return v___x_921_;
}
else
{
uint8_t v___x_922_; 
v___x_922_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_913_, v_fvarId_917_, v_a_798_);
lean_dec(v_fvarId_917_);
lean_dec(v_fvarId_913_);
if (v___x_922_ == 0)
{
lean_dec_ref(v_k_920_);
lean_dec(v_y_919_);
lean_dec_ref(v_k_916_);
lean_dec(v_y_915_);
lean_dec(v_a_798_);
return v___x_922_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_y_915_, v_y_919_, v_a_798_);
lean_dec(v_y_919_);
lean_dec(v_y_915_);
if (v___x_923_ == 0)
{
lean_dec_ref(v_k_920_);
lean_dec_ref(v_k_916_);
lean_dec(v_a_798_);
return v___x_923_;
}
else
{
v_code_u2081_796_ = v_k_916_;
v_code_u2082_797_ = v_k_920_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_925_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_925_ = 0;
return v___x_925_;
}
}
case 8:
{
if (lean_obj_tag(v_code_u2082_797_) == 8)
{
lean_object* v_fvarId_926_; lean_object* v_i_927_; lean_object* v_y_928_; lean_object* v_k_929_; lean_object* v_fvarId_930_; lean_object* v_i_931_; lean_object* v_y_932_; lean_object* v_k_933_; uint8_t v___x_934_; 
v_fvarId_926_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc(v_fvarId_926_);
v_i_927_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc(v_i_927_);
v_y_928_ = lean_ctor_get(v_code_u2081_796_, 2);
lean_inc(v_y_928_);
v_k_929_ = lean_ctor_get(v_code_u2081_796_, 3);
lean_inc_ref(v_k_929_);
lean_dec_ref(v_code_u2081_796_);
v_fvarId_930_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc(v_fvarId_930_);
v_i_931_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc(v_i_931_);
v_y_932_ = lean_ctor_get(v_code_u2082_797_, 2);
lean_inc(v_y_932_);
v_k_933_ = lean_ctor_get(v_code_u2082_797_, 3);
lean_inc_ref(v_k_933_);
lean_dec_ref(v_code_u2082_797_);
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
lean_dec(v_a_798_);
return v___x_934_;
}
else
{
uint8_t v___x_935_; 
v___x_935_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_926_, v_fvarId_930_, v_a_798_);
lean_dec(v_fvarId_930_);
lean_dec(v_fvarId_926_);
if (v___x_935_ == 0)
{
lean_dec_ref(v_k_933_);
lean_dec(v_y_932_);
lean_dec_ref(v_k_929_);
lean_dec(v_y_928_);
lean_dec(v_a_798_);
return v___x_935_;
}
else
{
uint8_t v___x_936_; 
v___x_936_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_928_, v_y_932_, v_a_798_);
lean_dec(v_y_932_);
lean_dec(v_y_928_);
if (v___x_936_ == 0)
{
lean_dec_ref(v_k_933_);
lean_dec_ref(v_k_929_);
lean_dec(v_a_798_);
return v___x_936_;
}
else
{
v_code_u2081_796_ = v_k_929_;
v_code_u2082_797_ = v_k_933_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_938_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_938_ = 0;
return v___x_938_;
}
}
case 9:
{
if (lean_obj_tag(v_code_u2082_797_) == 9)
{
lean_object* v_fvarId_939_; lean_object* v_i_940_; lean_object* v_offset_941_; lean_object* v_y_942_; lean_object* v_ty_943_; lean_object* v_k_944_; lean_object* v_fvarId_945_; lean_object* v_i_946_; lean_object* v_offset_947_; lean_object* v_y_948_; lean_object* v_ty_949_; lean_object* v_k_950_; uint8_t v___x_951_; 
v_fvarId_939_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc(v_fvarId_939_);
v_i_940_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc(v_i_940_);
v_offset_941_ = lean_ctor_get(v_code_u2081_796_, 2);
lean_inc(v_offset_941_);
v_y_942_ = lean_ctor_get(v_code_u2081_796_, 3);
lean_inc(v_y_942_);
v_ty_943_ = lean_ctor_get(v_code_u2081_796_, 4);
lean_inc_ref(v_ty_943_);
v_k_944_ = lean_ctor_get(v_code_u2081_796_, 5);
lean_inc_ref(v_k_944_);
lean_dec_ref(v_code_u2081_796_);
v_fvarId_945_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc(v_fvarId_945_);
v_i_946_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc(v_i_946_);
v_offset_947_ = lean_ctor_get(v_code_u2082_797_, 2);
lean_inc(v_offset_947_);
v_y_948_ = lean_ctor_get(v_code_u2082_797_, 3);
lean_inc(v_y_948_);
v_ty_949_ = lean_ctor_get(v_code_u2082_797_, 4);
lean_inc_ref(v_ty_949_);
v_k_950_ = lean_ctor_get(v_code_u2082_797_, 5);
lean_inc_ref(v_k_950_);
lean_dec_ref(v_code_u2082_797_);
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
lean_dec(v_a_798_);
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
lean_dec(v_a_798_);
return v___x_952_;
}
else
{
uint8_t v___x_953_; 
v___x_953_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_939_, v_fvarId_945_, v_a_798_);
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
lean_dec(v_a_798_);
return v___x_953_;
}
else
{
uint8_t v___x_954_; 
v___x_954_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_942_, v_y_948_, v_a_798_);
lean_dec(v_y_948_);
lean_dec(v_y_942_);
if (v___x_954_ == 0)
{
lean_dec_ref(v_k_950_);
lean_dec_ref(v_ty_949_);
lean_dec_ref(v_k_944_);
lean_dec_ref(v_ty_943_);
lean_dec(v_a_798_);
return v___x_954_;
}
else
{
uint8_t v___x_955_; 
v___x_955_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_943_, v_ty_949_, v_a_798_);
lean_dec_ref(v_ty_949_);
lean_dec_ref(v_ty_943_);
if (v___x_955_ == 0)
{
lean_dec_ref(v_k_950_);
lean_dec_ref(v_k_944_);
lean_dec(v_a_798_);
return v___x_955_;
}
else
{
v_code_u2081_796_ = v_k_944_;
v_code_u2082_797_ = v_k_950_;
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
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_957_ = 0;
return v___x_957_;
}
}
case 10:
{
if (lean_obj_tag(v_code_u2082_797_) == 10)
{
lean_object* v_fvarId_958_; lean_object* v_cidx_959_; lean_object* v_k_960_; lean_object* v_fvarId_961_; lean_object* v_cidx_962_; lean_object* v_k_963_; uint8_t v___x_964_; 
v_fvarId_958_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc(v_fvarId_958_);
v_cidx_959_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc(v_cidx_959_);
v_k_960_ = lean_ctor_get(v_code_u2081_796_, 2);
lean_inc_ref(v_k_960_);
lean_dec_ref(v_code_u2081_796_);
v_fvarId_961_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc(v_fvarId_961_);
v_cidx_962_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc(v_cidx_962_);
v_k_963_ = lean_ctor_get(v_code_u2082_797_, 2);
lean_inc_ref(v_k_963_);
lean_dec_ref(v_code_u2082_797_);
v___x_964_ = lean_nat_dec_eq(v_cidx_959_, v_cidx_962_);
lean_dec(v_cidx_962_);
lean_dec(v_cidx_959_);
if (v___x_964_ == 0)
{
lean_dec_ref(v_k_963_);
lean_dec(v_fvarId_961_);
lean_dec_ref(v_k_960_);
lean_dec(v_fvarId_958_);
lean_dec(v_a_798_);
return v___x_964_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_958_, v_fvarId_961_, v_a_798_);
lean_dec(v_fvarId_961_);
lean_dec(v_fvarId_958_);
if (v___x_965_ == 0)
{
lean_dec_ref(v_k_963_);
lean_dec_ref(v_k_960_);
lean_dec(v_a_798_);
return v___x_965_;
}
else
{
v_code_u2081_796_ = v_k_960_;
v_code_u2082_797_ = v_k_963_;
goto _start;
}
}
}
else
{
uint8_t v___x_967_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_967_ = 0;
return v___x_967_;
}
}
case 11:
{
if (lean_obj_tag(v_code_u2082_797_) == 11)
{
lean_object* v_fvarId_968_; lean_object* v_n_969_; uint8_t v_check_970_; uint8_t v_persistent_971_; lean_object* v_k_972_; lean_object* v_fvarId_973_; lean_object* v_n_974_; uint8_t v_check_975_; uint8_t v_persistent_976_; lean_object* v_k_977_; 
v_fvarId_968_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc(v_fvarId_968_);
v_n_969_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc(v_n_969_);
v_check_970_ = lean_ctor_get_uint8(v_code_u2081_796_, sizeof(void*)*3);
v_persistent_971_ = lean_ctor_get_uint8(v_code_u2081_796_, sizeof(void*)*3 + 1);
v_k_972_ = lean_ctor_get(v_code_u2081_796_, 2);
lean_inc_ref(v_k_972_);
lean_dec_ref(v_code_u2081_796_);
v_fvarId_973_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc(v_fvarId_973_);
v_n_974_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc(v_n_974_);
v_check_975_ = lean_ctor_get_uint8(v_code_u2082_797_, sizeof(void*)*3);
v_persistent_976_ = lean_ctor_get_uint8(v_code_u2082_797_, sizeof(void*)*3 + 1);
v_k_977_ = lean_ctor_get(v_code_u2082_797_, 2);
lean_inc_ref(v_k_977_);
lean_dec_ref(v_code_u2082_797_);
v_fvarId_u2081_817_ = v_fvarId_968_;
v_n_u2081_818_ = v_n_969_;
v_c_u2081_819_ = v_check_970_;
v_p_u2081_820_ = v_persistent_971_;
v_k_u2081_821_ = v_k_972_;
v_fvarId_u2082_822_ = v_fvarId_973_;
v_n_u2082_823_ = v_n_974_;
v_c_u2082_824_ = v_check_975_;
v_p_u2082_825_ = v_persistent_976_;
v_k_u2082_826_ = v_k_977_;
v___y_827_ = v_a_798_;
goto v___jp_816_;
}
else
{
uint8_t v___x_978_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_978_ = 0;
return v___x_978_;
}
}
case 12:
{
if (lean_obj_tag(v_code_u2082_797_) == 12)
{
lean_object* v_fvarId_979_; lean_object* v_n_980_; uint8_t v_check_981_; uint8_t v_persistent_982_; lean_object* v_k_983_; lean_object* v_fvarId_984_; lean_object* v_n_985_; uint8_t v_check_986_; uint8_t v_persistent_987_; lean_object* v_k_988_; 
v_fvarId_979_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc(v_fvarId_979_);
v_n_980_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc(v_n_980_);
v_check_981_ = lean_ctor_get_uint8(v_code_u2081_796_, sizeof(void*)*3);
v_persistent_982_ = lean_ctor_get_uint8(v_code_u2081_796_, sizeof(void*)*3 + 1);
v_k_983_ = lean_ctor_get(v_code_u2081_796_, 2);
lean_inc_ref(v_k_983_);
lean_dec_ref(v_code_u2081_796_);
v_fvarId_984_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc(v_fvarId_984_);
v_n_985_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc(v_n_985_);
v_check_986_ = lean_ctor_get_uint8(v_code_u2082_797_, sizeof(void*)*3);
v_persistent_987_ = lean_ctor_get_uint8(v_code_u2082_797_, sizeof(void*)*3 + 1);
v_k_988_ = lean_ctor_get(v_code_u2082_797_, 2);
lean_inc_ref(v_k_988_);
lean_dec_ref(v_code_u2082_797_);
v_fvarId_u2081_817_ = v_fvarId_979_;
v_n_u2081_818_ = v_n_980_;
v_c_u2081_819_ = v_check_981_;
v_p_u2081_820_ = v_persistent_982_;
v_k_u2081_821_ = v_k_983_;
v_fvarId_u2082_822_ = v_fvarId_984_;
v_n_u2082_823_ = v_n_985_;
v_c_u2082_824_ = v_check_986_;
v_p_u2082_825_ = v_persistent_987_;
v_k_u2082_826_ = v_k_988_;
v___y_827_ = v_a_798_;
goto v___jp_816_;
}
else
{
uint8_t v___x_989_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_989_ = 0;
return v___x_989_;
}
}
default: 
{
if (lean_obj_tag(v_code_u2082_797_) == 13)
{
lean_object* v_fvarId_990_; lean_object* v_k_991_; lean_object* v_fvarId_992_; lean_object* v_k_993_; uint8_t v___x_994_; 
v_fvarId_990_ = lean_ctor_get(v_code_u2081_796_, 0);
lean_inc(v_fvarId_990_);
v_k_991_ = lean_ctor_get(v_code_u2081_796_, 1);
lean_inc_ref(v_k_991_);
lean_dec_ref(v_code_u2081_796_);
v_fvarId_992_ = lean_ctor_get(v_code_u2082_797_, 0);
lean_inc(v_fvarId_992_);
v_k_993_ = lean_ctor_get(v_code_u2082_797_, 1);
lean_inc_ref(v_k_993_);
lean_dec_ref(v_code_u2082_797_);
v___x_994_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_990_, v_fvarId_992_, v_a_798_);
lean_dec(v_fvarId_992_);
lean_dec(v_fvarId_990_);
if (v___x_994_ == 0)
{
lean_dec_ref(v_k_993_);
lean_dec_ref(v_k_991_);
lean_dec(v_a_798_);
return v___x_994_;
}
else
{
v_code_u2081_796_ = v_k_991_;
v_code_u2082_797_ = v_k_993_;
goto _start;
}
}
else
{
uint8_t v___x_996_; 
lean_dec_ref(v_code_u2081_796_);
lean_dec(v_a_798_);
lean_dec_ref(v_code_u2082_797_);
v___x_996_ = 0;
return v___x_996_;
}
}
}
v___jp_799_:
{
uint8_t v___x_805_; 
v___x_805_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v___y_801_, v___y_804_, v___y_802_);
lean_dec(v___y_804_);
lean_dec(v___y_801_);
if (v___x_805_ == 0)
{
lean_dec_ref(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_800_);
return v___x_805_;
}
else
{
v_code_u2081_796_ = v___y_803_;
v_code_u2082_797_ = v___y_800_;
v_a_798_ = v___y_802_;
goto _start;
}
}
v___jp_807_:
{
if (v___y_815_ == 0)
{
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v___y_815_;
}
else
{
if (v___y_814_ == 0)
{
if (v___y_808_ == 0)
{
v___y_800_ = v___y_809_;
v___y_801_ = v___y_810_;
v___y_802_ = v___y_811_;
v___y_803_ = v___y_812_;
v___y_804_ = v___y_813_;
goto v___jp_799_;
}
else
{
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v___y_814_;
}
}
else
{
if (v___y_808_ == 0)
{
lean_dec(v___y_813_);
lean_dec_ref(v___y_812_);
lean_dec(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
return v___y_808_;
}
else
{
v___y_800_ = v___y_809_;
v___y_801_ = v___y_810_;
v___y_802_ = v___y_811_;
v___y_803_ = v___y_812_;
v___y_804_ = v___y_813_;
goto v___jp_799_;
}
}
}
}
v___jp_816_:
{
uint8_t v___x_828_; 
v___x_828_ = lean_nat_dec_eq(v_n_u2081_818_, v_n_u2082_823_);
lean_dec(v_n_u2082_823_);
lean_dec(v_n_u2081_818_);
if (v___x_828_ == 0)
{
lean_dec(v___y_827_);
lean_dec_ref(v_k_u2082_826_);
lean_dec(v_fvarId_u2082_822_);
lean_dec_ref(v_k_u2081_821_);
lean_dec(v_fvarId_u2081_817_);
return v___x_828_;
}
else
{
if (v_c_u2081_819_ == 0)
{
if (v_c_u2082_824_ == 0)
{
v___y_808_ = v_p_u2082_825_;
v___y_809_ = v_k_u2082_826_;
v___y_810_ = v_fvarId_u2081_817_;
v___y_811_ = v___y_827_;
v___y_812_ = v_k_u2081_821_;
v___y_813_ = v_fvarId_u2082_822_;
v___y_814_ = v_p_u2081_820_;
v___y_815_ = v___x_828_;
goto v___jp_807_;
}
else
{
lean_dec(v___y_827_);
lean_dec_ref(v_k_u2082_826_);
lean_dec(v_fvarId_u2082_822_);
lean_dec_ref(v_k_u2081_821_);
lean_dec(v_fvarId_u2081_817_);
return v_c_u2081_819_;
}
}
else
{
v___y_808_ = v_p_u2082_825_;
v___y_809_ = v_k_u2082_826_;
v___y_810_ = v_fvarId_u2081_817_;
v___y_811_ = v___y_827_;
v___y_812_ = v_k_u2081_821_;
v___y_813_ = v_fvarId_u2082_822_;
v___y_814_ = v_p_u2081_820_;
v___y_815_ = v_c_u2082_824_;
goto v___jp_807_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(uint8_t v_pu_997_, lean_object* v_code_998_, lean_object* v_code_999_, lean_object* v_params_u2081_1000_, lean_object* v_params_u2082_1001_, lean_object* v_i_1002_, lean_object* v_a_1003_){
_start:
{
lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1004_ = lean_array_get_size(v_params_u2081_1000_);
v___x_1005_ = lean_nat_dec_lt(v_i_1002_, v___x_1004_);
if (v___x_1005_ == 0)
{
uint8_t v___x_1006_; 
lean_dec(v_i_1002_);
v___x_1006_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_997_, v_code_998_, v_code_999_, v_a_1003_);
return v___x_1006_;
}
else
{
lean_object* v_p_u2081_1007_; lean_object* v_fvarId_1008_; lean_object* v_type_1009_; lean_object* v_p_u2082_1010_; lean_object* v_fvarId_1011_; lean_object* v_type_1012_; uint8_t v___x_1013_; 
v_p_u2081_1007_ = lean_array_fget_borrowed(v_params_u2081_1000_, v_i_1002_);
v_fvarId_1008_ = lean_ctor_get(v_p_u2081_1007_, 0);
v_type_1009_ = lean_ctor_get(v_p_u2081_1007_, 2);
v_p_u2082_1010_ = lean_array_fget_borrowed(v_params_u2082_1001_, v_i_1002_);
v_fvarId_1011_ = lean_ctor_get(v_p_u2082_1010_, 0);
v_type_1012_ = lean_ctor_get(v_p_u2082_1010_, 2);
v___x_1013_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_1009_, v_type_1012_, v_a_1003_);
if (v___x_1013_ == 0)
{
lean_dec(v_a_1003_);
lean_dec(v_i_1002_);
lean_dec_ref(v_code_999_);
lean_dec_ref(v_code_998_);
return v___x_1013_;
}
else
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_unsigned_to_nat(1u);
v___x_1015_ = lean_nat_add(v_i_1002_, v___x_1014_);
lean_dec(v_i_1002_);
lean_inc(v_fvarId_1008_);
lean_inc(v_fvarId_1011_);
v___x_1016_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_1011_, v_fvarId_1008_, v_a_1003_);
v_i_1002_ = v___x_1015_;
v_a_1003_ = v___x_1016_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg___boxed(lean_object* v_pu_1018_, lean_object* v_code_1019_, lean_object* v_code_1020_, lean_object* v_params_u2081_1021_, lean_object* v_params_u2082_1022_, lean_object* v_i_1023_, lean_object* v_a_1024_){
_start:
{
uint8_t v_pu_boxed_1025_; uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_pu_boxed_1025_ = lean_unbox(v_pu_1018_);
v_res_1026_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_boxed_1025_, v_code_1019_, v_code_1020_, v_params_u2081_1021_, v_params_u2082_1022_, v_i_1023_, v_a_1024_);
lean_dec_ref(v_params_u2082_1022_);
lean_dec_ref(v_params_u2081_1021_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts___boxed(lean_object* v_pu_1028_, lean_object* v_alts_u2081_1029_, lean_object* v_alts_u2082_1030_, lean_object* v_a_1031_){
_start:
{
uint8_t v_pu_boxed_1032_; uint8_t v_res_1033_; lean_object* v_r_1034_; 
v_pu_boxed_1032_ = lean_unbox(v_pu_1028_);
v_res_1033_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_boxed_1032_, v_alts_u2081_1029_, v_alts_u2082_1030_, v_a_1031_);
lean_dec(v_a_1031_);
v_r_1034_ = lean_box(v_res_1033_);
return v_r_1034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___boxed(lean_object* v_pu_1035_, lean_object* v_as_1036_, lean_object* v_sz_1037_, lean_object* v_i_1038_, lean_object* v_b_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v_pu_boxed_1041_; size_t v_sz_boxed_1042_; size_t v_i_boxed_1043_; lean_object* v_res_1044_; 
v_pu_boxed_1041_ = lean_unbox(v_pu_1035_);
v_sz_boxed_1042_ = lean_unbox_usize(v_sz_1037_);
lean_dec(v_sz_1037_);
v_i_boxed_1043_ = lean_unbox_usize(v_i_1038_);
lean_dec(v_i_1038_);
v_res_1044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_boxed_1041_, v_as_1036_, v_sz_boxed_1042_, v_i_boxed_1043_, v_b_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v_as_1036_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqv___boxed(lean_object* v_pu_1045_, lean_object* v_code_u2081_1046_, lean_object* v_code_u2082_1047_, lean_object* v_a_1048_){
_start:
{
uint8_t v_pu_boxed_1049_; uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_pu_boxed_1049_ = lean_unbox(v_pu_1045_);
v_res_1050_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_boxed_1049_, v_code_u2081_1046_, v_code_u2082_1047_, v_a_1048_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(uint8_t v_pu_1052_, lean_object* v_code_1053_, lean_object* v_code_1054_, uint8_t v_pu_1055_, lean_object* v_params_u2081_1056_, lean_object* v_params_u2082_1057_, lean_object* v_h_1058_, lean_object* v_i_1059_, lean_object* v_a_1060_){
_start:
{
uint8_t v___x_1061_; 
lean_inc(v_a_1060_);
v___x_1061_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_1052_, v_code_1053_, v_code_1054_, v_params_u2081_1056_, v_params_u2082_1057_, v_i_1059_, v_a_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___boxed(lean_object* v_pu_1062_, lean_object* v_code_1063_, lean_object* v_code_1064_, lean_object* v_pu_1065_, lean_object* v_params_u2081_1066_, lean_object* v_params_u2082_1067_, lean_object* v_h_1068_, lean_object* v_i_1069_, lean_object* v_a_1070_){
_start:
{
uint8_t v_pu_boxed_1071_; uint8_t v_pu_boxed_1072_; uint8_t v_res_1073_; lean_object* v_r_1074_; 
v_pu_boxed_1071_ = lean_unbox(v_pu_1062_);
v_pu_boxed_1072_ = lean_unbox(v_pu_1065_);
v_res_1073_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(v_pu_boxed_1071_, v_code_1063_, v_code_1064_, v_pu_boxed_1072_, v_params_u2081_1066_, v_params_u2082_1067_, v_h_1068_, v_i_1069_, v_a_1070_);
lean_dec(v_a_1070_);
lean_dec_ref(v_params_u2082_1067_);
lean_dec_ref(v_params_u2081_1066_);
v_r_1074_ = lean_box(v_res_1073_);
return v_r_1074_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t v_pu_1075_, lean_object* v_c_u2081_1076_, lean_object* v_c_u2082_1077_){
_start:
{
lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = lean_box(1);
v___x_1079_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_1075_, v_c_u2081_1076_, v_c_u2082_1077_, v___x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_alphaEqv___boxed(lean_object* v_pu_1080_, lean_object* v_c_u2081_1081_, lean_object* v_c_u2082_1082_){
_start:
{
uint8_t v_pu_boxed_1083_; uint8_t v_res_1084_; lean_object* v_r_1085_; 
v_pu_boxed_1083_ = lean_unbox(v_pu_1080_);
v_res_1084_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v_pu_boxed_1083_, v_c_u2081_1081_, v_c_u2082_1082_);
v_r_1085_ = lean_box(v_res_1084_);
return v_r_1085_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
