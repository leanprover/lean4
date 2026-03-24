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
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(uint8_t v___x_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
switch(lean_obj_tag(v_x_517_))
{
case 0:
{
switch(lean_obj_tag(v_x_518_))
{
case 2:
{
return v___x_516_;
}
case 0:
{
lean_object* v_ctorName_519_; lean_object* v_ctorName_520_; uint8_t v___x_521_; 
v_ctorName_519_ = lean_ctor_get(v_x_517_, 0);
v_ctorName_520_ = lean_ctor_get(v_x_518_, 0);
v___x_521_ = l_Lean_Name_lt(v_ctorName_519_, v_ctorName_520_);
return v___x_521_;
}
default: 
{
uint8_t v___x_522_; 
v___x_522_ = 0;
return v___x_522_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_518_))
{
case 2:
{
return v___x_516_;
}
case 1:
{
lean_object* v_info_523_; lean_object* v_info_524_; lean_object* v_name_525_; lean_object* v_name_526_; uint8_t v___x_527_; 
v_info_523_ = lean_ctor_get(v_x_517_, 0);
v_info_524_ = lean_ctor_get(v_x_518_, 0);
v_name_525_ = lean_ctor_get(v_info_523_, 0);
v_name_526_ = lean_ctor_get(v_info_524_, 0);
v___x_527_ = l_Lean_Name_lt(v_name_525_, v_name_526_);
return v___x_527_;
}
default: 
{
uint8_t v___x_528_; 
v___x_528_ = 0;
return v___x_528_;
}
}
}
default: 
{
uint8_t v___x_529_; 
v___x_529_ = 0;
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed(lean_object* v___x_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
uint8_t v___x_223__boxed_533_; uint8_t v_res_534_; lean_object* v_r_535_; 
v___x_223__boxed_533_ = lean_unbox(v___x_530_);
v_res_534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_223__boxed_533_, v_x_531_, v_x_532_);
lean_dec_ref(v_x_532_);
lean_dec_ref(v_x_531_);
v_r_535_ = lean_box(v_res_534_);
return v_r_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(lean_object* v_as_536_, lean_object* v_lo_537_, lean_object* v_hi_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_nat_dec_lt(v_lo_537_, v_hi_538_);
if (v___x_539_ == 0)
{
lean_dec(v_lo_537_);
return v_as_536_;
}
else
{
lean_object* v___x_540_; lean_object* v___f_541_; lean_object* v___x_542_; lean_object* v_fst_543_; lean_object* v_snd_544_; uint8_t v___x_545_; 
v___x_540_ = lean_box(v___x_539_);
v___f_541_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_541_, 0, v___x_540_);
lean_inc(v_lo_537_);
v___x_542_ = l_Array_qpartition___redArg(v_as_536_, v___f_541_, v_lo_537_, v_hi_538_);
v_fst_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_fst_543_);
v_snd_544_ = lean_ctor_get(v___x_542_, 1);
lean_inc(v_snd_544_);
lean_dec_ref(v___x_542_);
v___x_545_ = lean_nat_dec_le(v_hi_538_, v_fst_543_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_snd_544_, v_lo_537_, v_fst_543_);
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_add(v_fst_543_, v___x_547_);
lean_dec(v_fst_543_);
v_as_536_ = v___x_546_;
v_lo_537_ = v___x_548_;
goto _start;
}
else
{
lean_dec(v_fst_543_);
lean_dec(v_lo_537_);
return v_snd_544_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___boxed(lean_object* v_as_550_, lean_object* v_lo_551_, lean_object* v_hi_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_as_550_, v_lo_551_, v_hi_552_);
lean_dec(v_hi_552_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(lean_object* v_alts_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = lean_array_get_size(v_alts_554_);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_nat_dec_eq(v___x_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___y_561_; uint8_t v___x_565_; 
v___x_558_ = lean_unsigned_to_nat(1u);
v___x_559_ = lean_nat_sub(v___x_555_, v___x_558_);
v___x_565_ = lean_nat_dec_le(v___x_556_, v___x_559_);
if (v___x_565_ == 0)
{
lean_inc(v___x_559_);
v___y_561_ = v___x_559_;
goto v___jp_560_;
}
else
{
v___y_561_ = v___x_556_;
goto v___jp_560_;
}
v___jp_560_:
{
uint8_t v___x_562_; 
v___x_562_ = lean_nat_dec_le(v___y_561_, v___x_559_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; 
lean_dec(v___x_559_);
lean_inc(v___y_561_);
v___x_563_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_alts_554_, v___y_561_, v___y_561_);
lean_dec(v___y_561_);
return v___x_563_;
}
else
{
lean_object* v___x_564_; 
v___x_564_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_alts_554_, v___y_561_, v___x_559_);
lean_dec(v___x_559_);
return v___x_564_;
}
}
}
else
{
return v_alts_554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(uint8_t v_pu_566_, lean_object* v_alts_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___boxed(lean_object* v_pu_569_, lean_object* v_alts_570_){
_start:
{
uint8_t v_pu_boxed_571_; lean_object* v_res_572_; 
v_pu_boxed_571_ = lean_unbox(v_pu_569_);
v_res_572_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(v_pu_boxed_571_, v_alts_570_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(lean_object* v_n_573_, lean_object* v_as_574_, lean_object* v_lo_575_, lean_object* v_hi_576_, lean_object* v_w_577_, lean_object* v_hlo_578_, lean_object* v_hhi_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_as_574_, v_lo_575_, v_hi_576_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___boxed(lean_object* v_n_581_, lean_object* v_as_582_, lean_object* v_lo_583_, lean_object* v_hi_584_, lean_object* v_w_585_, lean_object* v_hlo_586_, lean_object* v_hhi_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(v_n_581_, v_as_582_, v_lo_583_, v_hi_584_, v_w_585_, v_hlo_586_, v_hhi_587_);
lean_dec(v_hi_584_);
lean_dec(v_n_581_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(uint8_t v_pu_592_, lean_object* v_as_593_, size_t v_sz_594_, size_t v_i_595_, lean_object* v_b_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_a_599_; uint8_t v___x_603_; 
v___x_603_ = lean_usize_dec_lt(v_i_595_, v_sz_594_);
if (v___x_603_ == 0)
{
return v_b_596_;
}
else
{
lean_object* v_snd_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_692_; 
v_snd_604_ = lean_ctor_get(v_b_596_, 1);
v_isSharedCheck_692_ = !lean_is_exclusive(v_b_596_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v_b_596_, 0);
lean_dec(v_unused_693_);
v___x_606_ = v_b_596_;
v_isShared_607_ = v_isSharedCheck_692_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snd_604_);
lean_dec(v_b_596_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_692_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_array_608_; lean_object* v_start_609_; lean_object* v_stop_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v_array_608_ = lean_ctor_get(v_snd_604_, 0);
v_start_609_ = lean_ctor_get(v_snd_604_, 1);
v_stop_610_ = lean_ctor_get(v_snd_604_, 2);
v___x_611_ = lean_box(0);
v___x_612_ = lean_nat_dec_lt(v_start_609_, v_stop_610_);
if (v___x_612_ == 0)
{
lean_object* v___x_614_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_611_);
v___x_614_ = v___x_606_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_snd_604_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
else
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_688_; 
lean_inc(v_stop_610_);
lean_inc(v_start_609_);
lean_inc_ref(v_array_608_);
v_isSharedCheck_688_ = !lean_is_exclusive(v_snd_604_);
if (v_isSharedCheck_688_ == 0)
{
lean_object* v_unused_689_; lean_object* v_unused_690_; lean_object* v_unused_691_; 
v_unused_689_ = lean_ctor_get(v_snd_604_, 2);
lean_dec(v_unused_689_);
v_unused_690_ = lean_ctor_get(v_snd_604_, 1);
lean_dec(v_unused_690_);
v_unused_691_ = lean_ctor_get(v_snd_604_, 0);
lean_dec(v_unused_691_);
v___x_617_ = v_snd_604_;
v_isShared_618_ = v_isSharedCheck_688_;
goto v_resetjp_616_;
}
else
{
lean_dec(v_snd_604_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_688_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_a_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_624_; 
v_a_619_ = lean_array_uget_borrowed(v_as_593_, v_i_595_);
v___x_620_ = lean_array_fget(v_array_608_, v_start_609_);
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_start_609_, v___x_621_);
lean_dec(v_start_609_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_622_);
v___x_624_ = v___x_617_;
goto v_reusejp_623_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_array_608_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_622_);
lean_ctor_set(v_reuseFailAlloc_687_, 2, v_stop_610_);
v___x_624_ = v_reuseFailAlloc_687_;
goto v_reusejp_623_;
}
v_reusejp_623_:
{
uint8_t v___y_626_; 
switch(lean_obj_tag(v_a_619_))
{
case 0:
{
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v_ctorName_635_; lean_object* v_params_636_; lean_object* v_code_637_; lean_object* v_ctorName_638_; lean_object* v_params_639_; lean_object* v_code_640_; uint8_t v___x_641_; 
v_ctorName_635_ = lean_ctor_get(v_a_619_, 0);
v_params_636_ = lean_ctor_get(v_a_619_, 1);
v_code_637_ = lean_ctor_get(v_a_619_, 2);
v_ctorName_638_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_ctorName_638_);
v_params_639_ = lean_ctor_get(v___x_620_, 1);
lean_inc_ref(v_params_639_);
v_code_640_ = lean_ctor_get(v___x_620_, 2);
lean_inc_ref(v_code_640_);
lean_dec_ref(v___x_620_);
v___x_641_ = lean_name_eq(v_ctorName_635_, v_ctorName_638_);
lean_dec(v_ctorName_638_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec_ref(v_code_640_);
lean_dec_ref(v_params_639_);
lean_del_object(v___x_606_);
v___x_642_ = lean_box(v___x_641_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_624_);
return v___x_644_;
}
else
{
lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_645_ = lean_array_get_size(v_params_639_);
v___x_646_ = lean_array_get_size(v_params_636_);
v___x_647_ = lean_nat_dec_eq(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_dec_ref(v_code_640_);
lean_dec_ref(v_params_639_);
v___y_626_ = v___x_647_;
goto v___jp_625_;
}
else
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_597_);
lean_inc_ref(v_code_637_);
v___x_649_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_592_, v_code_637_, v_code_640_, v_params_636_, v_params_639_, v___x_648_, v___y_597_);
lean_dec_ref(v_params_639_);
if (v___x_649_ == 0)
{
v___y_626_ = v___x_649_;
goto v___jp_625_;
}
else
{
lean_object* v___x_650_; 
lean_del_object(v___x_606_);
v___x_650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_611_);
lean_ctor_set(v___x_650_, 1, v___x_624_);
v_a_599_ = v___x_650_;
goto v___jp_598_;
}
}
}
}
else
{
lean_dec(v___x_620_);
lean_del_object(v___x_606_);
goto v___jp_632_;
}
}
case 1:
{
lean_del_object(v___x_606_);
if (lean_obj_tag(v___x_620_) == 1)
{
lean_object* v_info_651_; lean_object* v_code_652_; lean_object* v_info_653_; lean_object* v_code_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_673_; 
v_info_651_ = lean_ctor_get(v_a_619_, 0);
v_code_652_ = lean_ctor_get(v_a_619_, 1);
v_info_653_ = lean_ctor_get(v___x_620_, 0);
v_code_654_ = lean_ctor_get(v___x_620_, 1);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_673_ == 0)
{
v___x_656_ = v___x_620_;
v_isShared_657_ = v_isSharedCheck_673_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_code_654_);
lean_inc(v_info_653_);
lean_dec(v___x_620_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_673_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
uint8_t v___x_658_; 
v___x_658_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_info_651_, v_info_653_);
lean_dec_ref(v_info_653_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
lean_dec_ref(v_code_654_);
v___x_659_ = lean_box(v___x_658_);
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
if (v_isShared_657_ == 0)
{
lean_ctor_set_tag(v___x_656_, 0);
lean_ctor_set(v___x_656_, 1, v___x_624_);
lean_ctor_set(v___x_656_, 0, v___x_660_);
v___x_662_ = v___x_656_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_624_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
uint8_t v___x_664_; 
lean_inc(v___y_597_);
lean_inc_ref(v_code_652_);
v___x_664_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_592_, v_code_652_, v_code_654_, v___y_597_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_665_ = lean_box(v___x_664_);
v___x_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
if (v_isShared_657_ == 0)
{
lean_ctor_set_tag(v___x_656_, 0);
lean_ctor_set(v___x_656_, 1, v___x_624_);
lean_ctor_set(v___x_656_, 0, v___x_666_);
v___x_668_ = v___x_656_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_624_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
else
{
lean_object* v___x_671_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set_tag(v___x_656_, 0);
lean_ctor_set(v___x_656_, 1, v___x_624_);
lean_ctor_set(v___x_656_, 0, v___x_611_);
v___x_671_ = v___x_656_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_624_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
v_a_599_ = v___x_671_;
goto v___jp_598_;
}
}
}
}
}
else
{
lean_dec(v___x_620_);
goto v___jp_632_;
}
}
default: 
{
lean_del_object(v___x_606_);
if (lean_obj_tag(v___x_620_) == 2)
{
lean_object* v_code_674_; lean_object* v_code_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_686_; 
v_code_674_ = lean_ctor_get(v_a_619_, 0);
v_code_675_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_686_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_686_ == 0)
{
v___x_677_ = v___x_620_;
v_isShared_678_ = v_isSharedCheck_686_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_code_675_);
lean_dec(v___x_620_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_686_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
uint8_t v___x_679_; 
lean_inc(v___y_597_);
lean_inc_ref(v_code_674_);
v___x_679_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_592_, v_code_674_, v_code_675_, v___y_597_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_682_; 
v___x_680_ = lean_box(v___x_679_);
if (v_isShared_678_ == 0)
{
lean_ctor_set_tag(v___x_677_, 1);
lean_ctor_set(v___x_677_, 0, v___x_680_);
v___x_682_ = v___x_677_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_680_);
v___x_682_ = v_reuseFailAlloc_684_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
lean_object* v___x_683_; 
v___x_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
lean_ctor_set(v___x_683_, 1, v___x_624_);
return v___x_683_;
}
}
else
{
lean_object* v___x_685_; 
lean_del_object(v___x_677_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_611_);
lean_ctor_set(v___x_685_, 1, v___x_624_);
v_a_599_ = v___x_685_;
goto v___jp_598_;
}
}
}
else
{
lean_dec(v___x_620_);
goto v___jp_632_;
}
}
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_627_ = lean_box(v___y_626_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_624_);
lean_ctor_set(v___x_606_, 0, v___x_628_);
v___x_630_ = v___x_606_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v___x_624_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
v___jp_632_:
{
lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0));
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
lean_ctor_set(v___x_634_, 1, v___x_624_);
return v___x_634_;
}
}
}
}
}
}
v___jp_598_:
{
size_t v___x_600_; size_t v___x_601_; 
v___x_600_ = ((size_t)1ULL);
v___x_601_ = lean_usize_add(v_i_595_, v___x_600_);
v_i_595_ = v___x_601_;
v_b_596_ = v_a_599_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(uint8_t v_pu_694_, lean_object* v_alts_u2081_695_, lean_object* v_alts_u2082_696_, lean_object* v_a_697_){
_start:
{
lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_698_ = lean_array_get_size(v_alts_u2081_695_);
v___x_699_ = lean_array_get_size(v_alts_u2082_696_);
v___x_700_ = lean_nat_dec_eq(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_dec_ref(v_alts_u2082_696_);
lean_dec_ref(v_alts_u2081_695_);
return v___x_700_;
}
else
{
lean_object* v_alts_u2081_701_; lean_object* v_alts_u2082_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; size_t v_sz_708_; size_t v___x_709_; lean_object* v___x_710_; lean_object* v_fst_711_; 
v_alts_u2081_701_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2081_695_);
v_alts_u2082_702_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2082_696_);
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_array_get_size(v_alts_u2082_702_);
v___x_705_ = l_Array_toSubarray___redArg(v_alts_u2082_702_, v___x_703_, v___x_704_);
v___x_706_ = lean_box(0);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
v_sz_708_ = lean_array_size(v_alts_u2081_701_);
v___x_709_ = ((size_t)0ULL);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_694_, v_alts_u2081_701_, v_sz_708_, v___x_709_, v___x_707_, v_a_697_);
lean_dec_ref(v_alts_u2081_701_);
v_fst_711_ = lean_ctor_get(v___x_710_, 0);
lean_inc(v_fst_711_);
lean_dec_ref(v___x_710_);
if (lean_obj_tag(v_fst_711_) == 0)
{
return v___x_700_;
}
else
{
lean_object* v_val_712_; uint8_t v___x_713_; 
v_val_712_ = lean_ctor_get(v_fst_711_, 0);
lean_inc(v_val_712_);
lean_dec_ref(v_fst_711_);
v___x_713_ = lean_unbox(v_val_712_);
lean_dec(v_val_712_);
return v___x_713_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqv(uint8_t v_pu_714_, lean_object* v_code_u2081_715_, lean_object* v_code_u2082_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; lean_object* v___y_722_; lean_object* v___y_723_; uint8_t v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; uint8_t v___y_733_; uint8_t v___y_734_; lean_object* v_fvarId_u2081_736_; lean_object* v_n_u2081_737_; uint8_t v_c_u2081_738_; uint8_t v_p_u2081_739_; lean_object* v_k_u2081_740_; lean_object* v_fvarId_u2082_741_; lean_object* v_n_u2082_742_; uint8_t v_c_u2082_743_; uint8_t v_p_u2082_744_; lean_object* v_k_u2082_745_; lean_object* v___y_746_; 
switch(lean_obj_tag(v_code_u2081_715_))
{
case 0:
{
if (lean_obj_tag(v_code_u2082_716_) == 0)
{
lean_object* v_decl_748_; lean_object* v_decl_749_; lean_object* v_k_750_; lean_object* v_k_751_; lean_object* v_fvarId_752_; lean_object* v_type_753_; lean_object* v_value_754_; lean_object* v_fvarId_755_; lean_object* v_type_756_; lean_object* v_value_757_; uint8_t v___x_758_; 
v_decl_748_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc_ref(v_decl_748_);
v_decl_749_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc_ref(v_decl_749_);
v_k_750_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc_ref(v_k_750_);
lean_dec_ref(v_code_u2081_715_);
v_k_751_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc_ref(v_k_751_);
lean_dec_ref(v_code_u2082_716_);
v_fvarId_752_ = lean_ctor_get(v_decl_748_, 0);
lean_inc(v_fvarId_752_);
v_type_753_ = lean_ctor_get(v_decl_748_, 2);
lean_inc_ref(v_type_753_);
v_value_754_ = lean_ctor_get(v_decl_748_, 3);
lean_inc(v_value_754_);
lean_dec_ref(v_decl_748_);
v_fvarId_755_ = lean_ctor_get(v_decl_749_, 0);
lean_inc(v_fvarId_755_);
v_type_756_ = lean_ctor_get(v_decl_749_, 2);
lean_inc_ref(v_type_756_);
v_value_757_ = lean_ctor_get(v_decl_749_, 3);
lean_inc(v_value_757_);
lean_dec_ref(v_decl_749_);
v___x_758_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_753_, v_type_756_, v_a_717_);
lean_dec_ref(v_type_756_);
lean_dec_ref(v_type_753_);
if (v___x_758_ == 0)
{
lean_dec(v_value_757_);
lean_dec(v_fvarId_755_);
lean_dec(v_value_754_);
lean_dec(v_fvarId_752_);
lean_dec_ref(v_k_751_);
lean_dec_ref(v_k_750_);
lean_dec(v_a_717_);
return v___x_758_;
}
else
{
uint8_t v___x_759_; 
v___x_759_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_714_, v_value_754_, v_value_757_, v_a_717_);
lean_dec(v_value_754_);
if (v___x_759_ == 0)
{
lean_dec(v_fvarId_755_);
lean_dec(v_fvarId_752_);
lean_dec_ref(v_k_751_);
lean_dec_ref(v_k_750_);
lean_dec(v_a_717_);
return v___x_759_;
}
else
{
lean_object* v___x_760_; 
v___x_760_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_755_, v_fvarId_752_, v_a_717_);
v_code_u2081_715_ = v_k_750_;
v_code_u2082_716_ = v_k_751_;
v_a_717_ = v___x_760_;
goto _start;
}
}
}
else
{
uint8_t v___x_762_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_762_ = 0;
return v___x_762_;
}
}
case 1:
{
if (lean_obj_tag(v_code_u2082_716_) == 1)
{
lean_object* v_decl_763_; lean_object* v_decl_764_; lean_object* v_k_765_; lean_object* v_k_766_; lean_object* v_fvarId_767_; lean_object* v_params_768_; lean_object* v_type_769_; lean_object* v_value_770_; lean_object* v_fvarId_771_; lean_object* v_params_772_; lean_object* v_type_773_; lean_object* v_value_774_; uint8_t v___x_775_; 
v_decl_763_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc_ref(v_decl_763_);
v_decl_764_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc_ref(v_decl_764_);
v_k_765_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc_ref(v_k_765_);
lean_dec_ref(v_code_u2081_715_);
v_k_766_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc_ref(v_k_766_);
lean_dec_ref(v_code_u2082_716_);
v_fvarId_767_ = lean_ctor_get(v_decl_763_, 0);
lean_inc(v_fvarId_767_);
v_params_768_ = lean_ctor_get(v_decl_763_, 2);
lean_inc_ref(v_params_768_);
v_type_769_ = lean_ctor_get(v_decl_763_, 3);
lean_inc_ref(v_type_769_);
v_value_770_ = lean_ctor_get(v_decl_763_, 4);
lean_inc_ref(v_value_770_);
lean_dec_ref(v_decl_763_);
v_fvarId_771_ = lean_ctor_get(v_decl_764_, 0);
lean_inc(v_fvarId_771_);
v_params_772_ = lean_ctor_get(v_decl_764_, 2);
lean_inc_ref(v_params_772_);
v_type_773_ = lean_ctor_get(v_decl_764_, 3);
lean_inc_ref(v_type_773_);
v_value_774_ = lean_ctor_get(v_decl_764_, 4);
lean_inc_ref(v_value_774_);
lean_dec_ref(v_decl_764_);
v___x_775_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_769_, v_type_773_, v_a_717_);
lean_dec_ref(v_type_773_);
lean_dec_ref(v_type_769_);
if (v___x_775_ == 0)
{
lean_dec_ref(v_value_774_);
lean_dec_ref(v_params_772_);
lean_dec(v_fvarId_771_);
lean_dec_ref(v_value_770_);
lean_dec_ref(v_params_768_);
lean_dec(v_fvarId_767_);
lean_dec_ref(v_k_766_);
lean_dec_ref(v_k_765_);
lean_dec(v_a_717_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; uint8_t v___x_778_; 
v___x_776_ = lean_array_get_size(v_params_772_);
v___x_777_ = lean_array_get_size(v_params_768_);
v___x_778_ = lean_nat_dec_eq(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
lean_dec_ref(v_value_774_);
lean_dec_ref(v_params_772_);
lean_dec(v_fvarId_771_);
lean_dec_ref(v_value_770_);
lean_dec_ref(v_params_768_);
lean_dec(v_fvarId_767_);
lean_dec_ref(v_k_766_);
lean_dec_ref(v_k_765_);
lean_dec(v_a_717_);
return v___x_778_;
}
else
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_717_);
v___x_780_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_714_, v_value_770_, v_value_774_, v_params_768_, v_params_772_, v___x_779_, v_a_717_);
lean_dec_ref(v_params_772_);
lean_dec_ref(v_params_768_);
if (v___x_780_ == 0)
{
lean_dec(v_fvarId_771_);
lean_dec(v_fvarId_767_);
lean_dec_ref(v_k_766_);
lean_dec_ref(v_k_765_);
lean_dec(v_a_717_);
return v___x_780_;
}
else
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_771_, v_fvarId_767_, v_a_717_);
v_code_u2081_715_ = v_k_765_;
v_code_u2082_716_ = v_k_766_;
v_a_717_ = v___x_781_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_783_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_783_ = 0;
return v___x_783_;
}
}
case 2:
{
if (lean_obj_tag(v_code_u2082_716_) == 2)
{
lean_object* v_decl_784_; lean_object* v_decl_785_; lean_object* v_k_786_; lean_object* v_k_787_; lean_object* v_fvarId_788_; lean_object* v_params_789_; lean_object* v_type_790_; lean_object* v_value_791_; lean_object* v_fvarId_792_; lean_object* v_params_793_; lean_object* v_type_794_; lean_object* v_value_795_; uint8_t v___x_796_; 
v_decl_784_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc_ref(v_decl_784_);
v_decl_785_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc_ref(v_decl_785_);
v_k_786_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc_ref(v_k_786_);
lean_dec_ref(v_code_u2081_715_);
v_k_787_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc_ref(v_k_787_);
lean_dec_ref(v_code_u2082_716_);
v_fvarId_788_ = lean_ctor_get(v_decl_784_, 0);
lean_inc(v_fvarId_788_);
v_params_789_ = lean_ctor_get(v_decl_784_, 2);
lean_inc_ref(v_params_789_);
v_type_790_ = lean_ctor_get(v_decl_784_, 3);
lean_inc_ref(v_type_790_);
v_value_791_ = lean_ctor_get(v_decl_784_, 4);
lean_inc_ref(v_value_791_);
lean_dec_ref(v_decl_784_);
v_fvarId_792_ = lean_ctor_get(v_decl_785_, 0);
lean_inc(v_fvarId_792_);
v_params_793_ = lean_ctor_get(v_decl_785_, 2);
lean_inc_ref(v_params_793_);
v_type_794_ = lean_ctor_get(v_decl_785_, 3);
lean_inc_ref(v_type_794_);
v_value_795_ = lean_ctor_get(v_decl_785_, 4);
lean_inc_ref(v_value_795_);
lean_dec_ref(v_decl_785_);
v___x_796_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_790_, v_type_794_, v_a_717_);
lean_dec_ref(v_type_794_);
lean_dec_ref(v_type_790_);
if (v___x_796_ == 0)
{
lean_dec_ref(v_value_795_);
lean_dec_ref(v_params_793_);
lean_dec(v_fvarId_792_);
lean_dec_ref(v_value_791_);
lean_dec_ref(v_params_789_);
lean_dec(v_fvarId_788_);
lean_dec_ref(v_k_787_);
lean_dec_ref(v_k_786_);
lean_dec(v_a_717_);
return v___x_796_;
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v___x_797_ = lean_array_get_size(v_params_793_);
v___x_798_ = lean_array_get_size(v_params_789_);
v___x_799_ = lean_nat_dec_eq(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_dec_ref(v_value_795_);
lean_dec_ref(v_params_793_);
lean_dec(v_fvarId_792_);
lean_dec_ref(v_value_791_);
lean_dec_ref(v_params_789_);
lean_dec(v_fvarId_788_);
lean_dec_ref(v_k_787_);
lean_dec_ref(v_k_786_);
lean_dec(v_a_717_);
return v___x_799_;
}
else
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_717_);
v___x_801_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_714_, v_value_791_, v_value_795_, v_params_789_, v_params_793_, v___x_800_, v_a_717_);
lean_dec_ref(v_params_793_);
lean_dec_ref(v_params_789_);
if (v___x_801_ == 0)
{
lean_dec(v_fvarId_792_);
lean_dec(v_fvarId_788_);
lean_dec_ref(v_k_787_);
lean_dec_ref(v_k_786_);
lean_dec(v_a_717_);
return v___x_801_;
}
else
{
lean_object* v___x_802_; 
v___x_802_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_792_, v_fvarId_788_, v_a_717_);
v_code_u2081_715_ = v_k_786_;
v_code_u2082_716_ = v_k_787_;
v_a_717_ = v___x_802_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_804_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_804_ = 0;
return v___x_804_;
}
}
case 3:
{
if (lean_obj_tag(v_code_u2082_716_) == 3)
{
lean_object* v_fvarId_805_; lean_object* v_args_806_; lean_object* v_fvarId_807_; lean_object* v_args_808_; uint8_t v___x_809_; 
v_fvarId_805_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc(v_fvarId_805_);
v_args_806_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc_ref(v_args_806_);
lean_dec_ref(v_code_u2081_715_);
v_fvarId_807_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc(v_fvarId_807_);
v_args_808_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc_ref(v_args_808_);
lean_dec_ref(v_code_u2082_716_);
v___x_809_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_805_, v_fvarId_807_, v_a_717_);
lean_dec(v_fvarId_807_);
lean_dec(v_fvarId_805_);
if (v___x_809_ == 0)
{
lean_dec_ref(v_args_808_);
lean_dec_ref(v_args_806_);
lean_dec(v_a_717_);
return v___x_809_;
}
else
{
uint8_t v___x_810_; 
v___x_810_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_714_, v_args_806_, v_args_808_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_args_806_);
return v___x_810_;
}
}
else
{
uint8_t v___x_811_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_811_ = 0;
return v___x_811_;
}
}
case 4:
{
if (lean_obj_tag(v_code_u2082_716_) == 4)
{
lean_object* v_cases_812_; lean_object* v_cases_813_; lean_object* v_resultType_814_; lean_object* v_discr_815_; lean_object* v_alts_816_; lean_object* v_resultType_817_; lean_object* v_discr_818_; lean_object* v_alts_819_; uint8_t v___x_820_; 
v_cases_812_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc_ref(v_cases_812_);
lean_dec_ref(v_code_u2081_715_);
v_cases_813_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc_ref(v_cases_813_);
lean_dec_ref(v_code_u2082_716_);
v_resultType_814_ = lean_ctor_get(v_cases_812_, 1);
lean_inc_ref(v_resultType_814_);
v_discr_815_ = lean_ctor_get(v_cases_812_, 2);
lean_inc(v_discr_815_);
v_alts_816_ = lean_ctor_get(v_cases_812_, 3);
lean_inc_ref(v_alts_816_);
lean_dec_ref(v_cases_812_);
v_resultType_817_ = lean_ctor_get(v_cases_813_, 1);
lean_inc_ref(v_resultType_817_);
v_discr_818_ = lean_ctor_get(v_cases_813_, 2);
lean_inc(v_discr_818_);
v_alts_819_ = lean_ctor_get(v_cases_813_, 3);
lean_inc_ref(v_alts_819_);
lean_dec_ref(v_cases_813_);
v___x_820_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_discr_815_, v_discr_818_, v_a_717_);
lean_dec(v_discr_818_);
lean_dec(v_discr_815_);
if (v___x_820_ == 0)
{
lean_dec_ref(v_alts_819_);
lean_dec_ref(v_resultType_817_);
lean_dec_ref(v_alts_816_);
lean_dec_ref(v_resultType_814_);
lean_dec(v_a_717_);
return v___x_820_;
}
else
{
uint8_t v___x_821_; 
v___x_821_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_resultType_814_, v_resultType_817_, v_a_717_);
lean_dec_ref(v_resultType_817_);
lean_dec_ref(v_resultType_814_);
if (v___x_821_ == 0)
{
lean_dec_ref(v_alts_819_);
lean_dec_ref(v_alts_816_);
lean_dec(v_a_717_);
return v___x_821_;
}
else
{
uint8_t v___x_822_; 
v___x_822_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_714_, v_alts_816_, v_alts_819_, v_a_717_);
lean_dec(v_a_717_);
return v___x_822_;
}
}
}
else
{
uint8_t v___x_823_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_823_ = 0;
return v___x_823_;
}
}
case 5:
{
if (lean_obj_tag(v_code_u2082_716_) == 5)
{
lean_object* v_fvarId_824_; lean_object* v_fvarId_825_; uint8_t v___x_826_; 
v_fvarId_824_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc(v_fvarId_824_);
lean_dec_ref(v_code_u2081_715_);
v_fvarId_825_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc(v_fvarId_825_);
lean_dec_ref(v_code_u2082_716_);
v___x_826_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_824_, v_fvarId_825_, v_a_717_);
lean_dec(v_a_717_);
lean_dec(v_fvarId_825_);
lean_dec(v_fvarId_824_);
return v___x_826_;
}
else
{
uint8_t v___x_827_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_827_ = 0;
return v___x_827_;
}
}
case 6:
{
if (lean_obj_tag(v_code_u2082_716_) == 6)
{
lean_object* v_type_828_; lean_object* v_type_829_; uint8_t v___x_830_; 
v_type_828_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc_ref(v_type_828_);
lean_dec_ref(v_code_u2081_715_);
v_type_829_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc_ref(v_type_829_);
lean_dec_ref(v_code_u2082_716_);
v___x_830_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_828_, v_type_829_, v_a_717_);
lean_dec(v_a_717_);
lean_dec_ref(v_type_829_);
lean_dec_ref(v_type_828_);
return v___x_830_;
}
else
{
uint8_t v___x_831_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_831_ = 0;
return v___x_831_;
}
}
case 7:
{
if (lean_obj_tag(v_code_u2082_716_) == 7)
{
lean_object* v_fvarId_832_; lean_object* v_i_833_; lean_object* v_y_834_; lean_object* v_k_835_; lean_object* v_fvarId_836_; lean_object* v_i_837_; lean_object* v_y_838_; lean_object* v_k_839_; uint8_t v___x_840_; 
v_fvarId_832_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc(v_fvarId_832_);
v_i_833_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc(v_i_833_);
v_y_834_ = lean_ctor_get(v_code_u2081_715_, 2);
lean_inc(v_y_834_);
v_k_835_ = lean_ctor_get(v_code_u2081_715_, 3);
lean_inc_ref(v_k_835_);
lean_dec_ref(v_code_u2081_715_);
v_fvarId_836_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc(v_fvarId_836_);
v_i_837_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc(v_i_837_);
v_y_838_ = lean_ctor_get(v_code_u2082_716_, 2);
lean_inc(v_y_838_);
v_k_839_ = lean_ctor_get(v_code_u2082_716_, 3);
lean_inc_ref(v_k_839_);
lean_dec_ref(v_code_u2082_716_);
v___x_840_ = lean_nat_dec_eq(v_i_833_, v_i_837_);
lean_dec(v_i_837_);
lean_dec(v_i_833_);
if (v___x_840_ == 0)
{
lean_dec_ref(v_k_839_);
lean_dec(v_y_838_);
lean_dec(v_fvarId_836_);
lean_dec_ref(v_k_835_);
lean_dec(v_y_834_);
lean_dec(v_fvarId_832_);
lean_dec(v_a_717_);
return v___x_840_;
}
else
{
uint8_t v___x_841_; 
v___x_841_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_832_, v_fvarId_836_, v_a_717_);
lean_dec(v_fvarId_836_);
lean_dec(v_fvarId_832_);
if (v___x_841_ == 0)
{
lean_dec_ref(v_k_839_);
lean_dec(v_y_838_);
lean_dec_ref(v_k_835_);
lean_dec(v_y_834_);
lean_dec(v_a_717_);
return v___x_841_;
}
else
{
uint8_t v___x_842_; 
v___x_842_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_y_834_, v_y_838_, v_a_717_);
lean_dec(v_y_838_);
lean_dec(v_y_834_);
if (v___x_842_ == 0)
{
lean_dec_ref(v_k_839_);
lean_dec_ref(v_k_835_);
lean_dec(v_a_717_);
return v___x_842_;
}
else
{
v_code_u2081_715_ = v_k_835_;
v_code_u2082_716_ = v_k_839_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_844_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_844_ = 0;
return v___x_844_;
}
}
case 8:
{
if (lean_obj_tag(v_code_u2082_716_) == 8)
{
lean_object* v_fvarId_845_; lean_object* v_i_846_; lean_object* v_y_847_; lean_object* v_k_848_; lean_object* v_fvarId_849_; lean_object* v_i_850_; lean_object* v_y_851_; lean_object* v_k_852_; uint8_t v___x_853_; 
v_fvarId_845_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc(v_fvarId_845_);
v_i_846_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc(v_i_846_);
v_y_847_ = lean_ctor_get(v_code_u2081_715_, 2);
lean_inc(v_y_847_);
v_k_848_ = lean_ctor_get(v_code_u2081_715_, 3);
lean_inc_ref(v_k_848_);
lean_dec_ref(v_code_u2081_715_);
v_fvarId_849_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc(v_fvarId_849_);
v_i_850_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc(v_i_850_);
v_y_851_ = lean_ctor_get(v_code_u2082_716_, 2);
lean_inc(v_y_851_);
v_k_852_ = lean_ctor_get(v_code_u2082_716_, 3);
lean_inc_ref(v_k_852_);
lean_dec_ref(v_code_u2082_716_);
v___x_853_ = lean_nat_dec_eq(v_i_846_, v_i_850_);
lean_dec(v_i_850_);
lean_dec(v_i_846_);
if (v___x_853_ == 0)
{
lean_dec_ref(v_k_852_);
lean_dec(v_y_851_);
lean_dec(v_fvarId_849_);
lean_dec_ref(v_k_848_);
lean_dec(v_y_847_);
lean_dec(v_fvarId_845_);
lean_dec(v_a_717_);
return v___x_853_;
}
else
{
uint8_t v___x_854_; 
v___x_854_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_845_, v_fvarId_849_, v_a_717_);
lean_dec(v_fvarId_849_);
lean_dec(v_fvarId_845_);
if (v___x_854_ == 0)
{
lean_dec_ref(v_k_852_);
lean_dec(v_y_851_);
lean_dec_ref(v_k_848_);
lean_dec(v_y_847_);
lean_dec(v_a_717_);
return v___x_854_;
}
else
{
uint8_t v___x_855_; 
v___x_855_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_847_, v_y_851_, v_a_717_);
lean_dec(v_y_851_);
lean_dec(v_y_847_);
if (v___x_855_ == 0)
{
lean_dec_ref(v_k_852_);
lean_dec_ref(v_k_848_);
lean_dec(v_a_717_);
return v___x_855_;
}
else
{
v_code_u2081_715_ = v_k_848_;
v_code_u2082_716_ = v_k_852_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_857_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_857_ = 0;
return v___x_857_;
}
}
case 9:
{
if (lean_obj_tag(v_code_u2082_716_) == 9)
{
lean_object* v_fvarId_858_; lean_object* v_i_859_; lean_object* v_offset_860_; lean_object* v_y_861_; lean_object* v_ty_862_; lean_object* v_k_863_; lean_object* v_fvarId_864_; lean_object* v_i_865_; lean_object* v_offset_866_; lean_object* v_y_867_; lean_object* v_ty_868_; lean_object* v_k_869_; uint8_t v___x_870_; 
v_fvarId_858_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc(v_fvarId_858_);
v_i_859_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc(v_i_859_);
v_offset_860_ = lean_ctor_get(v_code_u2081_715_, 2);
lean_inc(v_offset_860_);
v_y_861_ = lean_ctor_get(v_code_u2081_715_, 3);
lean_inc(v_y_861_);
v_ty_862_ = lean_ctor_get(v_code_u2081_715_, 4);
lean_inc_ref(v_ty_862_);
v_k_863_ = lean_ctor_get(v_code_u2081_715_, 5);
lean_inc_ref(v_k_863_);
lean_dec_ref(v_code_u2081_715_);
v_fvarId_864_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc(v_fvarId_864_);
v_i_865_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc(v_i_865_);
v_offset_866_ = lean_ctor_get(v_code_u2082_716_, 2);
lean_inc(v_offset_866_);
v_y_867_ = lean_ctor_get(v_code_u2082_716_, 3);
lean_inc(v_y_867_);
v_ty_868_ = lean_ctor_get(v_code_u2082_716_, 4);
lean_inc_ref(v_ty_868_);
v_k_869_ = lean_ctor_get(v_code_u2082_716_, 5);
lean_inc_ref(v_k_869_);
lean_dec_ref(v_code_u2082_716_);
v___x_870_ = lean_nat_dec_eq(v_i_859_, v_i_865_);
lean_dec(v_i_865_);
lean_dec(v_i_859_);
if (v___x_870_ == 0)
{
lean_dec_ref(v_k_869_);
lean_dec_ref(v_ty_868_);
lean_dec(v_y_867_);
lean_dec(v_offset_866_);
lean_dec(v_fvarId_864_);
lean_dec_ref(v_k_863_);
lean_dec_ref(v_ty_862_);
lean_dec(v_y_861_);
lean_dec(v_offset_860_);
lean_dec(v_fvarId_858_);
lean_dec(v_a_717_);
return v___x_870_;
}
else
{
uint8_t v___x_871_; 
v___x_871_ = lean_nat_dec_eq(v_offset_860_, v_offset_866_);
lean_dec(v_offset_866_);
lean_dec(v_offset_860_);
if (v___x_871_ == 0)
{
lean_dec_ref(v_k_869_);
lean_dec_ref(v_ty_868_);
lean_dec(v_y_867_);
lean_dec(v_fvarId_864_);
lean_dec_ref(v_k_863_);
lean_dec_ref(v_ty_862_);
lean_dec(v_y_861_);
lean_dec(v_fvarId_858_);
lean_dec(v_a_717_);
return v___x_871_;
}
else
{
uint8_t v___x_872_; 
v___x_872_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_858_, v_fvarId_864_, v_a_717_);
lean_dec(v_fvarId_864_);
lean_dec(v_fvarId_858_);
if (v___x_872_ == 0)
{
lean_dec_ref(v_k_869_);
lean_dec_ref(v_ty_868_);
lean_dec(v_y_867_);
lean_dec_ref(v_k_863_);
lean_dec_ref(v_ty_862_);
lean_dec(v_y_861_);
lean_dec(v_a_717_);
return v___x_872_;
}
else
{
uint8_t v___x_873_; 
v___x_873_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_861_, v_y_867_, v_a_717_);
lean_dec(v_y_867_);
lean_dec(v_y_861_);
if (v___x_873_ == 0)
{
lean_dec_ref(v_k_869_);
lean_dec_ref(v_ty_868_);
lean_dec_ref(v_k_863_);
lean_dec_ref(v_ty_862_);
lean_dec(v_a_717_);
return v___x_873_;
}
else
{
uint8_t v___x_874_; 
v___x_874_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_862_, v_ty_868_, v_a_717_);
lean_dec_ref(v_ty_868_);
lean_dec_ref(v_ty_862_);
if (v___x_874_ == 0)
{
lean_dec_ref(v_k_869_);
lean_dec_ref(v_k_863_);
lean_dec(v_a_717_);
return v___x_874_;
}
else
{
v_code_u2081_715_ = v_k_863_;
v_code_u2082_716_ = v_k_869_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_876_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_876_ = 0;
return v___x_876_;
}
}
case 10:
{
if (lean_obj_tag(v_code_u2082_716_) == 10)
{
lean_object* v_fvarId_877_; lean_object* v_cidx_878_; lean_object* v_k_879_; lean_object* v_fvarId_880_; lean_object* v_cidx_881_; lean_object* v_k_882_; uint8_t v___x_883_; 
v_fvarId_877_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc(v_fvarId_877_);
v_cidx_878_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc(v_cidx_878_);
v_k_879_ = lean_ctor_get(v_code_u2081_715_, 2);
lean_inc_ref(v_k_879_);
lean_dec_ref(v_code_u2081_715_);
v_fvarId_880_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc(v_fvarId_880_);
v_cidx_881_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc(v_cidx_881_);
v_k_882_ = lean_ctor_get(v_code_u2082_716_, 2);
lean_inc_ref(v_k_882_);
lean_dec_ref(v_code_u2082_716_);
v___x_883_ = lean_nat_dec_eq(v_cidx_878_, v_cidx_881_);
lean_dec(v_cidx_881_);
lean_dec(v_cidx_878_);
if (v___x_883_ == 0)
{
lean_dec_ref(v_k_882_);
lean_dec(v_fvarId_880_);
lean_dec_ref(v_k_879_);
lean_dec(v_fvarId_877_);
lean_dec(v_a_717_);
return v___x_883_;
}
else
{
uint8_t v___x_884_; 
v___x_884_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_877_, v_fvarId_880_, v_a_717_);
lean_dec(v_fvarId_880_);
lean_dec(v_fvarId_877_);
if (v___x_884_ == 0)
{
lean_dec_ref(v_k_882_);
lean_dec_ref(v_k_879_);
lean_dec(v_a_717_);
return v___x_884_;
}
else
{
v_code_u2081_715_ = v_k_879_;
v_code_u2082_716_ = v_k_882_;
goto _start;
}
}
}
else
{
uint8_t v___x_886_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_886_ = 0;
return v___x_886_;
}
}
case 11:
{
if (lean_obj_tag(v_code_u2082_716_) == 11)
{
lean_object* v_fvarId_887_; lean_object* v_n_888_; uint8_t v_check_889_; uint8_t v_persistent_890_; lean_object* v_k_891_; lean_object* v_fvarId_892_; lean_object* v_n_893_; uint8_t v_check_894_; uint8_t v_persistent_895_; lean_object* v_k_896_; 
v_fvarId_887_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc(v_fvarId_887_);
v_n_888_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc(v_n_888_);
v_check_889_ = lean_ctor_get_uint8(v_code_u2081_715_, sizeof(void*)*3);
v_persistent_890_ = lean_ctor_get_uint8(v_code_u2081_715_, sizeof(void*)*3 + 1);
v_k_891_ = lean_ctor_get(v_code_u2081_715_, 2);
lean_inc_ref(v_k_891_);
lean_dec_ref(v_code_u2081_715_);
v_fvarId_892_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc(v_fvarId_892_);
v_n_893_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc(v_n_893_);
v_check_894_ = lean_ctor_get_uint8(v_code_u2082_716_, sizeof(void*)*3);
v_persistent_895_ = lean_ctor_get_uint8(v_code_u2082_716_, sizeof(void*)*3 + 1);
v_k_896_ = lean_ctor_get(v_code_u2082_716_, 2);
lean_inc_ref(v_k_896_);
lean_dec_ref(v_code_u2082_716_);
v_fvarId_u2081_736_ = v_fvarId_887_;
v_n_u2081_737_ = v_n_888_;
v_c_u2081_738_ = v_check_889_;
v_p_u2081_739_ = v_persistent_890_;
v_k_u2081_740_ = v_k_891_;
v_fvarId_u2082_741_ = v_fvarId_892_;
v_n_u2082_742_ = v_n_893_;
v_c_u2082_743_ = v_check_894_;
v_p_u2082_744_ = v_persistent_895_;
v_k_u2082_745_ = v_k_896_;
v___y_746_ = v_a_717_;
goto v___jp_735_;
}
else
{
uint8_t v___x_897_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_897_ = 0;
return v___x_897_;
}
}
case 12:
{
if (lean_obj_tag(v_code_u2082_716_) == 12)
{
lean_object* v_fvarId_898_; lean_object* v_n_899_; uint8_t v_check_900_; uint8_t v_persistent_901_; lean_object* v_k_902_; lean_object* v_fvarId_903_; lean_object* v_n_904_; uint8_t v_check_905_; uint8_t v_persistent_906_; lean_object* v_k_907_; 
v_fvarId_898_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc(v_fvarId_898_);
v_n_899_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc(v_n_899_);
v_check_900_ = lean_ctor_get_uint8(v_code_u2081_715_, sizeof(void*)*3);
v_persistent_901_ = lean_ctor_get_uint8(v_code_u2081_715_, sizeof(void*)*3 + 1);
v_k_902_ = lean_ctor_get(v_code_u2081_715_, 2);
lean_inc_ref(v_k_902_);
lean_dec_ref(v_code_u2081_715_);
v_fvarId_903_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc(v_fvarId_903_);
v_n_904_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc(v_n_904_);
v_check_905_ = lean_ctor_get_uint8(v_code_u2082_716_, sizeof(void*)*3);
v_persistent_906_ = lean_ctor_get_uint8(v_code_u2082_716_, sizeof(void*)*3 + 1);
v_k_907_ = lean_ctor_get(v_code_u2082_716_, 2);
lean_inc_ref(v_k_907_);
lean_dec_ref(v_code_u2082_716_);
v_fvarId_u2081_736_ = v_fvarId_898_;
v_n_u2081_737_ = v_n_899_;
v_c_u2081_738_ = v_check_900_;
v_p_u2081_739_ = v_persistent_901_;
v_k_u2081_740_ = v_k_902_;
v_fvarId_u2082_741_ = v_fvarId_903_;
v_n_u2082_742_ = v_n_904_;
v_c_u2082_743_ = v_check_905_;
v_p_u2082_744_ = v_persistent_906_;
v_k_u2082_745_ = v_k_907_;
v___y_746_ = v_a_717_;
goto v___jp_735_;
}
else
{
uint8_t v___x_908_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_908_ = 0;
return v___x_908_;
}
}
default: 
{
if (lean_obj_tag(v_code_u2082_716_) == 13)
{
lean_object* v_fvarId_909_; lean_object* v_k_910_; lean_object* v_fvarId_911_; lean_object* v_k_912_; uint8_t v___x_913_; 
v_fvarId_909_ = lean_ctor_get(v_code_u2081_715_, 0);
lean_inc(v_fvarId_909_);
v_k_910_ = lean_ctor_get(v_code_u2081_715_, 1);
lean_inc_ref(v_k_910_);
lean_dec_ref(v_code_u2081_715_);
v_fvarId_911_ = lean_ctor_get(v_code_u2082_716_, 0);
lean_inc(v_fvarId_911_);
v_k_912_ = lean_ctor_get(v_code_u2082_716_, 1);
lean_inc_ref(v_k_912_);
lean_dec_ref(v_code_u2082_716_);
v___x_913_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_909_, v_fvarId_911_, v_a_717_);
lean_dec(v_fvarId_911_);
lean_dec(v_fvarId_909_);
if (v___x_913_ == 0)
{
lean_dec_ref(v_k_912_);
lean_dec_ref(v_k_910_);
lean_dec(v_a_717_);
return v___x_913_;
}
else
{
v_code_u2081_715_ = v_k_910_;
v_code_u2082_716_ = v_k_912_;
goto _start;
}
}
else
{
uint8_t v___x_915_; 
lean_dec_ref(v_code_u2081_715_);
lean_dec(v_a_717_);
lean_dec_ref(v_code_u2082_716_);
v___x_915_ = 0;
return v___x_915_;
}
}
}
v___jp_718_:
{
uint8_t v___x_724_; 
v___x_724_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v___y_720_, v___y_723_, v___y_721_);
lean_dec(v___y_723_);
lean_dec(v___y_720_);
if (v___x_724_ == 0)
{
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_719_);
return v___x_724_;
}
else
{
v_code_u2081_715_ = v___y_722_;
v_code_u2082_716_ = v___y_719_;
v_a_717_ = v___y_721_;
goto _start;
}
}
v___jp_726_:
{
if (v___y_734_ == 0)
{
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v___y_734_;
}
else
{
if (v___y_733_ == 0)
{
if (v___y_727_ == 0)
{
v___y_719_ = v___y_728_;
v___y_720_ = v___y_729_;
v___y_721_ = v___y_730_;
v___y_722_ = v___y_731_;
v___y_723_ = v___y_732_;
goto v___jp_718_;
}
else
{
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v___y_733_;
}
}
else
{
if (v___y_727_ == 0)
{
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
return v___y_727_;
}
else
{
v___y_719_ = v___y_728_;
v___y_720_ = v___y_729_;
v___y_721_ = v___y_730_;
v___y_722_ = v___y_731_;
v___y_723_ = v___y_732_;
goto v___jp_718_;
}
}
}
}
v___jp_735_:
{
uint8_t v___x_747_; 
v___x_747_ = lean_nat_dec_eq(v_n_u2081_737_, v_n_u2082_742_);
lean_dec(v_n_u2082_742_);
lean_dec(v_n_u2081_737_);
if (v___x_747_ == 0)
{
lean_dec(v___y_746_);
lean_dec_ref(v_k_u2082_745_);
lean_dec(v_fvarId_u2082_741_);
lean_dec_ref(v_k_u2081_740_);
lean_dec(v_fvarId_u2081_736_);
return v___x_747_;
}
else
{
if (v_c_u2081_738_ == 0)
{
if (v_c_u2082_743_ == 0)
{
v___y_727_ = v_p_u2082_744_;
v___y_728_ = v_k_u2082_745_;
v___y_729_ = v_fvarId_u2081_736_;
v___y_730_ = v___y_746_;
v___y_731_ = v_k_u2081_740_;
v___y_732_ = v_fvarId_u2082_741_;
v___y_733_ = v_p_u2081_739_;
v___y_734_ = v___x_747_;
goto v___jp_726_;
}
else
{
lean_dec(v___y_746_);
lean_dec_ref(v_k_u2082_745_);
lean_dec(v_fvarId_u2082_741_);
lean_dec_ref(v_k_u2081_740_);
lean_dec(v_fvarId_u2081_736_);
return v_c_u2081_738_;
}
}
else
{
v___y_727_ = v_p_u2082_744_;
v___y_728_ = v_k_u2082_745_;
v___y_729_ = v_fvarId_u2081_736_;
v___y_730_ = v___y_746_;
v___y_731_ = v_k_u2081_740_;
v___y_732_ = v_fvarId_u2082_741_;
v___y_733_ = v_p_u2081_739_;
v___y_734_ = v_c_u2082_743_;
goto v___jp_726_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(uint8_t v_pu_916_, lean_object* v_code_917_, lean_object* v_code_918_, lean_object* v_params_u2081_919_, lean_object* v_params_u2082_920_, lean_object* v_i_921_, lean_object* v_a_922_){
_start:
{
lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_923_ = lean_array_get_size(v_params_u2081_919_);
v___x_924_ = lean_nat_dec_lt(v_i_921_, v___x_923_);
if (v___x_924_ == 0)
{
uint8_t v___x_925_; 
lean_dec(v_i_921_);
v___x_925_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_916_, v_code_917_, v_code_918_, v_a_922_);
return v___x_925_;
}
else
{
lean_object* v_p_u2081_926_; lean_object* v_fvarId_927_; lean_object* v_type_928_; lean_object* v_p_u2082_929_; lean_object* v_fvarId_930_; lean_object* v_type_931_; uint8_t v___x_932_; 
v_p_u2081_926_ = lean_array_fget_borrowed(v_params_u2081_919_, v_i_921_);
v_fvarId_927_ = lean_ctor_get(v_p_u2081_926_, 0);
v_type_928_ = lean_ctor_get(v_p_u2081_926_, 2);
v_p_u2082_929_ = lean_array_fget_borrowed(v_params_u2082_920_, v_i_921_);
v_fvarId_930_ = lean_ctor_get(v_p_u2082_929_, 0);
v_type_931_ = lean_ctor_get(v_p_u2082_929_, 2);
v___x_932_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_928_, v_type_931_, v_a_922_);
if (v___x_932_ == 0)
{
lean_dec(v_a_922_);
lean_dec(v_i_921_);
lean_dec_ref(v_code_918_);
lean_dec_ref(v_code_917_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_933_ = lean_unsigned_to_nat(1u);
v___x_934_ = lean_nat_add(v_i_921_, v___x_933_);
lean_dec(v_i_921_);
lean_inc(v_fvarId_927_);
lean_inc(v_fvarId_930_);
v___x_935_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_930_, v_fvarId_927_, v_a_922_);
v_i_921_ = v___x_934_;
v_a_922_ = v___x_935_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg___boxed(lean_object* v_pu_937_, lean_object* v_code_938_, lean_object* v_code_939_, lean_object* v_params_u2081_940_, lean_object* v_params_u2082_941_, lean_object* v_i_942_, lean_object* v_a_943_){
_start:
{
uint8_t v_pu_boxed_944_; uint8_t v_res_945_; lean_object* v_r_946_; 
v_pu_boxed_944_ = lean_unbox(v_pu_937_);
v_res_945_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_boxed_944_, v_code_938_, v_code_939_, v_params_u2081_940_, v_params_u2082_941_, v_i_942_, v_a_943_);
lean_dec_ref(v_params_u2082_941_);
lean_dec_ref(v_params_u2081_940_);
v_r_946_ = lean_box(v_res_945_);
return v_r_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts___boxed(lean_object* v_pu_947_, lean_object* v_alts_u2081_948_, lean_object* v_alts_u2082_949_, lean_object* v_a_950_){
_start:
{
uint8_t v_pu_boxed_951_; uint8_t v_res_952_; lean_object* v_r_953_; 
v_pu_boxed_951_ = lean_unbox(v_pu_947_);
v_res_952_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_boxed_951_, v_alts_u2081_948_, v_alts_u2082_949_, v_a_950_);
lean_dec(v_a_950_);
v_r_953_ = lean_box(v_res_952_);
return v_r_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___boxed(lean_object* v_pu_954_, lean_object* v_as_955_, lean_object* v_sz_956_, lean_object* v_i_957_, lean_object* v_b_958_, lean_object* v___y_959_){
_start:
{
uint8_t v_pu_boxed_960_; size_t v_sz_boxed_961_; size_t v_i_boxed_962_; lean_object* v_res_963_; 
v_pu_boxed_960_ = lean_unbox(v_pu_954_);
v_sz_boxed_961_ = lean_unbox_usize(v_sz_956_);
lean_dec(v_sz_956_);
v_i_boxed_962_ = lean_unbox_usize(v_i_957_);
lean_dec(v_i_957_);
v_res_963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_boxed_960_, v_as_955_, v_sz_boxed_961_, v_i_boxed_962_, v_b_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v_as_955_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqv___boxed(lean_object* v_pu_964_, lean_object* v_code_u2081_965_, lean_object* v_code_u2082_966_, lean_object* v_a_967_){
_start:
{
uint8_t v_pu_boxed_968_; uint8_t v_res_969_; lean_object* v_r_970_; 
v_pu_boxed_968_ = lean_unbox(v_pu_964_);
v_res_969_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_boxed_968_, v_code_u2081_965_, v_code_u2082_966_, v_a_967_);
v_r_970_ = lean_box(v_res_969_);
return v_r_970_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(uint8_t v_pu_971_, lean_object* v_code_972_, lean_object* v_code_973_, uint8_t v_pu_974_, lean_object* v_params_u2081_975_, lean_object* v_params_u2082_976_, lean_object* v_h_977_, lean_object* v_i_978_, lean_object* v_a_979_){
_start:
{
uint8_t v___x_980_; 
lean_inc(v_a_979_);
v___x_980_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_971_, v_code_972_, v_code_973_, v_params_u2081_975_, v_params_u2082_976_, v_i_978_, v_a_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___boxed(lean_object* v_pu_981_, lean_object* v_code_982_, lean_object* v_code_983_, lean_object* v_pu_984_, lean_object* v_params_u2081_985_, lean_object* v_params_u2082_986_, lean_object* v_h_987_, lean_object* v_i_988_, lean_object* v_a_989_){
_start:
{
uint8_t v_pu_boxed_990_; uint8_t v_pu_boxed_991_; uint8_t v_res_992_; lean_object* v_r_993_; 
v_pu_boxed_990_ = lean_unbox(v_pu_981_);
v_pu_boxed_991_ = lean_unbox(v_pu_984_);
v_res_992_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(v_pu_boxed_990_, v_code_982_, v_code_983_, v_pu_boxed_991_, v_params_u2081_985_, v_params_u2082_986_, v_h_987_, v_i_988_, v_a_989_);
lean_dec(v_a_989_);
lean_dec_ref(v_params_u2082_986_);
lean_dec_ref(v_params_u2081_985_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t v_pu_994_, lean_object* v_c_u2081_995_, lean_object* v_c_u2082_996_){
_start:
{
lean_object* v___x_997_; uint8_t v___x_998_; 
v___x_997_ = lean_box(1);
v___x_998_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_994_, v_c_u2081_995_, v_c_u2082_996_, v___x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_alphaEqv___boxed(lean_object* v_pu_999_, lean_object* v_c_u2081_1000_, lean_object* v_c_u2082_1001_){
_start:
{
uint8_t v_pu_boxed_1002_; uint8_t v_res_1003_; lean_object* v_r_1004_; 
v_pu_boxed_1002_ = lean_unbox(v_pu_999_);
v_res_1003_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v_pu_boxed_1002_, v_c_u2081_1000_, v_c_u2082_1001_);
v_r_1004_ = lean_box(v_res_1003_);
return v_r_1004_;
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
