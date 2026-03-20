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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_418_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_u2082_415_, v_fvarId_u2081_414_, v_a_417_);
v___x_419_ = lean_apply_1(v_x_416_, v___x_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withFVar(lean_object* v_00_u03b1_420_, lean_object* v_fvarId_u2081_421_, lean_object* v_fvarId_u2082_422_, lean_object* v_x_423_, lean_object* v_a_424_){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_u2082_422_, v_fvarId_u2081_421_, v_a_424_);
v___x_426_ = lean_apply_1(v_x_423_, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(lean_object* v_params_u2081_427_, lean_object* v_params_u2082_428_, lean_object* v_x_429_, lean_object* v_i_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = lean_array_get_size(v_params_u2081_427_);
v___x_433_ = lean_nat_dec_lt(v_i_430_, v___x_432_);
if (v___x_433_ == 0)
{
lean_object* v___x_434_; uint8_t v___x_435_; 
lean_dec(v_i_430_);
v___x_434_ = lean_apply_1(v_x_429_, v_a_431_);
v___x_435_ = lean_unbox(v___x_434_);
return v___x_435_;
}
else
{
lean_object* v_p_u2081_436_; lean_object* v_fvarId_437_; lean_object* v_type_438_; lean_object* v_p_u2082_439_; lean_object* v_fvarId_440_; lean_object* v_type_441_; uint8_t v___x_442_; 
v_p_u2081_436_ = lean_array_fget_borrowed(v_params_u2081_427_, v_i_430_);
v_fvarId_437_ = lean_ctor_get(v_p_u2081_436_, 0);
v_type_438_ = lean_ctor_get(v_p_u2081_436_, 2);
v_p_u2082_439_ = lean_array_fget_borrowed(v_params_u2082_428_, v_i_430_);
v_fvarId_440_ = lean_ctor_get(v_p_u2082_439_, 0);
v_type_441_ = lean_ctor_get(v_p_u2082_439_, 2);
v___x_442_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_438_, v_type_441_, v_a_431_);
if (v___x_442_ == 0)
{
lean_dec(v_a_431_);
lean_dec(v_i_430_);
lean_dec_ref(v_x_429_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = lean_nat_add(v_i_430_, v___x_443_);
lean_dec(v_i_430_);
lean_inc(v_fvarId_437_);
lean_inc(v_fvarId_440_);
v___x_445_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_440_, v_fvarId_437_, v_a_431_);
v_i_430_ = v___x_444_;
v_a_431_ = v___x_445_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg___boxed(lean_object* v_params_u2081_447_, lean_object* v_params_u2082_448_, lean_object* v_x_449_, lean_object* v_i_450_, lean_object* v_a_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_447_, v_params_u2082_448_, v_x_449_, v_i_450_, v_a_451_);
lean_dec_ref(v_params_u2082_448_);
lean_dec_ref(v_params_u2081_447_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(uint8_t v_pu_454_, lean_object* v_params_u2081_455_, lean_object* v_params_u2082_456_, lean_object* v_x_457_, lean_object* v_h_458_, lean_object* v_i_459_, lean_object* v_a_460_){
_start:
{
uint8_t v___x_461_; 
v___x_461_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_455_, v_params_u2082_456_, v_x_457_, v_i_459_, v_a_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___boxed(lean_object* v_pu_462_, lean_object* v_params_u2081_463_, lean_object* v_params_u2082_464_, lean_object* v_x_465_, lean_object* v_h_466_, lean_object* v_i_467_, lean_object* v_a_468_){
_start:
{
uint8_t v_pu_boxed_469_; uint8_t v_res_470_; lean_object* v_r_471_; 
v_pu_boxed_469_ = lean_unbox(v_pu_462_);
v_res_470_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go(v_pu_boxed_469_, v_params_u2081_463_, v_params_u2082_464_, v_x_465_, v_h_466_, v_i_467_, v_a_468_);
lean_dec_ref(v_params_u2082_464_);
lean_dec_ref(v_params_u2081_463_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(lean_object* v_params_u2081_472_, lean_object* v_params_u2082_473_, lean_object* v_x_474_, lean_object* v_a_475_){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_476_ = lean_array_get_size(v_params_u2082_473_);
v___x_477_ = lean_array_get_size(v_params_u2081_472_);
v___x_478_ = lean_nat_dec_eq(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_dec(v_a_475_);
lean_dec_ref(v_x_474_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; uint8_t v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_472_, v_params_u2082_473_, v_x_474_, v___x_479_, v_a_475_);
return v___x_480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg___boxed(lean_object* v_params_u2081_481_, lean_object* v_params_u2082_482_, lean_object* v_x_483_, lean_object* v_a_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams___redArg(v_params_u2081_481_, v_params_u2082_482_, v_x_483_, v_a_484_);
lean_dec_ref(v_params_u2082_482_);
lean_dec_ref(v_params_u2081_481_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_withParams(uint8_t v_pu_487_, lean_object* v_params_u2081_488_, lean_object* v_params_u2082_489_, lean_object* v_x_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_492_ = lean_array_get_size(v_params_u2082_489_);
v___x_493_ = lean_array_get_size(v_params_u2081_488_);
v___x_494_ = lean_nat_dec_eq(v___x_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v_a_491_);
lean_dec_ref(v_x_490_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v___x_496_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___redArg(v_params_u2081_488_, v_params_u2082_489_, v_x_490_, v___x_495_, v_a_491_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_withParams___boxed(lean_object* v_pu_497_, lean_object* v_params_u2081_498_, lean_object* v_params_u2082_499_, lean_object* v_x_500_, lean_object* v_a_501_){
_start:
{
uint8_t v_pu_boxed_502_; uint8_t v_res_503_; lean_object* v_r_504_; 
v_pu_boxed_502_ = lean_unbox(v_pu_497_);
v_res_503_ = l_Lean_Compiler_LCNF_AlphaEqv_withParams(v_pu_boxed_502_, v_params_u2081_498_, v_params_u2082_499_, v_x_500_, v_a_501_);
lean_dec_ref(v_params_u2082_499_);
lean_dec_ref(v_params_u2081_498_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(uint8_t v___x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
switch(lean_obj_tag(v_x_506_))
{
case 0:
{
switch(lean_obj_tag(v_x_507_))
{
case 2:
{
return v___x_505_;
}
case 0:
{
lean_object* v_ctorName_508_; lean_object* v_ctorName_509_; uint8_t v___x_510_; 
v_ctorName_508_ = lean_ctor_get(v_x_506_, 0);
v_ctorName_509_ = lean_ctor_get(v_x_507_, 0);
v___x_510_ = l_Lean_Name_lt(v_ctorName_508_, v_ctorName_509_);
return v___x_510_;
}
default: 
{
uint8_t v___x_511_; 
v___x_511_ = 0;
return v___x_511_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_507_))
{
case 2:
{
return v___x_505_;
}
case 1:
{
lean_object* v_info_512_; lean_object* v_info_513_; lean_object* v_name_514_; lean_object* v_name_515_; uint8_t v___x_516_; 
v_info_512_ = lean_ctor_get(v_x_506_, 0);
v_info_513_ = lean_ctor_get(v_x_507_, 0);
v_name_514_ = lean_ctor_get(v_info_512_, 0);
v_name_515_ = lean_ctor_get(v_info_513_, 0);
v___x_516_ = l_Lean_Name_lt(v_name_514_, v_name_515_);
return v___x_516_;
}
default: 
{
uint8_t v___x_517_; 
v___x_517_ = 0;
return v___x_517_;
}
}
}
default: 
{
uint8_t v___x_518_; 
v___x_518_ = 0;
return v___x_518_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed(lean_object* v___x_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
uint8_t v___x_223__boxed_522_; uint8_t v_res_523_; lean_object* v_r_524_; 
v___x_223__boxed_522_ = lean_unbox(v___x_519_);
v_res_523_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0(v___x_223__boxed_522_, v_x_520_, v_x_521_);
lean_dec_ref(v_x_521_);
lean_dec_ref(v_x_520_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(lean_object* v_as_525_, lean_object* v_lo_526_, lean_object* v_hi_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_nat_dec_lt(v_lo_526_, v_hi_527_);
if (v___x_528_ == 0)
{
lean_dec(v_lo_526_);
return v_as_525_;
}
else
{
lean_object* v___x_529_; lean_object* v___f_530_; lean_object* v___x_531_; lean_object* v_fst_532_; lean_object* v_snd_533_; uint8_t v___x_534_; 
v___x_529_ = lean_box(v___x_528_);
v___f_530_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_530_, 0, v___x_529_);
lean_inc(v_lo_526_);
v___x_531_ = l_Array_qpartition___redArg(v_as_525_, v___f_530_, v_lo_526_, v_hi_527_);
v_fst_532_ = lean_ctor_get(v___x_531_, 0);
lean_inc(v_fst_532_);
v_snd_533_ = lean_ctor_get(v___x_531_, 1);
lean_inc(v_snd_533_);
lean_dec_ref(v___x_531_);
v___x_534_ = lean_nat_dec_le(v_hi_527_, v_fst_532_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_535_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_snd_533_, v_lo_526_, v_fst_532_);
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_add(v_fst_532_, v___x_536_);
lean_dec(v_fst_532_);
v_as_525_ = v___x_535_;
v_lo_526_ = v___x_537_;
goto _start;
}
else
{
lean_dec(v_fst_532_);
lean_dec(v_lo_526_);
return v_snd_533_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg___boxed(lean_object* v_as_539_, lean_object* v_lo_540_, lean_object* v_hi_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_as_539_, v_lo_540_, v_hi_541_);
lean_dec(v_hi_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(lean_object* v_alts_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_544_ = lean_array_get_size(v_alts_543_);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_nat_dec_eq(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___y_550_; uint8_t v___x_554_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_sub(v___x_544_, v___x_547_);
v___x_554_ = lean_nat_dec_le(v___x_545_, v___x_548_);
if (v___x_554_ == 0)
{
lean_inc(v___x_548_);
v___y_550_ = v___x_548_;
goto v___jp_549_;
}
else
{
v___y_550_ = v___x_545_;
goto v___jp_549_;
}
v___jp_549_:
{
uint8_t v___x_551_; 
v___x_551_ = lean_nat_dec_le(v___y_550_, v___x_548_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; 
lean_dec(v___x_548_);
lean_inc(v___y_550_);
v___x_552_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_alts_543_, v___y_550_, v___y_550_);
lean_dec(v___y_550_);
return v___x_552_;
}
else
{
lean_object* v___x_553_; 
v___x_553_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_alts_543_, v___y_550_, v___x_548_);
lean_dec(v___x_548_);
return v___x_553_;
}
}
}
else
{
return v_alts_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(uint8_t v_pu_555_, lean_object* v_alts_556_){
_start:
{
lean_object* v___x_557_; 
v___x_557_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_556_);
return v___x_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___boxed(lean_object* v_pu_558_, lean_object* v_alts_559_){
_start:
{
uint8_t v_pu_boxed_560_; lean_object* v_res_561_; 
v_pu_boxed_560_ = lean_unbox(v_pu_558_);
v_res_561_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts(v_pu_boxed_560_, v_alts_559_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(lean_object* v_n_562_, lean_object* v_as_563_, lean_object* v_lo_564_, lean_object* v_hi_565_, lean_object* v_w_566_, lean_object* v_hlo_567_, lean_object* v_hhi_568_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___redArg(v_as_563_, v_lo_564_, v_hi_565_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0___boxed(lean_object* v_n_570_, lean_object* v_as_571_, lean_object* v_lo_572_, lean_object* v_hi_573_, lean_object* v_w_574_, lean_object* v_hlo_575_, lean_object* v_hhi_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Compiler_LCNF_AlphaEqv_sortAlts_spec__0(v_n_570_, v_as_571_, v_lo_572_, v_hi_573_, v_w_574_, v_hlo_575_, v_hhi_576_);
lean_dec(v_hi_573_);
lean_dec(v_n_570_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(uint8_t v_pu_581_, lean_object* v_as_582_, size_t v_sz_583_, size_t v_i_584_, lean_object* v_b_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_a_588_; uint8_t v___x_592_; 
v___x_592_ = lean_usize_dec_lt(v_i_584_, v_sz_583_);
if (v___x_592_ == 0)
{
lean_dec(v___y_586_);
return v_b_585_;
}
else
{
lean_object* v_snd_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_681_; 
v_snd_593_ = lean_ctor_get(v_b_585_, 1);
v_isSharedCheck_681_ = !lean_is_exclusive(v_b_585_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v_b_585_, 0);
lean_dec(v_unused_682_);
v___x_595_ = v_b_585_;
v_isShared_596_ = v_isSharedCheck_681_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_snd_593_);
lean_dec(v_b_585_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_681_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v_array_597_; lean_object* v_start_598_; lean_object* v_stop_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_array_597_ = lean_ctor_get(v_snd_593_, 0);
v_start_598_ = lean_ctor_get(v_snd_593_, 1);
v_stop_599_ = lean_ctor_get(v_snd_593_, 2);
v___x_600_ = lean_box(0);
v___x_601_ = lean_nat_dec_lt(v_start_598_, v_stop_599_);
if (v___x_601_ == 0)
{
lean_object* v___x_603_; 
lean_dec(v___y_586_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 0, v___x_600_);
v___x_603_ = v___x_595_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_snd_593_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
else
{
lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_677_; 
lean_inc(v_stop_599_);
lean_inc(v_start_598_);
lean_inc_ref(v_array_597_);
v_isSharedCheck_677_ = !lean_is_exclusive(v_snd_593_);
if (v_isSharedCheck_677_ == 0)
{
lean_object* v_unused_678_; lean_object* v_unused_679_; lean_object* v_unused_680_; 
v_unused_678_ = lean_ctor_get(v_snd_593_, 2);
lean_dec(v_unused_678_);
v_unused_679_ = lean_ctor_get(v_snd_593_, 1);
lean_dec(v_unused_679_);
v_unused_680_ = lean_ctor_get(v_snd_593_, 0);
lean_dec(v_unused_680_);
v___x_606_ = v_snd_593_;
v_isShared_607_ = v_isSharedCheck_677_;
goto v_resetjp_605_;
}
else
{
lean_dec(v_snd_593_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_677_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_a_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v_a_608_ = lean_array_uget_borrowed(v_as_582_, v_i_584_);
v___x_609_ = lean_array_fget(v_array_597_, v_start_598_);
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_add(v_start_598_, v___x_610_);
lean_dec(v_start_598_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v___x_611_);
v___x_613_ = v___x_606_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_array_597_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_stop_599_);
v___x_613_ = v_reuseFailAlloc_676_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
uint8_t v___y_615_; 
switch(lean_obj_tag(v_a_608_))
{
case 0:
{
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_ctorName_624_; lean_object* v_params_625_; lean_object* v_code_626_; lean_object* v_ctorName_627_; lean_object* v_params_628_; lean_object* v_code_629_; uint8_t v___x_630_; 
v_ctorName_624_ = lean_ctor_get(v_a_608_, 0);
v_params_625_ = lean_ctor_get(v_a_608_, 1);
v_code_626_ = lean_ctor_get(v_a_608_, 2);
v_ctorName_627_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_ctorName_627_);
v_params_628_ = lean_ctor_get(v___x_609_, 1);
lean_inc_ref(v_params_628_);
v_code_629_ = lean_ctor_get(v___x_609_, 2);
lean_inc_ref(v_code_629_);
lean_dec_ref(v___x_609_);
v___x_630_ = lean_name_eq(v_ctorName_624_, v_ctorName_627_);
lean_dec(v_ctorName_627_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v_code_629_);
lean_dec_ref(v_params_628_);
lean_del_object(v___x_595_);
lean_dec(v___y_586_);
v___x_631_ = lean_box(v___x_630_);
v___x_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_613_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v___x_634_ = lean_array_get_size(v_params_628_);
v___x_635_ = lean_array_get_size(v_params_625_);
v___x_636_ = lean_nat_dec_eq(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec_ref(v_code_629_);
lean_dec_ref(v_params_628_);
lean_dec(v___y_586_);
v___y_615_ = v___x_636_;
goto v___jp_614_;
}
else
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_unsigned_to_nat(0u);
lean_inc(v___y_586_);
lean_inc_ref(v_code_626_);
v___x_638_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_581_, v_code_626_, v_code_629_, v_params_625_, v_params_628_, v___x_637_, v___y_586_);
lean_dec_ref(v_params_628_);
if (v___x_638_ == 0)
{
lean_dec(v___y_586_);
v___y_615_ = v___x_638_;
goto v___jp_614_;
}
else
{
lean_object* v___x_639_; 
lean_del_object(v___x_595_);
v___x_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_600_);
lean_ctor_set(v___x_639_, 1, v___x_613_);
v_a_588_ = v___x_639_;
goto v___jp_587_;
}
}
}
}
else
{
lean_dec(v___x_609_);
lean_del_object(v___x_595_);
lean_dec(v___y_586_);
goto v___jp_621_;
}
}
case 1:
{
lean_del_object(v___x_595_);
if (lean_obj_tag(v___x_609_) == 1)
{
lean_object* v_info_640_; lean_object* v_code_641_; lean_object* v_info_642_; lean_object* v_code_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_662_; 
v_info_640_ = lean_ctor_get(v_a_608_, 0);
v_code_641_ = lean_ctor_get(v_a_608_, 1);
v_info_642_ = lean_ctor_get(v___x_609_, 0);
v_code_643_ = lean_ctor_get(v___x_609_, 1);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_662_ == 0)
{
v___x_645_ = v___x_609_;
v_isShared_646_ = v_isSharedCheck_662_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_code_643_);
lean_inc(v_info_642_);
lean_dec(v___x_609_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_662_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
uint8_t v___x_647_; 
v___x_647_ = l_Lean_Compiler_LCNF_instBEqCtorInfo_beq(v_info_640_, v_info_642_);
lean_dec_ref(v_info_642_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_651_; 
lean_dec_ref(v_code_643_);
lean_dec(v___y_586_);
v___x_648_ = lean_box(v___x_647_);
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 1, v___x_613_);
lean_ctor_set(v___x_645_, 0, v___x_649_);
v___x_651_ = v___x_645_;
goto v_reusejp_650_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_649_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v___x_613_);
v___x_651_ = v_reuseFailAlloc_652_;
goto v_reusejp_650_;
}
v_reusejp_650_:
{
return v___x_651_;
}
}
else
{
uint8_t v___x_653_; 
lean_inc(v___y_586_);
lean_inc_ref(v_code_641_);
v___x_653_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_581_, v_code_641_, v_code_643_, v___y_586_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
lean_dec(v___y_586_);
v___x_654_ = lean_box(v___x_653_);
v___x_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 1, v___x_613_);
lean_ctor_set(v___x_645_, 0, v___x_655_);
v___x_657_ = v___x_645_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v___x_613_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
else
{
lean_object* v___x_660_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set_tag(v___x_645_, 0);
lean_ctor_set(v___x_645_, 1, v___x_613_);
lean_ctor_set(v___x_645_, 0, v___x_600_);
v___x_660_ = v___x_645_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v___x_600_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v___x_613_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
v_a_588_ = v___x_660_;
goto v___jp_587_;
}
}
}
}
}
else
{
lean_dec(v___x_609_);
lean_dec(v___y_586_);
goto v___jp_621_;
}
}
default: 
{
lean_del_object(v___x_595_);
if (lean_obj_tag(v___x_609_) == 2)
{
lean_object* v_code_663_; lean_object* v_code_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_675_; 
v_code_663_ = lean_ctor_get(v_a_608_, 0);
v_code_664_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_675_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_675_ == 0)
{
v___x_666_ = v___x_609_;
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_code_664_);
lean_dec(v___x_609_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_675_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
uint8_t v___x_668_; 
lean_inc(v___y_586_);
lean_inc_ref(v_code_663_);
v___x_668_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_581_, v_code_663_, v_code_664_, v___y_586_);
if (v___x_668_ == 0)
{
lean_object* v___x_669_; lean_object* v___x_671_; 
lean_dec(v___y_586_);
v___x_669_ = lean_box(v___x_668_);
if (v_isShared_667_ == 0)
{
lean_ctor_set_tag(v___x_666_, 1);
lean_ctor_set(v___x_666_, 0, v___x_669_);
v___x_671_ = v___x_666_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_673_; 
v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_669_);
v___x_671_ = v_reuseFailAlloc_673_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___x_613_);
return v___x_672_;
}
}
else
{
lean_object* v___x_674_; 
lean_del_object(v___x_666_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_600_);
lean_ctor_set(v___x_674_, 1, v___x_613_);
v_a_588_ = v___x_674_;
goto v___jp_587_;
}
}
}
else
{
lean_dec(v___x_609_);
lean_dec(v___y_586_);
goto v___jp_621_;
}
}
}
v___jp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_616_ = lean_box(v___y_615_);
v___x_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
if (v_isShared_596_ == 0)
{
lean_ctor_set(v___x_595_, 1, v___x_613_);
lean_ctor_set(v___x_595_, 0, v___x_617_);
v___x_619_ = v___x_595_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v___x_613_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
v___jp_621_:
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___closed__0));
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_613_);
return v___x_623_;
}
}
}
}
}
}
v___jp_587_:
{
size_t v___x_589_; size_t v___x_590_; 
v___x_589_ = ((size_t)1ULL);
v___x_590_ = lean_usize_add(v_i_584_, v___x_589_);
v_i_584_ = v___x_590_;
v_b_585_ = v_a_588_;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(uint8_t v_pu_683_, lean_object* v_alts_u2081_684_, lean_object* v_alts_u2082_685_, lean_object* v_a_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = lean_array_get_size(v_alts_u2081_684_);
v___x_688_ = lean_array_get_size(v_alts_u2082_685_);
v___x_689_ = lean_nat_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_dec(v_a_686_);
lean_dec_ref(v_alts_u2082_685_);
lean_dec_ref(v_alts_u2081_684_);
return v___x_689_;
}
else
{
lean_object* v_alts_u2081_690_; lean_object* v_alts_u2082_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; size_t v_sz_697_; size_t v___x_698_; lean_object* v___x_699_; lean_object* v_fst_700_; 
v_alts_u2081_690_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2081_684_);
v_alts_u2082_691_ = l_Lean_Compiler_LCNF_AlphaEqv_sortAlts___redArg(v_alts_u2082_685_);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_array_get_size(v_alts_u2082_691_);
v___x_694_ = l_Array_toSubarray___redArg(v_alts_u2082_691_, v___x_692_, v___x_693_);
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_694_);
v_sz_697_ = lean_array_size(v_alts_u2081_690_);
v___x_698_ = ((size_t)0ULL);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_683_, v_alts_u2081_690_, v_sz_697_, v___x_698_, v___x_696_, v_a_686_);
lean_dec_ref(v_alts_u2081_690_);
v_fst_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_fst_700_);
lean_dec_ref(v___x_699_);
if (lean_obj_tag(v_fst_700_) == 0)
{
return v___x_689_;
}
else
{
lean_object* v_val_701_; uint8_t v___x_702_; 
v_val_701_ = lean_ctor_get(v_fst_700_, 0);
lean_inc(v_val_701_);
lean_dec_ref(v_fst_700_);
v___x_702_ = lean_unbox(v_val_701_);
lean_dec(v_val_701_);
return v___x_702_;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_AlphaEqv_eqv(uint8_t v_pu_703_, lean_object* v_code_u2081_704_, lean_object* v_code_u2082_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_711_; lean_object* v___y_712_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; uint8_t v___y_719_; lean_object* v___y_720_; lean_object* v___y_721_; uint8_t v___y_722_; uint8_t v___y_723_; lean_object* v_fvarId_u2081_725_; lean_object* v_n_u2081_726_; uint8_t v_c_u2081_727_; uint8_t v_p_u2081_728_; lean_object* v_k_u2081_729_; lean_object* v_fvarId_u2082_730_; lean_object* v_n_u2082_731_; uint8_t v_c_u2082_732_; uint8_t v_p_u2082_733_; lean_object* v_k_u2082_734_; lean_object* v___y_735_; 
switch(lean_obj_tag(v_code_u2081_704_))
{
case 0:
{
if (lean_obj_tag(v_code_u2082_705_) == 0)
{
lean_object* v_decl_737_; lean_object* v_decl_738_; lean_object* v_k_739_; lean_object* v_k_740_; lean_object* v_fvarId_741_; lean_object* v_type_742_; lean_object* v_value_743_; lean_object* v_fvarId_744_; lean_object* v_type_745_; lean_object* v_value_746_; uint8_t v___x_747_; 
v_decl_737_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc_ref(v_decl_737_);
v_decl_738_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc_ref(v_decl_738_);
v_k_739_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc_ref(v_k_739_);
lean_dec_ref(v_code_u2081_704_);
v_k_740_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc_ref(v_k_740_);
lean_dec_ref(v_code_u2082_705_);
v_fvarId_741_ = lean_ctor_get(v_decl_737_, 0);
lean_inc(v_fvarId_741_);
v_type_742_ = lean_ctor_get(v_decl_737_, 2);
lean_inc_ref(v_type_742_);
v_value_743_ = lean_ctor_get(v_decl_737_, 3);
lean_inc(v_value_743_);
lean_dec_ref(v_decl_737_);
v_fvarId_744_ = lean_ctor_get(v_decl_738_, 0);
lean_inc(v_fvarId_744_);
v_type_745_ = lean_ctor_get(v_decl_738_, 2);
lean_inc_ref(v_type_745_);
v_value_746_ = lean_ctor_get(v_decl_738_, 3);
lean_inc(v_value_746_);
lean_dec_ref(v_decl_738_);
v___x_747_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_742_, v_type_745_, v_a_706_);
lean_dec_ref(v_type_745_);
lean_dec_ref(v_type_742_);
if (v___x_747_ == 0)
{
lean_dec(v_value_746_);
lean_dec(v_fvarId_744_);
lean_dec(v_value_743_);
lean_dec(v_fvarId_741_);
lean_dec_ref(v_k_740_);
lean_dec_ref(v_k_739_);
lean_dec(v_a_706_);
return v___x_747_;
}
else
{
uint8_t v___x_748_; 
v___x_748_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvLetValue(v_pu_703_, v_value_743_, v_value_746_, v_a_706_);
lean_dec(v_value_743_);
if (v___x_748_ == 0)
{
lean_dec(v_fvarId_744_);
lean_dec(v_fvarId_741_);
lean_dec_ref(v_k_740_);
lean_dec_ref(v_k_739_);
lean_dec(v_a_706_);
return v___x_748_;
}
else
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_744_, v_fvarId_741_, v_a_706_);
v_code_u2081_704_ = v_k_739_;
v_code_u2082_705_ = v_k_740_;
v_a_706_ = v___x_749_;
goto _start;
}
}
}
else
{
uint8_t v___x_751_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_751_ = 0;
return v___x_751_;
}
}
case 1:
{
if (lean_obj_tag(v_code_u2082_705_) == 1)
{
lean_object* v_decl_752_; lean_object* v_decl_753_; lean_object* v_k_754_; lean_object* v_k_755_; lean_object* v_fvarId_756_; lean_object* v_params_757_; lean_object* v_type_758_; lean_object* v_value_759_; lean_object* v_fvarId_760_; lean_object* v_params_761_; lean_object* v_type_762_; lean_object* v_value_763_; uint8_t v___x_764_; 
v_decl_752_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc_ref(v_decl_752_);
v_decl_753_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc_ref(v_decl_753_);
v_k_754_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc_ref(v_k_754_);
lean_dec_ref(v_code_u2081_704_);
v_k_755_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc_ref(v_k_755_);
lean_dec_ref(v_code_u2082_705_);
v_fvarId_756_ = lean_ctor_get(v_decl_752_, 0);
lean_inc(v_fvarId_756_);
v_params_757_ = lean_ctor_get(v_decl_752_, 2);
lean_inc_ref(v_params_757_);
v_type_758_ = lean_ctor_get(v_decl_752_, 3);
lean_inc_ref(v_type_758_);
v_value_759_ = lean_ctor_get(v_decl_752_, 4);
lean_inc_ref(v_value_759_);
lean_dec_ref(v_decl_752_);
v_fvarId_760_ = lean_ctor_get(v_decl_753_, 0);
lean_inc(v_fvarId_760_);
v_params_761_ = lean_ctor_get(v_decl_753_, 2);
lean_inc_ref(v_params_761_);
v_type_762_ = lean_ctor_get(v_decl_753_, 3);
lean_inc_ref(v_type_762_);
v_value_763_ = lean_ctor_get(v_decl_753_, 4);
lean_inc_ref(v_value_763_);
lean_dec_ref(v_decl_753_);
v___x_764_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_758_, v_type_762_, v_a_706_);
lean_dec_ref(v_type_762_);
lean_dec_ref(v_type_758_);
if (v___x_764_ == 0)
{
lean_dec_ref(v_value_763_);
lean_dec_ref(v_params_761_);
lean_dec(v_fvarId_760_);
lean_dec_ref(v_value_759_);
lean_dec_ref(v_params_757_);
lean_dec(v_fvarId_756_);
lean_dec_ref(v_k_755_);
lean_dec_ref(v_k_754_);
lean_dec(v_a_706_);
return v___x_764_;
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_765_ = lean_array_get_size(v_params_761_);
v___x_766_ = lean_array_get_size(v_params_757_);
v___x_767_ = lean_nat_dec_eq(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_dec_ref(v_value_763_);
lean_dec_ref(v_params_761_);
lean_dec(v_fvarId_760_);
lean_dec_ref(v_value_759_);
lean_dec_ref(v_params_757_);
lean_dec(v_fvarId_756_);
lean_dec_ref(v_k_755_);
lean_dec_ref(v_k_754_);
lean_dec(v_a_706_);
return v___x_767_;
}
else
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_706_);
v___x_769_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_703_, v_value_759_, v_value_763_, v_params_757_, v_params_761_, v___x_768_, v_a_706_);
lean_dec_ref(v_params_761_);
lean_dec_ref(v_params_757_);
if (v___x_769_ == 0)
{
lean_dec(v_fvarId_760_);
lean_dec(v_fvarId_756_);
lean_dec_ref(v_k_755_);
lean_dec_ref(v_k_754_);
lean_dec(v_a_706_);
return v___x_769_;
}
else
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_760_, v_fvarId_756_, v_a_706_);
v_code_u2081_704_ = v_k_754_;
v_code_u2082_705_ = v_k_755_;
v_a_706_ = v___x_770_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_772_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_772_ = 0;
return v___x_772_;
}
}
case 2:
{
if (lean_obj_tag(v_code_u2082_705_) == 2)
{
lean_object* v_decl_773_; lean_object* v_decl_774_; lean_object* v_k_775_; lean_object* v_k_776_; lean_object* v_fvarId_777_; lean_object* v_params_778_; lean_object* v_type_779_; lean_object* v_value_780_; lean_object* v_fvarId_781_; lean_object* v_params_782_; lean_object* v_type_783_; lean_object* v_value_784_; uint8_t v___x_785_; 
v_decl_773_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc_ref(v_decl_773_);
v_decl_774_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc_ref(v_decl_774_);
v_k_775_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc_ref(v_k_775_);
lean_dec_ref(v_code_u2081_704_);
v_k_776_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc_ref(v_k_776_);
lean_dec_ref(v_code_u2082_705_);
v_fvarId_777_ = lean_ctor_get(v_decl_773_, 0);
lean_inc(v_fvarId_777_);
v_params_778_ = lean_ctor_get(v_decl_773_, 2);
lean_inc_ref(v_params_778_);
v_type_779_ = lean_ctor_get(v_decl_773_, 3);
lean_inc_ref(v_type_779_);
v_value_780_ = lean_ctor_get(v_decl_773_, 4);
lean_inc_ref(v_value_780_);
lean_dec_ref(v_decl_773_);
v_fvarId_781_ = lean_ctor_get(v_decl_774_, 0);
lean_inc(v_fvarId_781_);
v_params_782_ = lean_ctor_get(v_decl_774_, 2);
lean_inc_ref(v_params_782_);
v_type_783_ = lean_ctor_get(v_decl_774_, 3);
lean_inc_ref(v_type_783_);
v_value_784_ = lean_ctor_get(v_decl_774_, 4);
lean_inc_ref(v_value_784_);
lean_dec_ref(v_decl_774_);
v___x_785_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_779_, v_type_783_, v_a_706_);
lean_dec_ref(v_type_783_);
lean_dec_ref(v_type_779_);
if (v___x_785_ == 0)
{
lean_dec_ref(v_value_784_);
lean_dec_ref(v_params_782_);
lean_dec(v_fvarId_781_);
lean_dec_ref(v_value_780_);
lean_dec_ref(v_params_778_);
lean_dec(v_fvarId_777_);
lean_dec_ref(v_k_776_);
lean_dec_ref(v_k_775_);
lean_dec(v_a_706_);
return v___x_785_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_786_ = lean_array_get_size(v_params_782_);
v___x_787_ = lean_array_get_size(v_params_778_);
v___x_788_ = lean_nat_dec_eq(v___x_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_dec_ref(v_value_784_);
lean_dec_ref(v_params_782_);
lean_dec(v_fvarId_781_);
lean_dec_ref(v_value_780_);
lean_dec_ref(v_params_778_);
lean_dec(v_fvarId_777_);
lean_dec_ref(v_k_776_);
lean_dec_ref(v_k_775_);
lean_dec(v_a_706_);
return v___x_788_;
}
else
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_unsigned_to_nat(0u);
lean_inc(v_a_706_);
v___x_790_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_703_, v_value_780_, v_value_784_, v_params_778_, v_params_782_, v___x_789_, v_a_706_);
lean_dec_ref(v_params_782_);
lean_dec_ref(v_params_778_);
if (v___x_790_ == 0)
{
lean_dec(v_fvarId_781_);
lean_dec(v_fvarId_777_);
lean_dec_ref(v_k_776_);
lean_dec_ref(v_k_775_);
lean_dec(v_a_706_);
return v___x_790_;
}
else
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_781_, v_fvarId_777_, v_a_706_);
v_code_u2081_704_ = v_k_775_;
v_code_u2082_705_ = v_k_776_;
v_a_706_ = v___x_791_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_793_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_793_ = 0;
return v___x_793_;
}
}
case 3:
{
if (lean_obj_tag(v_code_u2082_705_) == 3)
{
lean_object* v_fvarId_794_; lean_object* v_args_795_; lean_object* v_fvarId_796_; lean_object* v_args_797_; uint8_t v___x_798_; 
v_fvarId_794_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc(v_fvarId_794_);
v_args_795_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc_ref(v_args_795_);
lean_dec_ref(v_code_u2081_704_);
v_fvarId_796_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc(v_fvarId_796_);
v_args_797_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc_ref(v_args_797_);
lean_dec_ref(v_code_u2082_705_);
v___x_798_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_794_, v_fvarId_796_, v_a_706_);
lean_dec(v_fvarId_796_);
lean_dec(v_fvarId_794_);
if (v___x_798_ == 0)
{
lean_dec_ref(v_args_797_);
lean_dec_ref(v_args_795_);
lean_dec(v_a_706_);
return v___x_798_;
}
else
{
uint8_t v___x_799_; 
v___x_799_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArgs(v_pu_703_, v_args_795_, v_args_797_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_args_795_);
return v___x_799_;
}
}
else
{
uint8_t v___x_800_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_800_ = 0;
return v___x_800_;
}
}
case 4:
{
if (lean_obj_tag(v_code_u2082_705_) == 4)
{
lean_object* v_cases_801_; lean_object* v_cases_802_; lean_object* v_resultType_803_; lean_object* v_discr_804_; lean_object* v_alts_805_; lean_object* v_resultType_806_; lean_object* v_discr_807_; lean_object* v_alts_808_; uint8_t v___x_809_; 
v_cases_801_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc_ref(v_cases_801_);
lean_dec_ref(v_code_u2081_704_);
v_cases_802_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc_ref(v_cases_802_);
lean_dec_ref(v_code_u2082_705_);
v_resultType_803_ = lean_ctor_get(v_cases_801_, 1);
lean_inc_ref(v_resultType_803_);
v_discr_804_ = lean_ctor_get(v_cases_801_, 2);
lean_inc(v_discr_804_);
v_alts_805_ = lean_ctor_get(v_cases_801_, 3);
lean_inc_ref(v_alts_805_);
lean_dec_ref(v_cases_801_);
v_resultType_806_ = lean_ctor_get(v_cases_802_, 1);
lean_inc_ref(v_resultType_806_);
v_discr_807_ = lean_ctor_get(v_cases_802_, 2);
lean_inc(v_discr_807_);
v_alts_808_ = lean_ctor_get(v_cases_802_, 3);
lean_inc_ref(v_alts_808_);
lean_dec_ref(v_cases_802_);
v___x_809_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_discr_804_, v_discr_807_, v_a_706_);
lean_dec(v_discr_807_);
lean_dec(v_discr_804_);
if (v___x_809_ == 0)
{
lean_dec_ref(v_alts_808_);
lean_dec_ref(v_resultType_806_);
lean_dec_ref(v_alts_805_);
lean_dec_ref(v_resultType_803_);
lean_dec(v_a_706_);
return v___x_809_;
}
else
{
uint8_t v___x_810_; 
v___x_810_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_resultType_803_, v_resultType_806_, v_a_706_);
lean_dec_ref(v_resultType_806_);
lean_dec_ref(v_resultType_803_);
if (v___x_810_ == 0)
{
lean_dec_ref(v_alts_808_);
lean_dec_ref(v_alts_805_);
lean_dec(v_a_706_);
return v___x_810_;
}
else
{
uint8_t v___x_811_; 
v___x_811_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_703_, v_alts_805_, v_alts_808_, v_a_706_);
return v___x_811_;
}
}
}
else
{
uint8_t v___x_812_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_812_ = 0;
return v___x_812_;
}
}
case 5:
{
if (lean_obj_tag(v_code_u2082_705_) == 5)
{
lean_object* v_fvarId_813_; lean_object* v_fvarId_814_; uint8_t v___x_815_; 
v_fvarId_813_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc(v_fvarId_813_);
lean_dec_ref(v_code_u2081_704_);
v_fvarId_814_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc(v_fvarId_814_);
lean_dec_ref(v_code_u2082_705_);
v___x_815_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_813_, v_fvarId_814_, v_a_706_);
lean_dec(v_a_706_);
lean_dec(v_fvarId_814_);
lean_dec(v_fvarId_813_);
return v___x_815_;
}
else
{
uint8_t v___x_816_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_816_ = 0;
return v___x_816_;
}
}
case 6:
{
if (lean_obj_tag(v_code_u2082_705_) == 6)
{
lean_object* v_type_817_; lean_object* v_type_818_; uint8_t v___x_819_; 
v_type_817_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc_ref(v_type_817_);
lean_dec_ref(v_code_u2081_704_);
v_type_818_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc_ref(v_type_818_);
lean_dec_ref(v_code_u2082_705_);
v___x_819_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_817_, v_type_818_, v_a_706_);
lean_dec(v_a_706_);
lean_dec_ref(v_type_818_);
lean_dec_ref(v_type_817_);
return v___x_819_;
}
else
{
uint8_t v___x_820_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_820_ = 0;
return v___x_820_;
}
}
case 7:
{
if (lean_obj_tag(v_code_u2082_705_) == 7)
{
lean_object* v_fvarId_821_; lean_object* v_i_822_; lean_object* v_y_823_; lean_object* v_k_824_; lean_object* v_fvarId_825_; lean_object* v_i_826_; lean_object* v_y_827_; lean_object* v_k_828_; uint8_t v___x_829_; 
v_fvarId_821_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc(v_fvarId_821_);
v_i_822_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc(v_i_822_);
v_y_823_ = lean_ctor_get(v_code_u2081_704_, 2);
lean_inc(v_y_823_);
v_k_824_ = lean_ctor_get(v_code_u2081_704_, 3);
lean_inc_ref(v_k_824_);
lean_dec_ref(v_code_u2081_704_);
v_fvarId_825_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc(v_fvarId_825_);
v_i_826_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc(v_i_826_);
v_y_827_ = lean_ctor_get(v_code_u2082_705_, 2);
lean_inc(v_y_827_);
v_k_828_ = lean_ctor_get(v_code_u2082_705_, 3);
lean_inc_ref(v_k_828_);
lean_dec_ref(v_code_u2082_705_);
v___x_829_ = lean_nat_dec_eq(v_i_822_, v_i_826_);
lean_dec(v_i_826_);
lean_dec(v_i_822_);
if (v___x_829_ == 0)
{
lean_dec_ref(v_k_828_);
lean_dec(v_y_827_);
lean_dec(v_fvarId_825_);
lean_dec_ref(v_k_824_);
lean_dec(v_y_823_);
lean_dec(v_fvarId_821_);
lean_dec(v_a_706_);
return v___x_829_;
}
else
{
uint8_t v___x_830_; 
v___x_830_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_821_, v_fvarId_825_, v_a_706_);
lean_dec(v_fvarId_825_);
lean_dec(v_fvarId_821_);
if (v___x_830_ == 0)
{
lean_dec_ref(v_k_828_);
lean_dec(v_y_827_);
lean_dec_ref(v_k_824_);
lean_dec(v_y_823_);
lean_dec(v_a_706_);
return v___x_830_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvArg___redArg(v_y_823_, v_y_827_, v_a_706_);
lean_dec(v_y_827_);
lean_dec(v_y_823_);
if (v___x_831_ == 0)
{
lean_dec_ref(v_k_828_);
lean_dec_ref(v_k_824_);
lean_dec(v_a_706_);
return v___x_831_;
}
else
{
v_code_u2081_704_ = v_k_824_;
v_code_u2082_705_ = v_k_828_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_833_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_833_ = 0;
return v___x_833_;
}
}
case 8:
{
if (lean_obj_tag(v_code_u2082_705_) == 8)
{
lean_object* v_fvarId_834_; lean_object* v_i_835_; lean_object* v_y_836_; lean_object* v_k_837_; lean_object* v_fvarId_838_; lean_object* v_i_839_; lean_object* v_y_840_; lean_object* v_k_841_; uint8_t v___x_842_; 
v_fvarId_834_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc(v_fvarId_834_);
v_i_835_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc(v_i_835_);
v_y_836_ = lean_ctor_get(v_code_u2081_704_, 2);
lean_inc(v_y_836_);
v_k_837_ = lean_ctor_get(v_code_u2081_704_, 3);
lean_inc_ref(v_k_837_);
lean_dec_ref(v_code_u2081_704_);
v_fvarId_838_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc(v_fvarId_838_);
v_i_839_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc(v_i_839_);
v_y_840_ = lean_ctor_get(v_code_u2082_705_, 2);
lean_inc(v_y_840_);
v_k_841_ = lean_ctor_get(v_code_u2082_705_, 3);
lean_inc_ref(v_k_841_);
lean_dec_ref(v_code_u2082_705_);
v___x_842_ = lean_nat_dec_eq(v_i_835_, v_i_839_);
lean_dec(v_i_839_);
lean_dec(v_i_835_);
if (v___x_842_ == 0)
{
lean_dec_ref(v_k_841_);
lean_dec(v_y_840_);
lean_dec(v_fvarId_838_);
lean_dec_ref(v_k_837_);
lean_dec(v_y_836_);
lean_dec(v_fvarId_834_);
lean_dec(v_a_706_);
return v___x_842_;
}
else
{
uint8_t v___x_843_; 
v___x_843_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_834_, v_fvarId_838_, v_a_706_);
lean_dec(v_fvarId_838_);
lean_dec(v_fvarId_834_);
if (v___x_843_ == 0)
{
lean_dec_ref(v_k_841_);
lean_dec(v_y_840_);
lean_dec_ref(v_k_837_);
lean_dec(v_y_836_);
lean_dec(v_a_706_);
return v___x_843_;
}
else
{
uint8_t v___x_844_; 
v___x_844_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_836_, v_y_840_, v_a_706_);
lean_dec(v_y_840_);
lean_dec(v_y_836_);
if (v___x_844_ == 0)
{
lean_dec_ref(v_k_841_);
lean_dec_ref(v_k_837_);
lean_dec(v_a_706_);
return v___x_844_;
}
else
{
v_code_u2081_704_ = v_k_837_;
v_code_u2082_705_ = v_k_841_;
goto _start;
}
}
}
}
else
{
uint8_t v___x_846_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_846_ = 0;
return v___x_846_;
}
}
case 9:
{
if (lean_obj_tag(v_code_u2082_705_) == 9)
{
lean_object* v_fvarId_847_; lean_object* v_i_848_; lean_object* v_offset_849_; lean_object* v_y_850_; lean_object* v_ty_851_; lean_object* v_k_852_; lean_object* v_fvarId_853_; lean_object* v_i_854_; lean_object* v_offset_855_; lean_object* v_y_856_; lean_object* v_ty_857_; lean_object* v_k_858_; uint8_t v___x_859_; 
v_fvarId_847_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc(v_fvarId_847_);
v_i_848_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc(v_i_848_);
v_offset_849_ = lean_ctor_get(v_code_u2081_704_, 2);
lean_inc(v_offset_849_);
v_y_850_ = lean_ctor_get(v_code_u2081_704_, 3);
lean_inc(v_y_850_);
v_ty_851_ = lean_ctor_get(v_code_u2081_704_, 4);
lean_inc_ref(v_ty_851_);
v_k_852_ = lean_ctor_get(v_code_u2081_704_, 5);
lean_inc_ref(v_k_852_);
lean_dec_ref(v_code_u2081_704_);
v_fvarId_853_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc(v_fvarId_853_);
v_i_854_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc(v_i_854_);
v_offset_855_ = lean_ctor_get(v_code_u2082_705_, 2);
lean_inc(v_offset_855_);
v_y_856_ = lean_ctor_get(v_code_u2082_705_, 3);
lean_inc(v_y_856_);
v_ty_857_ = lean_ctor_get(v_code_u2082_705_, 4);
lean_inc_ref(v_ty_857_);
v_k_858_ = lean_ctor_get(v_code_u2082_705_, 5);
lean_inc_ref(v_k_858_);
lean_dec_ref(v_code_u2082_705_);
v___x_859_ = lean_nat_dec_eq(v_i_848_, v_i_854_);
lean_dec(v_i_854_);
lean_dec(v_i_848_);
if (v___x_859_ == 0)
{
lean_dec_ref(v_k_858_);
lean_dec_ref(v_ty_857_);
lean_dec(v_y_856_);
lean_dec(v_offset_855_);
lean_dec(v_fvarId_853_);
lean_dec_ref(v_k_852_);
lean_dec_ref(v_ty_851_);
lean_dec(v_y_850_);
lean_dec(v_offset_849_);
lean_dec(v_fvarId_847_);
lean_dec(v_a_706_);
return v___x_859_;
}
else
{
uint8_t v___x_860_; 
v___x_860_ = lean_nat_dec_eq(v_offset_849_, v_offset_855_);
lean_dec(v_offset_855_);
lean_dec(v_offset_849_);
if (v___x_860_ == 0)
{
lean_dec_ref(v_k_858_);
lean_dec_ref(v_ty_857_);
lean_dec(v_y_856_);
lean_dec(v_fvarId_853_);
lean_dec_ref(v_k_852_);
lean_dec_ref(v_ty_851_);
lean_dec(v_y_850_);
lean_dec(v_fvarId_847_);
lean_dec(v_a_706_);
return v___x_860_;
}
else
{
uint8_t v___x_861_; 
v___x_861_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_847_, v_fvarId_853_, v_a_706_);
lean_dec(v_fvarId_853_);
lean_dec(v_fvarId_847_);
if (v___x_861_ == 0)
{
lean_dec_ref(v_k_858_);
lean_dec_ref(v_ty_857_);
lean_dec(v_y_856_);
lean_dec_ref(v_k_852_);
lean_dec_ref(v_ty_851_);
lean_dec(v_y_850_);
lean_dec(v_a_706_);
return v___x_861_;
}
else
{
uint8_t v___x_862_; 
v___x_862_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_y_850_, v_y_856_, v_a_706_);
lean_dec(v_y_856_);
lean_dec(v_y_850_);
if (v___x_862_ == 0)
{
lean_dec_ref(v_k_858_);
lean_dec_ref(v_ty_857_);
lean_dec_ref(v_k_852_);
lean_dec_ref(v_ty_851_);
lean_dec(v_a_706_);
return v___x_862_;
}
else
{
uint8_t v___x_863_; 
v___x_863_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_ty_851_, v_ty_857_, v_a_706_);
lean_dec_ref(v_ty_857_);
lean_dec_ref(v_ty_851_);
if (v___x_863_ == 0)
{
lean_dec_ref(v_k_858_);
lean_dec_ref(v_k_852_);
lean_dec(v_a_706_);
return v___x_863_;
}
else
{
v_code_u2081_704_ = v_k_852_;
v_code_u2082_705_ = v_k_858_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_865_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_865_ = 0;
return v___x_865_;
}
}
case 10:
{
if (lean_obj_tag(v_code_u2082_705_) == 10)
{
lean_object* v_fvarId_866_; lean_object* v_cidx_867_; lean_object* v_k_868_; lean_object* v_fvarId_869_; lean_object* v_cidx_870_; lean_object* v_k_871_; uint8_t v___x_872_; 
v_fvarId_866_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc(v_fvarId_866_);
v_cidx_867_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc(v_cidx_867_);
v_k_868_ = lean_ctor_get(v_code_u2081_704_, 2);
lean_inc_ref(v_k_868_);
lean_dec_ref(v_code_u2081_704_);
v_fvarId_869_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc(v_fvarId_869_);
v_cidx_870_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc(v_cidx_870_);
v_k_871_ = lean_ctor_get(v_code_u2082_705_, 2);
lean_inc_ref(v_k_871_);
lean_dec_ref(v_code_u2082_705_);
v___x_872_ = lean_nat_dec_eq(v_cidx_867_, v_cidx_870_);
lean_dec(v_cidx_870_);
lean_dec(v_cidx_867_);
if (v___x_872_ == 0)
{
lean_dec_ref(v_k_871_);
lean_dec(v_fvarId_869_);
lean_dec_ref(v_k_868_);
lean_dec(v_fvarId_866_);
lean_dec(v_a_706_);
return v___x_872_;
}
else
{
uint8_t v___x_873_; 
v___x_873_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_866_, v_fvarId_869_, v_a_706_);
lean_dec(v_fvarId_869_);
lean_dec(v_fvarId_866_);
if (v___x_873_ == 0)
{
lean_dec_ref(v_k_871_);
lean_dec_ref(v_k_868_);
lean_dec(v_a_706_);
return v___x_873_;
}
else
{
v_code_u2081_704_ = v_k_868_;
v_code_u2082_705_ = v_k_871_;
goto _start;
}
}
}
else
{
uint8_t v___x_875_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_875_ = 0;
return v___x_875_;
}
}
case 11:
{
if (lean_obj_tag(v_code_u2082_705_) == 11)
{
lean_object* v_fvarId_876_; lean_object* v_n_877_; uint8_t v_check_878_; uint8_t v_persistent_879_; lean_object* v_k_880_; lean_object* v_fvarId_881_; lean_object* v_n_882_; uint8_t v_check_883_; uint8_t v_persistent_884_; lean_object* v_k_885_; 
v_fvarId_876_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc(v_fvarId_876_);
v_n_877_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc(v_n_877_);
v_check_878_ = lean_ctor_get_uint8(v_code_u2081_704_, sizeof(void*)*3);
v_persistent_879_ = lean_ctor_get_uint8(v_code_u2081_704_, sizeof(void*)*3 + 1);
v_k_880_ = lean_ctor_get(v_code_u2081_704_, 2);
lean_inc_ref(v_k_880_);
lean_dec_ref(v_code_u2081_704_);
v_fvarId_881_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc(v_fvarId_881_);
v_n_882_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc(v_n_882_);
v_check_883_ = lean_ctor_get_uint8(v_code_u2082_705_, sizeof(void*)*3);
v_persistent_884_ = lean_ctor_get_uint8(v_code_u2082_705_, sizeof(void*)*3 + 1);
v_k_885_ = lean_ctor_get(v_code_u2082_705_, 2);
lean_inc_ref(v_k_885_);
lean_dec_ref(v_code_u2082_705_);
v_fvarId_u2081_725_ = v_fvarId_876_;
v_n_u2081_726_ = v_n_877_;
v_c_u2081_727_ = v_check_878_;
v_p_u2081_728_ = v_persistent_879_;
v_k_u2081_729_ = v_k_880_;
v_fvarId_u2082_730_ = v_fvarId_881_;
v_n_u2082_731_ = v_n_882_;
v_c_u2082_732_ = v_check_883_;
v_p_u2082_733_ = v_persistent_884_;
v_k_u2082_734_ = v_k_885_;
v___y_735_ = v_a_706_;
goto v___jp_724_;
}
else
{
uint8_t v___x_886_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_886_ = 0;
return v___x_886_;
}
}
case 12:
{
if (lean_obj_tag(v_code_u2082_705_) == 12)
{
lean_object* v_fvarId_887_; lean_object* v_n_888_; uint8_t v_check_889_; uint8_t v_persistent_890_; lean_object* v_k_891_; lean_object* v_fvarId_892_; lean_object* v_n_893_; uint8_t v_check_894_; uint8_t v_persistent_895_; lean_object* v_k_896_; 
v_fvarId_887_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc(v_fvarId_887_);
v_n_888_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc(v_n_888_);
v_check_889_ = lean_ctor_get_uint8(v_code_u2081_704_, sizeof(void*)*3);
v_persistent_890_ = lean_ctor_get_uint8(v_code_u2081_704_, sizeof(void*)*3 + 1);
v_k_891_ = lean_ctor_get(v_code_u2081_704_, 2);
lean_inc_ref(v_k_891_);
lean_dec_ref(v_code_u2081_704_);
v_fvarId_892_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc(v_fvarId_892_);
v_n_893_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc(v_n_893_);
v_check_894_ = lean_ctor_get_uint8(v_code_u2082_705_, sizeof(void*)*3);
v_persistent_895_ = lean_ctor_get_uint8(v_code_u2082_705_, sizeof(void*)*3 + 1);
v_k_896_ = lean_ctor_get(v_code_u2082_705_, 2);
lean_inc_ref(v_k_896_);
lean_dec_ref(v_code_u2082_705_);
v_fvarId_u2081_725_ = v_fvarId_887_;
v_n_u2081_726_ = v_n_888_;
v_c_u2081_727_ = v_check_889_;
v_p_u2081_728_ = v_persistent_890_;
v_k_u2081_729_ = v_k_891_;
v_fvarId_u2082_730_ = v_fvarId_892_;
v_n_u2082_731_ = v_n_893_;
v_c_u2082_732_ = v_check_894_;
v_p_u2082_733_ = v_persistent_895_;
v_k_u2082_734_ = v_k_896_;
v___y_735_ = v_a_706_;
goto v___jp_724_;
}
else
{
uint8_t v___x_897_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_897_ = 0;
return v___x_897_;
}
}
default: 
{
if (lean_obj_tag(v_code_u2082_705_) == 13)
{
lean_object* v_fvarId_898_; lean_object* v_k_899_; lean_object* v_fvarId_900_; lean_object* v_k_901_; uint8_t v___x_902_; 
v_fvarId_898_ = lean_ctor_get(v_code_u2081_704_, 0);
lean_inc(v_fvarId_898_);
v_k_899_ = lean_ctor_get(v_code_u2081_704_, 1);
lean_inc_ref(v_k_899_);
lean_dec_ref(v_code_u2081_704_);
v_fvarId_900_ = lean_ctor_get(v_code_u2082_705_, 0);
lean_inc(v_fvarId_900_);
v_k_901_ = lean_ctor_get(v_code_u2082_705_, 1);
lean_inc_ref(v_k_901_);
lean_dec_ref(v_code_u2082_705_);
v___x_902_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v_fvarId_898_, v_fvarId_900_, v_a_706_);
lean_dec(v_fvarId_900_);
lean_dec(v_fvarId_898_);
if (v___x_902_ == 0)
{
lean_dec_ref(v_k_901_);
lean_dec_ref(v_k_899_);
lean_dec(v_a_706_);
return v___x_902_;
}
else
{
v_code_u2081_704_ = v_k_899_;
v_code_u2082_705_ = v_k_901_;
goto _start;
}
}
else
{
uint8_t v___x_904_; 
lean_dec_ref(v_code_u2081_704_);
lean_dec(v_a_706_);
lean_dec_ref(v_code_u2082_705_);
v___x_904_ = 0;
return v___x_904_;
}
}
}
v___jp_707_:
{
uint8_t v___x_713_; 
v___x_713_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvFVar(v___y_709_, v___y_712_, v___y_708_);
lean_dec(v___y_712_);
lean_dec(v___y_709_);
if (v___x_713_ == 0)
{
lean_dec_ref(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_708_);
return v___x_713_;
}
else
{
v_code_u2081_704_ = v___y_710_;
v_code_u2082_705_ = v___y_711_;
v_a_706_ = v___y_708_;
goto _start;
}
}
v___jp_715_:
{
if (v___y_723_ == 0)
{
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec(v___y_716_);
return v___y_723_;
}
else
{
if (v___y_719_ == 0)
{
if (v___y_722_ == 0)
{
v___y_708_ = v___y_716_;
v___y_709_ = v___y_717_;
v___y_710_ = v___y_718_;
v___y_711_ = v___y_721_;
v___y_712_ = v___y_720_;
goto v___jp_707_;
}
else
{
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec(v___y_716_);
return v___y_719_;
}
}
else
{
if (v___y_722_ == 0)
{
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec(v___y_716_);
return v___y_722_;
}
else
{
v___y_708_ = v___y_716_;
v___y_709_ = v___y_717_;
v___y_710_ = v___y_718_;
v___y_711_ = v___y_721_;
v___y_712_ = v___y_720_;
goto v___jp_707_;
}
}
}
}
v___jp_724_:
{
uint8_t v___x_736_; 
v___x_736_ = lean_nat_dec_eq(v_n_u2081_726_, v_n_u2082_731_);
lean_dec(v_n_u2082_731_);
lean_dec(v_n_u2081_726_);
if (v___x_736_ == 0)
{
lean_dec(v___y_735_);
lean_dec_ref(v_k_u2082_734_);
lean_dec(v_fvarId_u2082_730_);
lean_dec_ref(v_k_u2081_729_);
lean_dec(v_fvarId_u2081_725_);
return v___x_736_;
}
else
{
if (v_c_u2081_727_ == 0)
{
if (v_c_u2082_732_ == 0)
{
v___y_716_ = v___y_735_;
v___y_717_ = v_fvarId_u2081_725_;
v___y_718_ = v_k_u2081_729_;
v___y_719_ = v_p_u2081_728_;
v___y_720_ = v_fvarId_u2082_730_;
v___y_721_ = v_k_u2082_734_;
v___y_722_ = v_p_u2082_733_;
v___y_723_ = v___x_736_;
goto v___jp_715_;
}
else
{
lean_dec(v___y_735_);
lean_dec_ref(v_k_u2082_734_);
lean_dec(v_fvarId_u2082_730_);
lean_dec_ref(v_k_u2081_729_);
lean_dec(v_fvarId_u2081_725_);
return v_c_u2081_727_;
}
}
else
{
v___y_716_ = v___y_735_;
v___y_717_ = v_fvarId_u2081_725_;
v___y_718_ = v_k_u2081_729_;
v___y_719_ = v_p_u2081_728_;
v___y_720_ = v_fvarId_u2082_730_;
v___y_721_ = v_k_u2082_734_;
v___y_722_ = v_p_u2082_733_;
v___y_723_ = v_c_u2082_732_;
goto v___jp_715_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(uint8_t v_pu_905_, lean_object* v_code_906_, lean_object* v_code_907_, lean_object* v_params_u2081_908_, lean_object* v_params_u2082_909_, lean_object* v_i_910_, lean_object* v_a_911_){
_start:
{
lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_912_ = lean_array_get_size(v_params_u2081_908_);
v___x_913_ = lean_nat_dec_lt(v_i_910_, v___x_912_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; 
lean_dec(v_i_910_);
v___x_914_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_905_, v_code_906_, v_code_907_, v_a_911_);
return v___x_914_;
}
else
{
lean_object* v_p_u2081_915_; lean_object* v_fvarId_916_; lean_object* v_type_917_; lean_object* v_p_u2082_918_; lean_object* v_fvarId_919_; lean_object* v_type_920_; uint8_t v___x_921_; 
v_p_u2081_915_ = lean_array_fget_borrowed(v_params_u2081_908_, v_i_910_);
v_fvarId_916_ = lean_ctor_get(v_p_u2081_915_, 0);
v_type_917_ = lean_ctor_get(v_p_u2081_915_, 2);
v_p_u2082_918_ = lean_array_fget_borrowed(v_params_u2082_909_, v_i_910_);
v_fvarId_919_ = lean_ctor_get(v_p_u2082_918_, 0);
v_type_920_ = lean_ctor_get(v_p_u2082_918_, 2);
v___x_921_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvType(v_type_917_, v_type_920_, v_a_911_);
if (v___x_921_ == 0)
{
lean_dec(v_a_911_);
lean_dec(v_i_910_);
lean_dec_ref(v_code_907_);
lean_dec_ref(v_code_906_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = lean_unsigned_to_nat(1u);
v___x_923_ = lean_nat_add(v_i_910_, v___x_922_);
lean_dec(v_i_910_);
lean_inc(v_fvarId_916_);
lean_inc(v_fvarId_919_);
v___x_924_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(v_fvarId_919_, v_fvarId_916_, v_a_911_);
v_i_910_ = v___x_923_;
v_a_911_ = v___x_924_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg___boxed(lean_object* v_pu_926_, lean_object* v_code_927_, lean_object* v_code_928_, lean_object* v_params_u2081_929_, lean_object* v_params_u2082_930_, lean_object* v_i_931_, lean_object* v_a_932_){
_start:
{
uint8_t v_pu_boxed_933_; uint8_t v_res_934_; lean_object* v_r_935_; 
v_pu_boxed_933_ = lean_unbox(v_pu_926_);
v_res_934_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_boxed_933_, v_code_927_, v_code_928_, v_params_u2081_929_, v_params_u2082_930_, v_i_931_, v_a_932_);
lean_dec_ref(v_params_u2082_930_);
lean_dec_ref(v_params_u2081_929_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts___boxed(lean_object* v_pu_936_, lean_object* v_alts_u2081_937_, lean_object* v_alts_u2082_938_, lean_object* v_a_939_){
_start:
{
uint8_t v_pu_boxed_940_; uint8_t v_res_941_; lean_object* v_r_942_; 
v_pu_boxed_940_ = lean_unbox(v_pu_936_);
v_res_941_ = l_Lean_Compiler_LCNF_AlphaEqv_eqvAlts(v_pu_boxed_940_, v_alts_u2081_937_, v_alts_u2082_938_, v_a_939_);
v_r_942_ = lean_box(v_res_941_);
return v_r_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1___boxed(lean_object* v_pu_943_, lean_object* v_as_944_, lean_object* v_sz_945_, lean_object* v_i_946_, lean_object* v_b_947_, lean_object* v___y_948_){
_start:
{
uint8_t v_pu_boxed_949_; size_t v_sz_boxed_950_; size_t v_i_boxed_951_; lean_object* v_res_952_; 
v_pu_boxed_949_ = lean_unbox(v_pu_943_);
v_sz_boxed_950_ = lean_unbox_usize(v_sz_945_);
lean_dec(v_sz_945_);
v_i_boxed_951_ = lean_unbox_usize(v_i_946_);
lean_dec(v_i_946_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__1(v_pu_boxed_949_, v_as_944_, v_sz_boxed_950_, v_i_boxed_951_, v_b_947_, v___y_948_);
lean_dec_ref(v_as_944_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AlphaEqv_eqv___boxed(lean_object* v_pu_953_, lean_object* v_code_u2081_954_, lean_object* v_code_u2082_955_, lean_object* v_a_956_){
_start:
{
uint8_t v_pu_boxed_957_; uint8_t v_res_958_; lean_object* v_r_959_; 
v_pu_boxed_957_ = lean_unbox(v_pu_953_);
v_res_958_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_boxed_957_, v_code_u2081_954_, v_code_u2082_955_, v_a_956_);
v_r_959_ = lean_box(v_res_958_);
return v_r_959_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(uint8_t v_pu_960_, lean_object* v_code_961_, lean_object* v_code_962_, uint8_t v_pu_963_, lean_object* v_params_u2081_964_, lean_object* v_params_u2082_965_, lean_object* v_h_966_, lean_object* v_i_967_, lean_object* v_a_968_){
_start:
{
uint8_t v___x_969_; 
v___x_969_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___redArg(v_pu_960_, v_code_961_, v_code_962_, v_params_u2081_964_, v_params_u2082_965_, v_i_967_, v_a_968_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0___boxed(lean_object* v_pu_970_, lean_object* v_code_971_, lean_object* v_code_972_, lean_object* v_pu_973_, lean_object* v_params_u2081_974_, lean_object* v_params_u2082_975_, lean_object* v_h_976_, lean_object* v_i_977_, lean_object* v_a_978_){
_start:
{
uint8_t v_pu_boxed_979_; uint8_t v_pu_boxed_980_; uint8_t v_res_981_; lean_object* v_r_982_; 
v_pu_boxed_979_ = lean_unbox(v_pu_970_);
v_pu_boxed_980_ = lean_unbox(v_pu_973_);
v_res_981_ = l___private_Lean_Compiler_LCNF_AlphaEqv_0__Lean_Compiler_LCNF_AlphaEqv_withParams_go___at___00Lean_Compiler_LCNF_AlphaEqv_eqvAlts_spec__0(v_pu_boxed_979_, v_code_971_, v_code_972_, v_pu_boxed_980_, v_params_u2081_974_, v_params_u2082_975_, v_h_976_, v_i_977_, v_a_978_);
lean_dec_ref(v_params_u2082_975_);
lean_dec_ref(v_params_u2081_974_);
v_r_982_ = lean_box(v_res_981_);
return v_r_982_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_alphaEqv(uint8_t v_pu_983_, lean_object* v_c_u2081_984_, lean_object* v_c_u2082_985_){
_start:
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = lean_box(1);
v___x_987_ = l_Lean_Compiler_LCNF_AlphaEqv_eqv(v_pu_983_, v_c_u2081_984_, v_c_u2082_985_, v___x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_alphaEqv___boxed(lean_object* v_pu_988_, lean_object* v_c_u2081_989_, lean_object* v_c_u2082_990_){
_start:
{
uint8_t v_pu_boxed_991_; uint8_t v_res_992_; lean_object* v_r_993_; 
v_pu_boxed_991_ = lean_unbox(v_pu_988_);
v_res_992_ = l_Lean_Compiler_LCNF_Code_alphaEqv(v_pu_boxed_991_, v_c_u2081_989_, v_c_u2082_990_);
v_r_993_ = lean_box(v_res_992_);
return v_r_993_;
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
