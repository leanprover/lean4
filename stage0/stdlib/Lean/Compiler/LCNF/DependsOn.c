// Lean compiler output
// Module: Lean.Compiler.LCNF.DependsOn
// Imports: public import Lean.Compiler.LCNF.Basic
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
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_dependsOn___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Arg_dependsOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_dependsOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LetValue_dependsOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_dependsOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LetDecl_dependsOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_dependsOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FunDecl_dependsOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_dependsOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_dependsOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_dependsOn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_dependsOn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(lean_object* v_k_1_, lean_object* v_t_2_){
_start:
{
if (lean_obj_tag(v_t_2_) == 0)
{
lean_object* v_k_3_; lean_object* v_l_4_; lean_object* v_r_5_; uint8_t v___x_6_; 
v_k_3_ = lean_ctor_get(v_t_2_, 1);
v_l_4_ = lean_ctor_get(v_t_2_, 3);
v_r_5_ = lean_ctor_get(v_t_2_, 4);
v___x_6_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1_, v_k_3_);
switch(v___x_6_)
{
case 0:
{
v_t_2_ = v_l_4_;
goto _start;
}
case 1:
{
uint8_t v___x_8_; 
v___x_8_ = 1;
return v___x_8_;
}
default: 
{
v_t_2_ = v_r_5_;
goto _start;
}
}
}
else
{
uint8_t v___x_10_; 
v___x_10_ = 0;
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg___boxed(lean_object* v_k_11_, lean_object* v_t_12_){
_start:
{
uint8_t v_res_13_; lean_object* v_r_14_; 
v_res_13_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_k_11_, v_t_12_);
lean_dec(v_t_12_);
lean_dec(v_k_11_);
v_r_14_ = lean_box(v_res_13_);
return v_r_14_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn(lean_object* v_fvarId_15_, lean_object* v_a_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_15_, v_a_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___boxed(lean_object* v_fvarId_18_, lean_object* v_a_19_){
_start:
{
uint8_t v_res_20_; lean_object* v_r_21_; 
v_res_20_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn(v_fvarId_18_, v_a_19_);
lean_dec(v_a_19_);
lean_dec(v_fvarId_18_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0(lean_object* v_00_u03b2_22_, lean_object* v_k_23_, lean_object* v_t_24_){
_start:
{
uint8_t v___x_25_; 
v___x_25_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_k_23_, v_t_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___boxed(lean_object* v_00_u03b2_26_, lean_object* v_k_27_, lean_object* v_t_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0(v_00_u03b2_26_, v_k_27_, v_t_28_);
lean_dec(v_t_28_);
lean_dec(v_k_27_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(lean_object* v_a_31_, lean_object* v_e_32_){
_start:
{
uint8_t v___x_33_; lean_object* v_d_35_; lean_object* v_b_36_; 
v___x_33_ = l_Lean_Expr_hasFVar(v_e_32_);
if (v___x_33_ == 0)
{
return v___x_33_;
}
else
{
switch(lean_obj_tag(v_e_32_))
{
case 7:
{
lean_object* v_binderType_39_; lean_object* v_body_40_; 
v_binderType_39_ = lean_ctor_get(v_e_32_, 1);
v_body_40_ = lean_ctor_get(v_e_32_, 2);
v_d_35_ = v_binderType_39_;
v_b_36_ = v_body_40_;
goto v___jp_34_;
}
case 6:
{
lean_object* v_binderType_41_; lean_object* v_body_42_; 
v_binderType_41_ = lean_ctor_get(v_e_32_, 1);
v_body_42_ = lean_ctor_get(v_e_32_, 2);
v_d_35_ = v_binderType_41_;
v_b_36_ = v_body_42_;
goto v___jp_34_;
}
case 10:
{
lean_object* v_expr_43_; 
v_expr_43_ = lean_ctor_get(v_e_32_, 1);
v_e_32_ = v_expr_43_;
goto _start;
}
case 8:
{
lean_object* v_type_45_; lean_object* v_value_46_; lean_object* v_body_47_; uint8_t v___x_48_; 
v_type_45_ = lean_ctor_get(v_e_32_, 1);
v_value_46_ = lean_ctor_get(v_e_32_, 2);
v_body_47_ = lean_ctor_get(v_e_32_, 3);
v___x_48_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_31_, v_type_45_);
if (v___x_48_ == 0)
{
uint8_t v___x_49_; 
v___x_49_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_31_, v_value_46_);
if (v___x_49_ == 0)
{
v_e_32_ = v_body_47_;
goto _start;
}
else
{
return v___x_33_;
}
}
else
{
return v___x_33_;
}
}
case 5:
{
lean_object* v_fn_51_; lean_object* v_arg_52_; uint8_t v___x_53_; 
v_fn_51_ = lean_ctor_get(v_e_32_, 0);
v_arg_52_ = lean_ctor_get(v_e_32_, 1);
v___x_53_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_31_, v_fn_51_);
if (v___x_53_ == 0)
{
v_e_32_ = v_arg_52_;
goto _start;
}
else
{
return v___x_33_;
}
}
case 11:
{
lean_object* v_struct_55_; 
v_struct_55_ = lean_ctor_get(v_e_32_, 2);
v_e_32_ = v_struct_55_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_57_; uint8_t v___x_58_; 
v_fvarId_57_ = lean_ctor_get(v_e_32_, 0);
v___x_58_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_57_, v_a_31_);
return v___x_58_;
}
default: 
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
}
}
v___jp_34_:
{
uint8_t v___x_37_; 
v___x_37_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_31_, v_d_35_);
if (v___x_37_ == 0)
{
v_e_32_ = v_b_36_;
goto _start;
}
else
{
return v___x_33_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0___boxed(lean_object* v_a_60_, lean_object* v_e_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_60_, v_e_61_);
lean_dec_ref(v_e_61_);
lean_dec(v_a_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(lean_object* v_e_64_, lean_object* v_a_65_){
_start:
{
uint8_t v___x_66_; 
v___x_66_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_65_, v_e_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn___boxed(lean_object* v_e_67_, lean_object* v_a_68_){
_start:
{
uint8_t v_res_69_; lean_object* v_r_70_; 
v_res_69_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(v_e_67_, v_a_68_);
lean_dec(v_a_68_);
lean_dec_ref(v_e_67_);
v_r_70_ = lean_box(v_res_69_);
return v_r_70_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
switch(lean_obj_tag(v_a_71_))
{
case 0:
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
case 1:
{
lean_object* v_fvarId_74_; uint8_t v___x_75_; 
v_fvarId_74_ = lean_ctor_get(v_a_71_, 0);
v___x_75_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_74_, v_a_72_);
return v___x_75_;
}
default: 
{
lean_object* v_expr_76_; uint8_t v___x_77_; 
v_expr_76_ = lean_ctor_get(v_a_71_, 0);
v___x_77_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_72_, v_expr_76_);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg___boxed(lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_a_78_, v_a_79_);
lean_dec(v_a_79_);
lean_dec(v_a_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t v_pu_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_a_83_, v_a_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___boxed(lean_object* v_pu_86_, lean_object* v_a_87_, lean_object* v_a_88_){
_start:
{
uint8_t v_pu_boxed_89_; uint8_t v_res_90_; lean_object* v_r_91_; 
v_pu_boxed_89_ = lean_unbox(v_pu_86_);
v_res_90_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v_pu_boxed_89_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec(v_a_87_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(lean_object* v_as_92_, size_t v_i_93_, size_t v_stop_94_, lean_object* v___y_95_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lean_usize_dec_eq(v_i_93_, v_stop_94_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_array_uget_borrowed(v_as_92_, v_i_93_);
v___x_98_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v___x_97_, v___y_95_);
if (v___x_98_ == 0)
{
size_t v___x_99_; size_t v___x_100_; 
v___x_99_ = ((size_t)1ULL);
v___x_100_ = lean_usize_add(v_i_93_, v___x_99_);
v_i_93_ = v___x_100_;
goto _start;
}
else
{
return v___x_98_;
}
}
else
{
uint8_t v___x_102_; 
v___x_102_ = 0;
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg___boxed(lean_object* v_as_103_, lean_object* v_i_104_, lean_object* v_stop_105_, lean_object* v___y_106_){
_start:
{
size_t v_i_boxed_107_; size_t v_stop_boxed_108_; uint8_t v_res_109_; lean_object* v_r_110_; 
v_i_boxed_107_ = lean_unbox_usize(v_i_104_);
lean_dec(v_i_104_);
v_stop_boxed_108_ = lean_unbox_usize(v_stop_105_);
lean_dec(v_stop_105_);
v_res_109_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_as_103_, v_i_boxed_107_, v_stop_boxed_108_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v_as_103_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(uint8_t v_pu_111_, lean_object* v_e_112_, lean_object* v_a_113_){
_start:
{
lean_object* v_args_115_; lean_object* v___y_116_; 
switch(lean_obj_tag(v_e_112_))
{
case 2:
{
lean_object* v_struct_123_; uint8_t v___x_124_; 
v_struct_123_ = lean_ctor_get(v_e_112_, 2);
v___x_124_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_struct_123_, v_a_113_);
return v___x_124_;
}
case 3:
{
lean_object* v_args_125_; lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_args_125_ = lean_ctor_get(v_e_112_, 2);
v___x_126_ = lean_unsigned_to_nat(0u);
v___x_127_ = lean_array_get_size(v_args_125_);
v___x_128_ = lean_nat_dec_lt(v___x_126_, v___x_127_);
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
if (v___x_128_ == 0)
{
return v___x_128_;
}
else
{
size_t v___x_129_; size_t v___x_130_; uint8_t v___x_131_; 
v___x_129_ = ((size_t)0ULL);
v___x_130_ = lean_usize_of_nat(v___x_127_);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_125_, v___x_129_, v___x_130_, v_a_113_);
return v___x_131_;
}
}
}
case 4:
{
lean_object* v_fvarId_132_; lean_object* v_args_133_; uint8_t v___x_134_; 
v_fvarId_132_ = lean_ctor_get(v_e_112_, 0);
v_args_133_ = lean_ctor_get(v_e_112_, 1);
v___x_134_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_132_, v_a_113_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = lean_array_get_size(v_args_133_);
v___x_137_ = lean_nat_dec_lt(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
return v___x_134_;
}
else
{
if (v___x_137_ == 0)
{
return v___x_134_;
}
else
{
size_t v___x_138_; size_t v___x_139_; uint8_t v___x_140_; 
v___x_138_ = ((size_t)0ULL);
v___x_139_ = lean_usize_of_nat(v___x_136_);
v___x_140_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_133_, v___x_138_, v___x_139_, v_a_113_);
return v___x_140_;
}
}
}
else
{
return v___x_134_;
}
}
case 5:
{
lean_object* v_args_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_args_141_ = lean_ctor_get(v_e_112_, 1);
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = lean_array_get_size(v_args_141_);
v___x_144_ = lean_nat_dec_lt(v___x_142_, v___x_143_);
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
if (v___x_144_ == 0)
{
return v___x_144_;
}
else
{
size_t v___x_145_; size_t v___x_146_; uint8_t v___x_147_; 
v___x_145_ = ((size_t)0ULL);
v___x_146_ = lean_usize_of_nat(v___x_143_);
v___x_147_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_141_, v___x_145_, v___x_146_, v_a_113_);
return v___x_147_;
}
}
}
case 6:
{
lean_object* v_var_148_; uint8_t v___x_149_; 
v_var_148_ = lean_ctor_get(v_e_112_, 1);
v___x_149_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_148_, v_a_113_);
return v___x_149_;
}
case 7:
{
lean_object* v_var_150_; uint8_t v___x_151_; 
v_var_150_ = lean_ctor_get(v_e_112_, 1);
v___x_151_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_150_, v_a_113_);
return v___x_151_;
}
case 8:
{
lean_object* v_var_152_; uint8_t v___x_153_; 
v_var_152_ = lean_ctor_get(v_e_112_, 2);
v___x_153_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_152_, v_a_113_);
return v___x_153_;
}
case 9:
{
lean_object* v_args_154_; 
v_args_154_ = lean_ctor_get(v_e_112_, 1);
v_args_115_ = v_args_154_;
v___y_116_ = v_a_113_;
goto v___jp_114_;
}
case 10:
{
lean_object* v_args_155_; 
v_args_155_ = lean_ctor_get(v_e_112_, 1);
v_args_115_ = v_args_155_;
v___y_116_ = v_a_113_;
goto v___jp_114_;
}
case 11:
{
lean_object* v_var_156_; uint8_t v___x_157_; 
v_var_156_ = lean_ctor_get(v_e_112_, 1);
v___x_157_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_156_, v_a_113_);
return v___x_157_;
}
case 12:
{
lean_object* v_var_158_; lean_object* v_args_159_; uint8_t v___x_160_; 
v_var_158_ = lean_ctor_get(v_e_112_, 0);
v_args_159_ = lean_ctor_get(v_e_112_, 2);
v___x_160_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_158_, v_a_113_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_array_get_size(v_args_159_);
v___x_163_ = lean_nat_dec_lt(v___x_161_, v___x_162_);
if (v___x_163_ == 0)
{
return v___x_160_;
}
else
{
if (v___x_163_ == 0)
{
return v___x_160_;
}
else
{
size_t v___x_164_; size_t v___x_165_; uint8_t v___x_166_; 
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_162_);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_159_, v___x_164_, v___x_165_, v_a_113_);
return v___x_166_;
}
}
}
else
{
return v___x_160_;
}
}
case 13:
{
lean_object* v_fvarId_167_; uint8_t v___x_168_; 
v_fvarId_167_ = lean_ctor_get(v_e_112_, 1);
v___x_168_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_167_, v_a_113_);
return v___x_168_;
}
case 14:
{
lean_object* v_fvarId_169_; uint8_t v___x_170_; 
v_fvarId_169_ = lean_ctor_get(v_e_112_, 0);
v___x_170_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_169_, v_a_113_);
return v___x_170_;
}
case 15:
{
lean_object* v_fvarId_171_; uint8_t v___x_172_; 
v_fvarId_171_ = lean_ctor_get(v_e_112_, 0);
v___x_172_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_171_, v_a_113_);
return v___x_172_;
}
default: 
{
uint8_t v___x_173_; 
v___x_173_ = 0;
return v___x_173_;
}
}
v___jp_114_:
{
lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_117_ = lean_unsigned_to_nat(0u);
v___x_118_ = lean_array_get_size(v_args_115_);
v___x_119_ = lean_nat_dec_lt(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
return v___x_119_;
}
else
{
if (v___x_119_ == 0)
{
return v___x_119_;
}
else
{
size_t v___x_120_; size_t v___x_121_; uint8_t v___x_122_; 
v___x_120_ = ((size_t)0ULL);
v___x_121_ = lean_usize_of_nat(v___x_118_);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_115_, v___x_120_, v___x_121_, v___y_116_);
return v___x_122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn___boxed(lean_object* v_pu_174_, lean_object* v_e_175_, lean_object* v_a_176_){
_start:
{
uint8_t v_pu_boxed_177_; uint8_t v_res_178_; lean_object* v_r_179_; 
v_pu_boxed_177_ = lean_unbox(v_pu_174_);
v_res_178_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_boxed_177_, v_e_175_, v_a_176_);
lean_dec(v_a_176_);
lean_dec(v_e_175_);
v_r_179_ = lean_box(v_res_178_);
return v_r_179_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(uint8_t v_pu_180_, lean_object* v_as_181_, size_t v_i_182_, size_t v_stop_183_, lean_object* v___y_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_as_181_, v_i_182_, v_stop_183_, v___y_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___boxed(lean_object* v_pu_186_, lean_object* v_as_187_, lean_object* v_i_188_, lean_object* v_stop_189_, lean_object* v___y_190_){
_start:
{
uint8_t v_pu_boxed_191_; size_t v_i_boxed_192_; size_t v_stop_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_pu_boxed_191_ = lean_unbox(v_pu_186_);
v_i_boxed_192_ = lean_unbox_usize(v_i_188_);
lean_dec(v_i_188_);
v_stop_boxed_193_ = lean_unbox_usize(v_stop_189_);
lean_dec(v_stop_189_);
v_res_194_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(v_pu_boxed_191_, v_as_187_, v_i_boxed_192_, v_stop_boxed_193_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v_as_187_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(uint8_t v_pu_196_, lean_object* v_decl_197_, lean_object* v_a_198_){
_start:
{
lean_object* v_type_199_; lean_object* v_value_200_; uint8_t v___x_201_; 
v_type_199_ = lean_ctor_get(v_decl_197_, 2);
v_value_200_ = lean_ctor_get(v_decl_197_, 3);
v___x_201_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_198_, v_type_199_);
if (v___x_201_ == 0)
{
uint8_t v___x_202_; 
v___x_202_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_196_, v_value_200_, v_a_198_);
return v___x_202_;
}
else
{
return v___x_201_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn___boxed(lean_object* v_pu_203_, lean_object* v_decl_204_, lean_object* v_a_205_){
_start:
{
uint8_t v_pu_boxed_206_; uint8_t v_res_207_; lean_object* v_r_208_; 
v_pu_boxed_206_ = lean_unbox(v_pu_203_);
v_res_207_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_boxed_206_, v_decl_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_decl_204_);
v_r_208_ = lean_box(v_res_207_);
return v_r_208_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(uint8_t v_pu_209_, lean_object* v_c_210_, lean_object* v_a_211_){
_start:
{
switch(lean_obj_tag(v_c_210_))
{
case 0:
{
lean_object* v_decl_212_; lean_object* v_k_213_; uint8_t v___x_214_; 
v_decl_212_ = lean_ctor_get(v_c_210_, 0);
v_k_213_ = lean_ctor_get(v_c_210_, 1);
v___x_214_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_209_, v_decl_212_, v_a_211_);
if (v___x_214_ == 0)
{
v_c_210_ = v_k_213_;
goto _start;
}
else
{
return v___x_214_;
}
}
case 3:
{
lean_object* v_fvarId_216_; lean_object* v_args_217_; uint8_t v___x_218_; 
v_fvarId_216_ = lean_ctor_get(v_c_210_, 0);
v_args_217_ = lean_ctor_get(v_c_210_, 1);
v___x_218_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_216_, v_a_211_);
if (v___x_218_ == 0)
{
lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_array_get_size(v_args_217_);
v___x_221_ = lean_nat_dec_lt(v___x_219_, v___x_220_);
if (v___x_221_ == 0)
{
return v___x_218_;
}
else
{
if (v___x_221_ == 0)
{
return v___x_218_;
}
else
{
size_t v___x_222_; size_t v___x_223_; uint8_t v___x_224_; 
v___x_222_ = ((size_t)0ULL);
v___x_223_ = lean_usize_of_nat(v___x_220_);
v___x_224_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_217_, v___x_222_, v___x_223_, v_a_211_);
return v___x_224_;
}
}
}
else
{
return v___x_218_;
}
}
case 4:
{
lean_object* v_cases_225_; lean_object* v_resultType_226_; lean_object* v_discr_227_; lean_object* v_alts_228_; uint8_t v___x_229_; 
v_cases_225_ = lean_ctor_get(v_c_210_, 0);
v_resultType_226_ = lean_ctor_get(v_cases_225_, 1);
v_discr_227_ = lean_ctor_get(v_cases_225_, 2);
v_alts_228_ = lean_ctor_get(v_cases_225_, 3);
v___x_229_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_211_, v_resultType_226_);
if (v___x_229_ == 0)
{
uint8_t v___x_230_; 
v___x_230_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_discr_227_, v_a_211_);
if (v___x_230_ == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_array_get_size(v_alts_228_);
v___x_233_ = lean_nat_dec_lt(v___x_231_, v___x_232_);
if (v___x_233_ == 0)
{
return v___x_230_;
}
else
{
if (v___x_233_ == 0)
{
return v___x_230_;
}
else
{
size_t v___x_234_; size_t v___x_235_; uint8_t v___x_236_; 
v___x_234_ = ((size_t)0ULL);
v___x_235_ = lean_usize_of_nat(v___x_232_);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(v_pu_209_, v_alts_228_, v___x_234_, v___x_235_, v_a_211_);
return v___x_236_;
}
}
}
else
{
return v___x_230_;
}
}
else
{
return v___x_229_;
}
}
case 5:
{
lean_object* v_fvarId_237_; uint8_t v___x_238_; 
v_fvarId_237_ = lean_ctor_get(v_c_210_, 0);
v___x_238_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_237_, v_a_211_);
return v___x_238_;
}
case 6:
{
uint8_t v___x_239_; 
v___x_239_ = 0;
return v___x_239_;
}
case 7:
{
lean_object* v_fvarId_240_; lean_object* v_y_241_; lean_object* v_k_242_; uint8_t v___x_243_; 
v_fvarId_240_ = lean_ctor_get(v_c_210_, 0);
v_y_241_ = lean_ctor_get(v_c_210_, 2);
v_k_242_ = lean_ctor_get(v_c_210_, 3);
v___x_243_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_240_, v_a_211_);
if (v___x_243_ == 0)
{
uint8_t v___x_244_; 
v___x_244_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_y_241_, v_a_211_);
if (v___x_244_ == 0)
{
v_c_210_ = v_k_242_;
goto _start;
}
else
{
return v___x_244_;
}
}
else
{
return v___x_243_;
}
}
case 8:
{
lean_object* v_fvarId_246_; lean_object* v_y_247_; lean_object* v_k_248_; uint8_t v___x_249_; 
v_fvarId_246_ = lean_ctor_get(v_c_210_, 0);
v_y_247_ = lean_ctor_get(v_c_210_, 2);
v_k_248_ = lean_ctor_get(v_c_210_, 3);
v___x_249_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_246_, v_a_211_);
if (v___x_249_ == 0)
{
uint8_t v___x_250_; 
v___x_250_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_247_, v_a_211_);
if (v___x_250_ == 0)
{
v_c_210_ = v_k_248_;
goto _start;
}
else
{
return v___x_250_;
}
}
else
{
return v___x_249_;
}
}
case 9:
{
lean_object* v_fvarId_252_; lean_object* v_y_253_; lean_object* v_k_254_; uint8_t v___x_255_; 
v_fvarId_252_ = lean_ctor_get(v_c_210_, 0);
v_y_253_ = lean_ctor_get(v_c_210_, 3);
v_k_254_ = lean_ctor_get(v_c_210_, 5);
v___x_255_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_252_, v_a_211_);
if (v___x_255_ == 0)
{
uint8_t v___x_256_; 
v___x_256_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_253_, v_a_211_);
if (v___x_256_ == 0)
{
v_c_210_ = v_k_254_;
goto _start;
}
else
{
return v___x_256_;
}
}
else
{
return v___x_255_;
}
}
case 10:
{
lean_object* v_fvarId_258_; lean_object* v_k_259_; uint8_t v___x_260_; 
v_fvarId_258_ = lean_ctor_get(v_c_210_, 0);
v_k_259_ = lean_ctor_get(v_c_210_, 2);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_258_, v_a_211_);
if (v___x_260_ == 0)
{
v_c_210_ = v_k_259_;
goto _start;
}
else
{
return v___x_260_;
}
}
case 11:
{
lean_object* v_fvarId_262_; lean_object* v_k_263_; uint8_t v___x_264_; 
v_fvarId_262_ = lean_ctor_get(v_c_210_, 0);
v_k_263_ = lean_ctor_get(v_c_210_, 2);
v___x_264_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_262_, v_a_211_);
if (v___x_264_ == 0)
{
v_c_210_ = v_k_263_;
goto _start;
}
else
{
return v___x_264_;
}
}
case 12:
{
lean_object* v_fvarId_266_; lean_object* v_k_267_; uint8_t v___x_268_; 
v_fvarId_266_ = lean_ctor_get(v_c_210_, 0);
v_k_267_ = lean_ctor_get(v_c_210_, 3);
v___x_268_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_266_, v_a_211_);
if (v___x_268_ == 0)
{
v_c_210_ = v_k_267_;
goto _start;
}
else
{
return v___x_268_;
}
}
case 13:
{
lean_object* v_fvarId_270_; lean_object* v_k_271_; uint8_t v___x_272_; 
v_fvarId_270_ = lean_ctor_get(v_c_210_, 0);
v_k_271_ = lean_ctor_get(v_c_210_, 1);
v___x_272_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_270_, v_a_211_);
if (v___x_272_ == 0)
{
v_c_210_ = v_k_271_;
goto _start;
}
else
{
return v___x_272_;
}
}
default: 
{
lean_object* v_decl_274_; lean_object* v_k_275_; lean_object* v_type_276_; lean_object* v_value_277_; uint8_t v___x_278_; 
v_decl_274_ = lean_ctor_get(v_c_210_, 0);
v_k_275_ = lean_ctor_get(v_c_210_, 1);
v_type_276_ = lean_ctor_get(v_decl_274_, 3);
v_value_277_ = lean_ctor_get(v_decl_274_, 4);
v___x_278_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_211_, v_type_276_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; 
v___x_279_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_209_, v_value_277_, v_a_211_);
if (v___x_279_ == 0)
{
v_c_210_ = v_k_275_;
goto _start;
}
else
{
return v___x_279_;
}
}
else
{
return v___x_278_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(uint8_t v_pu_281_, lean_object* v_as_282_, size_t v_i_283_, size_t v_stop_284_, lean_object* v___y_285_){
_start:
{
uint8_t v___x_286_; 
v___x_286_ = lean_usize_dec_eq(v_i_283_, v_stop_284_);
if (v___x_286_ == 0)
{
uint8_t v___x_287_; lean_object* v___y_289_; lean_object* v___x_294_; 
v___x_287_ = 1;
v___x_294_ = lean_array_uget_borrowed(v_as_282_, v_i_283_);
switch(lean_obj_tag(v___x_294_))
{
case 0:
{
lean_object* v_code_295_; 
v_code_295_ = lean_ctor_get(v___x_294_, 2);
v___y_289_ = v_code_295_;
goto v___jp_288_;
}
case 1:
{
lean_object* v_code_296_; 
v_code_296_ = lean_ctor_get(v___x_294_, 1);
v___y_289_ = v_code_296_;
goto v___jp_288_;
}
default: 
{
lean_object* v_code_297_; 
v_code_297_ = lean_ctor_get(v___x_294_, 0);
v___y_289_ = v_code_297_;
goto v___jp_288_;
}
}
v___jp_288_:
{
uint8_t v___x_290_; 
v___x_290_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_281_, v___y_289_, v___y_285_);
if (v___x_290_ == 0)
{
size_t v___x_291_; size_t v___x_292_; 
v___x_291_ = ((size_t)1ULL);
v___x_292_ = lean_usize_add(v_i_283_, v___x_291_);
v_i_283_ = v___x_292_;
goto _start;
}
else
{
return v___x_287_;
}
}
}
else
{
uint8_t v___x_298_; 
v___x_298_ = 0;
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0___boxed(lean_object* v_pu_299_, lean_object* v_as_300_, lean_object* v_i_301_, lean_object* v_stop_302_, lean_object* v___y_303_){
_start:
{
uint8_t v_pu_boxed_304_; size_t v_i_boxed_305_; size_t v_stop_boxed_306_; uint8_t v_res_307_; lean_object* v_r_308_; 
v_pu_boxed_304_ = lean_unbox(v_pu_299_);
v_i_boxed_305_ = lean_unbox_usize(v_i_301_);
lean_dec(v_i_301_);
v_stop_boxed_306_ = lean_unbox_usize(v_stop_302_);
lean_dec(v_stop_302_);
v_res_307_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(v_pu_boxed_304_, v_as_300_, v_i_boxed_305_, v_stop_boxed_306_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v_as_300_);
v_r_308_ = lean_box(v_res_307_);
return v_r_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn___boxed(lean_object* v_pu_309_, lean_object* v_c_310_, lean_object* v_a_311_){
_start:
{
uint8_t v_pu_boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v_pu_boxed_312_ = lean_unbox(v_pu_309_);
v_res_313_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_boxed_312_, v_c_310_, v_a_311_);
lean_dec(v_a_311_);
lean_dec_ref(v_c_310_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(lean_object* v_arg_315_, lean_object* v_s_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_arg_315_, v_s_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_dependsOn___redArg___boxed(lean_object* v_arg_318_, lean_object* v_s_319_){
_start:
{
uint8_t v_res_320_; lean_object* v_r_321_; 
v_res_320_ = l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(v_arg_318_, v_s_319_);
lean_dec(v_s_319_);
lean_dec(v_arg_318_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Arg_dependsOn(uint8_t v_pu_322_, lean_object* v_arg_323_, lean_object* v_s_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_arg_323_, v_s_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_dependsOn___boxed(lean_object* v_pu_326_, lean_object* v_arg_327_, lean_object* v_s_328_){
_start:
{
uint8_t v_pu_boxed_329_; uint8_t v_res_330_; lean_object* v_r_331_; 
v_pu_boxed_329_ = lean_unbox(v_pu_326_);
v_res_330_ = l_Lean_Compiler_LCNF_Arg_dependsOn(v_pu_boxed_329_, v_arg_327_, v_s_328_);
lean_dec(v_s_328_);
lean_dec(v_arg_327_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LetValue_dependsOn(uint8_t v_pu_332_, lean_object* v_value_333_, lean_object* v_s_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_332_, v_value_333_, v_s_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_dependsOn___boxed(lean_object* v_pu_336_, lean_object* v_value_337_, lean_object* v_s_338_){
_start:
{
uint8_t v_pu_boxed_339_; uint8_t v_res_340_; lean_object* v_r_341_; 
v_pu_boxed_339_ = lean_unbox(v_pu_336_);
v_res_340_ = l_Lean_Compiler_LCNF_LetValue_dependsOn(v_pu_boxed_339_, v_value_337_, v_s_338_);
lean_dec(v_s_338_);
lean_dec(v_value_337_);
v_r_341_ = lean_box(v_res_340_);
return v_r_341_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LetDecl_dependsOn(uint8_t v_pu_342_, lean_object* v_decl_343_, lean_object* v_s_344_){
_start:
{
uint8_t v___x_345_; 
v___x_345_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_342_, v_decl_343_, v_s_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_dependsOn___boxed(lean_object* v_pu_346_, lean_object* v_decl_347_, lean_object* v_s_348_){
_start:
{
uint8_t v_pu_boxed_349_; uint8_t v_res_350_; lean_object* v_r_351_; 
v_pu_boxed_349_ = lean_unbox(v_pu_346_);
v_res_350_ = l_Lean_Compiler_LCNF_LetDecl_dependsOn(v_pu_boxed_349_, v_decl_347_, v_s_348_);
lean_dec(v_s_348_);
lean_dec_ref(v_decl_347_);
v_r_351_ = lean_box(v_res_350_);
return v_r_351_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FunDecl_dependsOn(uint8_t v_pu_352_, lean_object* v_decl_353_, lean_object* v_s_354_){
_start:
{
lean_object* v_type_355_; lean_object* v_value_356_; uint8_t v___x_357_; 
v_type_355_ = lean_ctor_get(v_decl_353_, 3);
v_value_356_ = lean_ctor_get(v_decl_353_, 4);
v___x_357_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_354_, v_type_355_);
if (v___x_357_ == 0)
{
uint8_t v___x_358_; 
v___x_358_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_352_, v_value_356_, v_s_354_);
return v___x_358_;
}
else
{
return v___x_357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_dependsOn___boxed(lean_object* v_pu_359_, lean_object* v_decl_360_, lean_object* v_s_361_){
_start:
{
uint8_t v_pu_boxed_362_; uint8_t v_res_363_; lean_object* v_r_364_; 
v_pu_boxed_362_ = lean_unbox(v_pu_359_);
v_res_363_ = l_Lean_Compiler_LCNF_FunDecl_dependsOn(v_pu_boxed_362_, v_decl_360_, v_s_361_);
lean_dec(v_s_361_);
lean_dec_ref(v_decl_360_);
v_r_364_ = lean_box(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t v_pu_365_, lean_object* v_decl_366_, lean_object* v_s_367_){
_start:
{
switch(lean_obj_tag(v_decl_366_))
{
case 0:
{
lean_object* v_decl_368_; uint8_t v___x_369_; 
v_decl_368_ = lean_ctor_get(v_decl_366_, 0);
v___x_369_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_365_, v_decl_368_, v_s_367_);
return v___x_369_;
}
case 1:
{
lean_object* v_decl_370_; lean_object* v_type_371_; lean_object* v_value_372_; uint8_t v___x_373_; 
v_decl_370_ = lean_ctor_get(v_decl_366_, 0);
v_type_371_ = lean_ctor_get(v_decl_370_, 3);
v_value_372_ = lean_ctor_get(v_decl_370_, 4);
v___x_373_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_367_, v_type_371_);
if (v___x_373_ == 0)
{
uint8_t v___x_374_; 
v___x_374_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_365_, v_value_372_, v_s_367_);
return v___x_374_;
}
else
{
return v___x_373_;
}
}
case 2:
{
lean_object* v_decl_375_; lean_object* v_type_376_; lean_object* v_value_377_; uint8_t v___x_378_; 
v_decl_375_ = lean_ctor_get(v_decl_366_, 0);
v_type_376_ = lean_ctor_get(v_decl_375_, 3);
v_value_377_ = lean_ctor_get(v_decl_375_, 4);
v___x_378_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_367_, v_type_376_);
if (v___x_378_ == 0)
{
uint8_t v___x_379_; 
v___x_379_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_365_, v_value_377_, v_s_367_);
return v___x_379_;
}
else
{
return v___x_378_;
}
}
case 3:
{
lean_object* v_fvarId_380_; lean_object* v_y_381_; uint8_t v___x_382_; 
v_fvarId_380_ = lean_ctor_get(v_decl_366_, 0);
v_y_381_ = lean_ctor_get(v_decl_366_, 2);
v___x_382_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_380_, v_s_367_);
if (v___x_382_ == 0)
{
uint8_t v___x_383_; 
v___x_383_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_y_381_, v_s_367_);
return v___x_383_;
}
else
{
return v___x_382_;
}
}
case 4:
{
lean_object* v_fvarId_384_; lean_object* v_y_385_; uint8_t v___x_386_; 
v_fvarId_384_ = lean_ctor_get(v_decl_366_, 0);
v_y_385_ = lean_ctor_get(v_decl_366_, 2);
v___x_386_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_384_, v_s_367_);
if (v___x_386_ == 0)
{
uint8_t v___x_387_; 
v___x_387_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_385_, v_s_367_);
return v___x_387_;
}
else
{
return v___x_386_;
}
}
case 5:
{
lean_object* v_fvarId_388_; lean_object* v_y_389_; uint8_t v___x_390_; 
v_fvarId_388_ = lean_ctor_get(v_decl_366_, 0);
v_y_389_ = lean_ctor_get(v_decl_366_, 3);
v___x_390_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_388_, v_s_367_);
if (v___x_390_ == 0)
{
uint8_t v___x_391_; 
v___x_391_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_389_, v_s_367_);
return v___x_391_;
}
else
{
return v___x_390_;
}
}
default: 
{
lean_object* v_fvarId_392_; uint8_t v___x_393_; 
v_fvarId_392_ = lean_ctor_get(v_decl_366_, 0);
v___x_393_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_392_, v_s_367_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_dependsOn___boxed(lean_object* v_pu_394_, lean_object* v_decl_395_, lean_object* v_s_396_){
_start:
{
uint8_t v_pu_boxed_397_; uint8_t v_res_398_; lean_object* v_r_399_; 
v_pu_boxed_397_ = lean_unbox(v_pu_394_);
v_res_398_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v_pu_boxed_397_, v_decl_395_, v_s_396_);
lean_dec(v_s_396_);
lean_dec_ref(v_decl_395_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_dependsOn(uint8_t v_pu_400_, lean_object* v_c_401_, lean_object* v_s_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_400_, v_c_401_, v_s_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_dependsOn___boxed(lean_object* v_pu_404_, lean_object* v_c_405_, lean_object* v_s_406_){
_start:
{
uint8_t v_pu_boxed_407_; uint8_t v_res_408_; lean_object* v_r_409_; 
v_pu_boxed_407_ = lean_unbox(v_pu_404_);
v_res_408_ = l_Lean_Compiler_LCNF_Code_dependsOn(v_pu_boxed_407_, v_c_405_, v_s_406_);
lean_dec(v_s_406_);
lean_dec_ref(v_c_405_);
v_r_409_ = lean_box(v_res_408_);
return v_r_409_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_DependsOn(builtin);
}
#ifdef __cplusplus
}
#endif
