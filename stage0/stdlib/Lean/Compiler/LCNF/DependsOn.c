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
uint8_t lean_bool_not(uint8_t);
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
uint8_t v___x_33_; uint8_t v___x_34_; 
v___x_33_ = l_Lean_Expr_hasFVar(v_e_32_);
v___x_34_ = lean_bool_not(v___x_33_);
if (v___x_34_ == 0)
{
uint8_t v___x_35_; lean_object* v_d_37_; lean_object* v_b_38_; 
v___x_35_ = 1;
switch(lean_obj_tag(v_e_32_))
{
case 7:
{
lean_object* v_binderType_41_; lean_object* v_body_42_; 
v_binderType_41_ = lean_ctor_get(v_e_32_, 1);
v_body_42_ = lean_ctor_get(v_e_32_, 2);
v_d_37_ = v_binderType_41_;
v_b_38_ = v_body_42_;
goto v___jp_36_;
}
case 6:
{
lean_object* v_binderType_43_; lean_object* v_body_44_; 
v_binderType_43_ = lean_ctor_get(v_e_32_, 1);
v_body_44_ = lean_ctor_get(v_e_32_, 2);
v_d_37_ = v_binderType_43_;
v_b_38_ = v_body_44_;
goto v___jp_36_;
}
case 10:
{
lean_object* v_expr_45_; 
v_expr_45_ = lean_ctor_get(v_e_32_, 1);
v_e_32_ = v_expr_45_;
goto _start;
}
case 8:
{
lean_object* v_type_47_; lean_object* v_value_48_; lean_object* v_body_49_; uint8_t v___x_50_; 
v_type_47_ = lean_ctor_get(v_e_32_, 1);
v_value_48_ = lean_ctor_get(v_e_32_, 2);
v_body_49_ = lean_ctor_get(v_e_32_, 3);
v___x_50_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_31_, v_type_47_);
if (v___x_50_ == 0)
{
uint8_t v___x_51_; 
v___x_51_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_31_, v_value_48_);
if (v___x_51_ == 0)
{
v_e_32_ = v_body_49_;
goto _start;
}
else
{
return v___x_35_;
}
}
else
{
return v___x_35_;
}
}
case 5:
{
lean_object* v_fn_53_; lean_object* v_arg_54_; uint8_t v___x_55_; 
v_fn_53_ = lean_ctor_get(v_e_32_, 0);
v_arg_54_ = lean_ctor_get(v_e_32_, 1);
v___x_55_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_31_, v_fn_53_);
if (v___x_55_ == 0)
{
v_e_32_ = v_arg_54_;
goto _start;
}
else
{
return v___x_35_;
}
}
case 11:
{
lean_object* v_struct_57_; 
v_struct_57_ = lean_ctor_get(v_e_32_, 2);
v_e_32_ = v_struct_57_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_59_; uint8_t v___x_60_; 
v_fvarId_59_ = lean_ctor_get(v_e_32_, 0);
v___x_60_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_59_, v_a_31_);
return v___x_60_;
}
default: 
{
return v___x_34_;
}
}
v___jp_36_:
{
uint8_t v___x_39_; 
v___x_39_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_31_, v_d_37_);
if (v___x_39_ == 0)
{
v_e_32_ = v_b_38_;
goto _start;
}
else
{
return v___x_35_;
}
}
}
else
{
uint8_t v___x_61_; 
v___x_61_ = 0;
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0___boxed(lean_object* v_a_62_, lean_object* v_e_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_62_, v_e_63_);
lean_dec_ref(v_e_63_);
lean_dec(v_a_62_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(lean_object* v_e_66_, lean_object* v_a_67_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_67_, v_e_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn___boxed(lean_object* v_e_69_, lean_object* v_a_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(v_e_69_, v_a_70_);
lean_dec(v_a_70_);
lean_dec_ref(v_e_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
switch(lean_obj_tag(v_a_73_))
{
case 0:
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
case 1:
{
lean_object* v_fvarId_76_; uint8_t v___x_77_; 
v_fvarId_76_ = lean_ctor_get(v_a_73_, 0);
v___x_77_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_76_, v_a_74_);
return v___x_77_;
}
default: 
{
lean_object* v_expr_78_; uint8_t v___x_79_; 
v_expr_78_ = lean_ctor_get(v_a_73_, 0);
v___x_79_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_74_, v_expr_78_);
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg___boxed(lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_a_80_, v_a_81_);
lean_dec(v_a_81_);
lean_dec(v_a_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t v_pu_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_a_85_, v_a_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___boxed(lean_object* v_pu_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
uint8_t v_pu_boxed_91_; uint8_t v_res_92_; lean_object* v_r_93_; 
v_pu_boxed_91_ = lean_unbox(v_pu_88_);
v_res_92_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v_pu_boxed_91_, v_a_89_, v_a_90_);
lean_dec(v_a_90_);
lean_dec(v_a_89_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(lean_object* v_as_94_, size_t v_i_95_, size_t v_stop_96_, lean_object* v___y_97_){
_start:
{
uint8_t v___x_98_; 
v___x_98_ = lean_usize_dec_eq(v_i_95_, v_stop_96_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; uint8_t v___x_100_; 
v___x_99_ = lean_array_uget_borrowed(v_as_94_, v_i_95_);
v___x_100_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v___x_99_, v___y_97_);
if (v___x_100_ == 0)
{
size_t v___x_101_; size_t v___x_102_; 
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_add(v_i_95_, v___x_101_);
v_i_95_ = v___x_102_;
goto _start;
}
else
{
return v___x_100_;
}
}
else
{
uint8_t v___x_104_; 
v___x_104_ = 0;
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg___boxed(lean_object* v_as_105_, lean_object* v_i_106_, lean_object* v_stop_107_, lean_object* v___y_108_){
_start:
{
size_t v_i_boxed_109_; size_t v_stop_boxed_110_; uint8_t v_res_111_; lean_object* v_r_112_; 
v_i_boxed_109_ = lean_unbox_usize(v_i_106_);
lean_dec(v_i_106_);
v_stop_boxed_110_ = lean_unbox_usize(v_stop_107_);
lean_dec(v_stop_107_);
v_res_111_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_as_105_, v_i_boxed_109_, v_stop_boxed_110_, v___y_108_);
lean_dec(v___y_108_);
lean_dec_ref(v_as_105_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(uint8_t v_pu_113_, lean_object* v_e_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_args_117_; lean_object* v___y_118_; 
switch(lean_obj_tag(v_e_114_))
{
case 2:
{
lean_object* v_struct_125_; uint8_t v___x_126_; 
v_struct_125_ = lean_ctor_get(v_e_114_, 2);
v___x_126_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_struct_125_, v_a_115_);
return v___x_126_;
}
case 3:
{
lean_object* v_args_127_; lean_object* v___x_128_; lean_object* v___x_129_; uint8_t v___x_130_; 
v_args_127_ = lean_ctor_get(v_e_114_, 2);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_array_get_size(v_args_127_);
v___x_130_ = lean_nat_dec_lt(v___x_128_, v___x_129_);
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
if (v___x_130_ == 0)
{
return v___x_130_;
}
else
{
size_t v___x_131_; size_t v___x_132_; uint8_t v___x_133_; 
v___x_131_ = ((size_t)0ULL);
v___x_132_ = lean_usize_of_nat(v___x_129_);
v___x_133_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_127_, v___x_131_, v___x_132_, v_a_115_);
return v___x_133_;
}
}
}
case 4:
{
lean_object* v_fvarId_134_; lean_object* v_args_135_; uint8_t v___x_136_; 
v_fvarId_134_ = lean_ctor_get(v_e_114_, 0);
v_args_135_ = lean_ctor_get(v_e_114_, 1);
v___x_136_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_134_, v_a_115_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_137_ = lean_unsigned_to_nat(0u);
v___x_138_ = lean_array_get_size(v_args_135_);
v___x_139_ = lean_nat_dec_lt(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
return v___x_136_;
}
else
{
if (v___x_139_ == 0)
{
return v___x_136_;
}
else
{
size_t v___x_140_; size_t v___x_141_; uint8_t v___x_142_; 
v___x_140_ = ((size_t)0ULL);
v___x_141_ = lean_usize_of_nat(v___x_138_);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_135_, v___x_140_, v___x_141_, v_a_115_);
return v___x_142_;
}
}
}
else
{
return v___x_136_;
}
}
case 5:
{
lean_object* v_args_143_; lean_object* v___x_144_; lean_object* v___x_145_; uint8_t v___x_146_; 
v_args_143_ = lean_ctor_get(v_e_114_, 1);
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = lean_array_get_size(v_args_143_);
v___x_146_ = lean_nat_dec_lt(v___x_144_, v___x_145_);
if (v___x_146_ == 0)
{
return v___x_146_;
}
else
{
if (v___x_146_ == 0)
{
return v___x_146_;
}
else
{
size_t v___x_147_; size_t v___x_148_; uint8_t v___x_149_; 
v___x_147_ = ((size_t)0ULL);
v___x_148_ = lean_usize_of_nat(v___x_145_);
v___x_149_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_143_, v___x_147_, v___x_148_, v_a_115_);
return v___x_149_;
}
}
}
case 6:
{
lean_object* v_var_150_; uint8_t v___x_151_; 
v_var_150_ = lean_ctor_get(v_e_114_, 1);
v___x_151_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_150_, v_a_115_);
return v___x_151_;
}
case 7:
{
lean_object* v_var_152_; uint8_t v___x_153_; 
v_var_152_ = lean_ctor_get(v_e_114_, 1);
v___x_153_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_152_, v_a_115_);
return v___x_153_;
}
case 8:
{
lean_object* v_var_154_; uint8_t v___x_155_; 
v_var_154_ = lean_ctor_get(v_e_114_, 2);
v___x_155_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_154_, v_a_115_);
return v___x_155_;
}
case 9:
{
lean_object* v_args_156_; 
v_args_156_ = lean_ctor_get(v_e_114_, 1);
v_args_117_ = v_args_156_;
v___y_118_ = v_a_115_;
goto v___jp_116_;
}
case 10:
{
lean_object* v_args_157_; 
v_args_157_ = lean_ctor_get(v_e_114_, 1);
v_args_117_ = v_args_157_;
v___y_118_ = v_a_115_;
goto v___jp_116_;
}
case 11:
{
lean_object* v_var_158_; uint8_t v___x_159_; 
v_var_158_ = lean_ctor_get(v_e_114_, 1);
v___x_159_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_158_, v_a_115_);
return v___x_159_;
}
case 12:
{
lean_object* v_var_160_; lean_object* v_args_161_; uint8_t v___x_162_; 
v_var_160_ = lean_ctor_get(v_e_114_, 0);
v_args_161_ = lean_ctor_get(v_e_114_, 2);
v___x_162_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_160_, v_a_115_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = lean_array_get_size(v_args_161_);
v___x_165_ = lean_nat_dec_lt(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
return v___x_162_;
}
else
{
if (v___x_165_ == 0)
{
return v___x_162_;
}
else
{
size_t v___x_166_; size_t v___x_167_; uint8_t v___x_168_; 
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_164_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_161_, v___x_166_, v___x_167_, v_a_115_);
return v___x_168_;
}
}
}
else
{
return v___x_162_;
}
}
case 13:
{
lean_object* v_fvarId_169_; uint8_t v___x_170_; 
v_fvarId_169_ = lean_ctor_get(v_e_114_, 1);
v___x_170_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_169_, v_a_115_);
return v___x_170_;
}
case 14:
{
lean_object* v_fvarId_171_; uint8_t v___x_172_; 
v_fvarId_171_ = lean_ctor_get(v_e_114_, 0);
v___x_172_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_171_, v_a_115_);
return v___x_172_;
}
case 15:
{
lean_object* v_fvarId_173_; uint8_t v___x_174_; 
v_fvarId_173_ = lean_ctor_get(v_e_114_, 0);
v___x_174_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_173_, v_a_115_);
return v___x_174_;
}
default: 
{
uint8_t v___x_175_; 
v___x_175_ = 0;
return v___x_175_;
}
}
v___jp_116_:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_array_get_size(v_args_117_);
v___x_121_ = lean_nat_dec_lt(v___x_119_, v___x_120_);
if (v___x_121_ == 0)
{
return v___x_121_;
}
else
{
if (v___x_121_ == 0)
{
return v___x_121_;
}
else
{
size_t v___x_122_; size_t v___x_123_; uint8_t v___x_124_; 
v___x_122_ = ((size_t)0ULL);
v___x_123_ = lean_usize_of_nat(v___x_120_);
v___x_124_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_117_, v___x_122_, v___x_123_, v___y_118_);
return v___x_124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn___boxed(lean_object* v_pu_176_, lean_object* v_e_177_, lean_object* v_a_178_){
_start:
{
uint8_t v_pu_boxed_179_; uint8_t v_res_180_; lean_object* v_r_181_; 
v_pu_boxed_179_ = lean_unbox(v_pu_176_);
v_res_180_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_boxed_179_, v_e_177_, v_a_178_);
lean_dec(v_a_178_);
lean_dec(v_e_177_);
v_r_181_ = lean_box(v_res_180_);
return v_r_181_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(uint8_t v_pu_182_, lean_object* v_as_183_, size_t v_i_184_, size_t v_stop_185_, lean_object* v___y_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_as_183_, v_i_184_, v_stop_185_, v___y_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___boxed(lean_object* v_pu_188_, lean_object* v_as_189_, lean_object* v_i_190_, lean_object* v_stop_191_, lean_object* v___y_192_){
_start:
{
uint8_t v_pu_boxed_193_; size_t v_i_boxed_194_; size_t v_stop_boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_pu_boxed_193_ = lean_unbox(v_pu_188_);
v_i_boxed_194_ = lean_unbox_usize(v_i_190_);
lean_dec(v_i_190_);
v_stop_boxed_195_ = lean_unbox_usize(v_stop_191_);
lean_dec(v_stop_191_);
v_res_196_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(v_pu_boxed_193_, v_as_189_, v_i_boxed_194_, v_stop_boxed_195_, v___y_192_);
lean_dec(v___y_192_);
lean_dec_ref(v_as_189_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(uint8_t v_pu_198_, lean_object* v_decl_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_type_201_; lean_object* v_value_202_; uint8_t v___x_203_; 
v_type_201_ = lean_ctor_get(v_decl_199_, 2);
v_value_202_ = lean_ctor_get(v_decl_199_, 3);
v___x_203_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_200_, v_type_201_);
if (v___x_203_ == 0)
{
uint8_t v___x_204_; 
v___x_204_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_198_, v_value_202_, v_a_200_);
return v___x_204_;
}
else
{
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn___boxed(lean_object* v_pu_205_, lean_object* v_decl_206_, lean_object* v_a_207_){
_start:
{
uint8_t v_pu_boxed_208_; uint8_t v_res_209_; lean_object* v_r_210_; 
v_pu_boxed_208_ = lean_unbox(v_pu_205_);
v_res_209_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_boxed_208_, v_decl_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_decl_206_);
v_r_210_ = lean_box(v_res_209_);
return v_r_210_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(uint8_t v_pu_211_, lean_object* v_c_212_, lean_object* v_a_213_){
_start:
{
switch(lean_obj_tag(v_c_212_))
{
case 0:
{
lean_object* v_decl_214_; lean_object* v_k_215_; uint8_t v___x_216_; 
v_decl_214_ = lean_ctor_get(v_c_212_, 0);
v_k_215_ = lean_ctor_get(v_c_212_, 1);
v___x_216_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_211_, v_decl_214_, v_a_213_);
if (v___x_216_ == 0)
{
v_c_212_ = v_k_215_;
goto _start;
}
else
{
return v___x_216_;
}
}
case 3:
{
lean_object* v_fvarId_218_; lean_object* v_args_219_; uint8_t v___x_220_; 
v_fvarId_218_ = lean_ctor_get(v_c_212_, 0);
v_args_219_ = lean_ctor_get(v_c_212_, 1);
v___x_220_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_218_, v_a_213_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_array_get_size(v_args_219_);
v___x_223_ = lean_nat_dec_lt(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
return v___x_220_;
}
else
{
if (v___x_223_ == 0)
{
return v___x_220_;
}
else
{
size_t v___x_224_; size_t v___x_225_; uint8_t v___x_226_; 
v___x_224_ = ((size_t)0ULL);
v___x_225_ = lean_usize_of_nat(v___x_222_);
v___x_226_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_219_, v___x_224_, v___x_225_, v_a_213_);
return v___x_226_;
}
}
}
else
{
return v___x_220_;
}
}
case 4:
{
lean_object* v_cases_227_; lean_object* v_resultType_228_; lean_object* v_discr_229_; lean_object* v_alts_230_; uint8_t v___x_231_; 
v_cases_227_ = lean_ctor_get(v_c_212_, 0);
v_resultType_228_ = lean_ctor_get(v_cases_227_, 1);
v_discr_229_ = lean_ctor_get(v_cases_227_, 2);
v_alts_230_ = lean_ctor_get(v_cases_227_, 3);
v___x_231_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_213_, v_resultType_228_);
if (v___x_231_ == 0)
{
uint8_t v___x_232_; 
v___x_232_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_discr_229_, v_a_213_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(0u);
v___x_234_ = lean_array_get_size(v_alts_230_);
v___x_235_ = lean_nat_dec_lt(v___x_233_, v___x_234_);
if (v___x_235_ == 0)
{
return v___x_232_;
}
else
{
if (v___x_235_ == 0)
{
return v___x_232_;
}
else
{
size_t v___x_236_; size_t v___x_237_; uint8_t v___x_238_; 
v___x_236_ = ((size_t)0ULL);
v___x_237_ = lean_usize_of_nat(v___x_234_);
v___x_238_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(v_pu_211_, v_alts_230_, v___x_236_, v___x_237_, v_a_213_);
return v___x_238_;
}
}
}
else
{
return v___x_232_;
}
}
else
{
return v___x_231_;
}
}
case 5:
{
lean_object* v_fvarId_239_; uint8_t v___x_240_; 
v_fvarId_239_ = lean_ctor_get(v_c_212_, 0);
v___x_240_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_239_, v_a_213_);
return v___x_240_;
}
case 6:
{
uint8_t v___x_241_; 
v___x_241_ = 0;
return v___x_241_;
}
case 7:
{
lean_object* v_fvarId_242_; lean_object* v_y_243_; lean_object* v_k_244_; uint8_t v___x_245_; 
v_fvarId_242_ = lean_ctor_get(v_c_212_, 0);
v_y_243_ = lean_ctor_get(v_c_212_, 2);
v_k_244_ = lean_ctor_get(v_c_212_, 3);
v___x_245_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_242_, v_a_213_);
if (v___x_245_ == 0)
{
uint8_t v___x_246_; 
v___x_246_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_y_243_, v_a_213_);
if (v___x_246_ == 0)
{
v_c_212_ = v_k_244_;
goto _start;
}
else
{
return v___x_246_;
}
}
else
{
return v___x_245_;
}
}
case 8:
{
lean_object* v_fvarId_248_; lean_object* v_y_249_; lean_object* v_k_250_; uint8_t v___x_251_; 
v_fvarId_248_ = lean_ctor_get(v_c_212_, 0);
v_y_249_ = lean_ctor_get(v_c_212_, 2);
v_k_250_ = lean_ctor_get(v_c_212_, 3);
v___x_251_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_248_, v_a_213_);
if (v___x_251_ == 0)
{
uint8_t v___x_252_; 
v___x_252_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_249_, v_a_213_);
if (v___x_252_ == 0)
{
v_c_212_ = v_k_250_;
goto _start;
}
else
{
return v___x_252_;
}
}
else
{
return v___x_251_;
}
}
case 9:
{
lean_object* v_fvarId_254_; lean_object* v_y_255_; lean_object* v_k_256_; uint8_t v___x_257_; 
v_fvarId_254_ = lean_ctor_get(v_c_212_, 0);
v_y_255_ = lean_ctor_get(v_c_212_, 3);
v_k_256_ = lean_ctor_get(v_c_212_, 5);
v___x_257_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_254_, v_a_213_);
if (v___x_257_ == 0)
{
uint8_t v___x_258_; 
v___x_258_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_255_, v_a_213_);
if (v___x_258_ == 0)
{
v_c_212_ = v_k_256_;
goto _start;
}
else
{
return v___x_258_;
}
}
else
{
return v___x_257_;
}
}
case 10:
{
lean_object* v_fvarId_260_; lean_object* v_k_261_; uint8_t v___x_262_; 
v_fvarId_260_ = lean_ctor_get(v_c_212_, 0);
v_k_261_ = lean_ctor_get(v_c_212_, 2);
v___x_262_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_260_, v_a_213_);
if (v___x_262_ == 0)
{
v_c_212_ = v_k_261_;
goto _start;
}
else
{
return v___x_262_;
}
}
case 11:
{
lean_object* v_fvarId_264_; lean_object* v_k_265_; uint8_t v___x_266_; 
v_fvarId_264_ = lean_ctor_get(v_c_212_, 0);
v_k_265_ = lean_ctor_get(v_c_212_, 2);
v___x_266_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_264_, v_a_213_);
if (v___x_266_ == 0)
{
v_c_212_ = v_k_265_;
goto _start;
}
else
{
return v___x_266_;
}
}
case 12:
{
lean_object* v_fvarId_268_; lean_object* v_k_269_; uint8_t v___x_270_; 
v_fvarId_268_ = lean_ctor_get(v_c_212_, 0);
v_k_269_ = lean_ctor_get(v_c_212_, 3);
v___x_270_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_268_, v_a_213_);
if (v___x_270_ == 0)
{
v_c_212_ = v_k_269_;
goto _start;
}
else
{
return v___x_270_;
}
}
case 13:
{
lean_object* v_fvarId_272_; lean_object* v_k_273_; uint8_t v___x_274_; 
v_fvarId_272_ = lean_ctor_get(v_c_212_, 0);
v_k_273_ = lean_ctor_get(v_c_212_, 1);
v___x_274_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_272_, v_a_213_);
if (v___x_274_ == 0)
{
v_c_212_ = v_k_273_;
goto _start;
}
else
{
return v___x_274_;
}
}
default: 
{
lean_object* v_decl_276_; lean_object* v_k_277_; lean_object* v_type_278_; lean_object* v_value_279_; uint8_t v___x_280_; 
v_decl_276_ = lean_ctor_get(v_c_212_, 0);
v_k_277_ = lean_ctor_get(v_c_212_, 1);
v_type_278_ = lean_ctor_get(v_decl_276_, 3);
v_value_279_ = lean_ctor_get(v_decl_276_, 4);
v___x_280_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_213_, v_type_278_);
if (v___x_280_ == 0)
{
uint8_t v___x_281_; 
v___x_281_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_211_, v_value_279_, v_a_213_);
if (v___x_281_ == 0)
{
v_c_212_ = v_k_277_;
goto _start;
}
else
{
return v___x_281_;
}
}
else
{
return v___x_280_;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(uint8_t v_pu_283_, lean_object* v_as_284_, size_t v_i_285_, size_t v_stop_286_, lean_object* v___y_287_){
_start:
{
uint8_t v___x_288_; 
v___x_288_ = lean_usize_dec_eq(v_i_285_, v_stop_286_);
if (v___x_288_ == 0)
{
uint8_t v___x_289_; lean_object* v___y_291_; lean_object* v___x_296_; 
v___x_289_ = 1;
v___x_296_ = lean_array_uget_borrowed(v_as_284_, v_i_285_);
switch(lean_obj_tag(v___x_296_))
{
case 0:
{
lean_object* v_code_297_; 
v_code_297_ = lean_ctor_get(v___x_296_, 2);
v___y_291_ = v_code_297_;
goto v___jp_290_;
}
case 1:
{
lean_object* v_code_298_; 
v_code_298_ = lean_ctor_get(v___x_296_, 1);
v___y_291_ = v_code_298_;
goto v___jp_290_;
}
default: 
{
lean_object* v_code_299_; 
v_code_299_ = lean_ctor_get(v___x_296_, 0);
v___y_291_ = v_code_299_;
goto v___jp_290_;
}
}
v___jp_290_:
{
uint8_t v___x_292_; 
v___x_292_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_283_, v___y_291_, v___y_287_);
if (v___x_292_ == 0)
{
size_t v___x_293_; size_t v___x_294_; 
v___x_293_ = ((size_t)1ULL);
v___x_294_ = lean_usize_add(v_i_285_, v___x_293_);
v_i_285_ = v___x_294_;
goto _start;
}
else
{
return v___x_289_;
}
}
}
else
{
uint8_t v___x_300_; 
v___x_300_ = 0;
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0___boxed(lean_object* v_pu_301_, lean_object* v_as_302_, lean_object* v_i_303_, lean_object* v_stop_304_, lean_object* v___y_305_){
_start:
{
uint8_t v_pu_boxed_306_; size_t v_i_boxed_307_; size_t v_stop_boxed_308_; uint8_t v_res_309_; lean_object* v_r_310_; 
v_pu_boxed_306_ = lean_unbox(v_pu_301_);
v_i_boxed_307_ = lean_unbox_usize(v_i_303_);
lean_dec(v_i_303_);
v_stop_boxed_308_ = lean_unbox_usize(v_stop_304_);
lean_dec(v_stop_304_);
v_res_309_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(v_pu_boxed_306_, v_as_302_, v_i_boxed_307_, v_stop_boxed_308_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v_as_302_);
v_r_310_ = lean_box(v_res_309_);
return v_r_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn___boxed(lean_object* v_pu_311_, lean_object* v_c_312_, lean_object* v_a_313_){
_start:
{
uint8_t v_pu_boxed_314_; uint8_t v_res_315_; lean_object* v_r_316_; 
v_pu_boxed_314_ = lean_unbox(v_pu_311_);
v_res_315_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_boxed_314_, v_c_312_, v_a_313_);
lean_dec(v_a_313_);
lean_dec_ref(v_c_312_);
v_r_316_ = lean_box(v_res_315_);
return v_r_316_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(lean_object* v_arg_317_, lean_object* v_s_318_){
_start:
{
uint8_t v___x_319_; 
v___x_319_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_arg_317_, v_s_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_dependsOn___redArg___boxed(lean_object* v_arg_320_, lean_object* v_s_321_){
_start:
{
uint8_t v_res_322_; lean_object* v_r_323_; 
v_res_322_ = l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(v_arg_320_, v_s_321_);
lean_dec(v_s_321_);
lean_dec(v_arg_320_);
v_r_323_ = lean_box(v_res_322_);
return v_r_323_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Arg_dependsOn(uint8_t v_pu_324_, lean_object* v_arg_325_, lean_object* v_s_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_arg_325_, v_s_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_dependsOn___boxed(lean_object* v_pu_328_, lean_object* v_arg_329_, lean_object* v_s_330_){
_start:
{
uint8_t v_pu_boxed_331_; uint8_t v_res_332_; lean_object* v_r_333_; 
v_pu_boxed_331_ = lean_unbox(v_pu_328_);
v_res_332_ = l_Lean_Compiler_LCNF_Arg_dependsOn(v_pu_boxed_331_, v_arg_329_, v_s_330_);
lean_dec(v_s_330_);
lean_dec(v_arg_329_);
v_r_333_ = lean_box(v_res_332_);
return v_r_333_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LetValue_dependsOn(uint8_t v_pu_334_, lean_object* v_value_335_, lean_object* v_s_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_334_, v_value_335_, v_s_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_dependsOn___boxed(lean_object* v_pu_338_, lean_object* v_value_339_, lean_object* v_s_340_){
_start:
{
uint8_t v_pu_boxed_341_; uint8_t v_res_342_; lean_object* v_r_343_; 
v_pu_boxed_341_ = lean_unbox(v_pu_338_);
v_res_342_ = l_Lean_Compiler_LCNF_LetValue_dependsOn(v_pu_boxed_341_, v_value_339_, v_s_340_);
lean_dec(v_s_340_);
lean_dec(v_value_339_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_LetDecl_dependsOn(uint8_t v_pu_344_, lean_object* v_decl_345_, lean_object* v_s_346_){
_start:
{
uint8_t v___x_347_; 
v___x_347_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_344_, v_decl_345_, v_s_346_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_dependsOn___boxed(lean_object* v_pu_348_, lean_object* v_decl_349_, lean_object* v_s_350_){
_start:
{
uint8_t v_pu_boxed_351_; uint8_t v_res_352_; lean_object* v_r_353_; 
v_pu_boxed_351_ = lean_unbox(v_pu_348_);
v_res_352_ = l_Lean_Compiler_LCNF_LetDecl_dependsOn(v_pu_boxed_351_, v_decl_349_, v_s_350_);
lean_dec(v_s_350_);
lean_dec_ref(v_decl_349_);
v_r_353_ = lean_box(v_res_352_);
return v_r_353_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_FunDecl_dependsOn(uint8_t v_pu_354_, lean_object* v_decl_355_, lean_object* v_s_356_){
_start:
{
lean_object* v_type_357_; lean_object* v_value_358_; uint8_t v___x_359_; 
v_type_357_ = lean_ctor_get(v_decl_355_, 3);
v_value_358_ = lean_ctor_get(v_decl_355_, 4);
v___x_359_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_356_, v_type_357_);
if (v___x_359_ == 0)
{
uint8_t v___x_360_; 
v___x_360_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_354_, v_value_358_, v_s_356_);
return v___x_360_;
}
else
{
return v___x_359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_dependsOn___boxed(lean_object* v_pu_361_, lean_object* v_decl_362_, lean_object* v_s_363_){
_start:
{
uint8_t v_pu_boxed_364_; uint8_t v_res_365_; lean_object* v_r_366_; 
v_pu_boxed_364_ = lean_unbox(v_pu_361_);
v_res_365_ = l_Lean_Compiler_LCNF_FunDecl_dependsOn(v_pu_boxed_364_, v_decl_362_, v_s_363_);
lean_dec(v_s_363_);
lean_dec_ref(v_decl_362_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t v_pu_367_, lean_object* v_decl_368_, lean_object* v_s_369_){
_start:
{
switch(lean_obj_tag(v_decl_368_))
{
case 0:
{
lean_object* v_decl_370_; uint8_t v___x_371_; 
v_decl_370_ = lean_ctor_get(v_decl_368_, 0);
v___x_371_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_367_, v_decl_370_, v_s_369_);
return v___x_371_;
}
case 1:
{
lean_object* v_decl_372_; lean_object* v_type_373_; lean_object* v_value_374_; uint8_t v___x_375_; 
v_decl_372_ = lean_ctor_get(v_decl_368_, 0);
v_type_373_ = lean_ctor_get(v_decl_372_, 3);
v_value_374_ = lean_ctor_get(v_decl_372_, 4);
v___x_375_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_369_, v_type_373_);
if (v___x_375_ == 0)
{
uint8_t v___x_376_; 
v___x_376_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_367_, v_value_374_, v_s_369_);
return v___x_376_;
}
else
{
return v___x_375_;
}
}
case 2:
{
lean_object* v_decl_377_; lean_object* v_type_378_; lean_object* v_value_379_; uint8_t v___x_380_; 
v_decl_377_ = lean_ctor_get(v_decl_368_, 0);
v_type_378_ = lean_ctor_get(v_decl_377_, 3);
v_value_379_ = lean_ctor_get(v_decl_377_, 4);
v___x_380_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_369_, v_type_378_);
if (v___x_380_ == 0)
{
uint8_t v___x_381_; 
v___x_381_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_367_, v_value_379_, v_s_369_);
return v___x_381_;
}
else
{
return v___x_380_;
}
}
case 3:
{
lean_object* v_fvarId_382_; lean_object* v_y_383_; uint8_t v___x_384_; 
v_fvarId_382_ = lean_ctor_get(v_decl_368_, 0);
v_y_383_ = lean_ctor_get(v_decl_368_, 2);
v___x_384_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_382_, v_s_369_);
if (v___x_384_ == 0)
{
uint8_t v___x_385_; 
v___x_385_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_y_383_, v_s_369_);
return v___x_385_;
}
else
{
return v___x_384_;
}
}
case 4:
{
lean_object* v_fvarId_386_; lean_object* v_y_387_; uint8_t v___x_388_; 
v_fvarId_386_ = lean_ctor_get(v_decl_368_, 0);
v_y_387_ = lean_ctor_get(v_decl_368_, 2);
v___x_388_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_386_, v_s_369_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; 
v___x_389_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_387_, v_s_369_);
return v___x_389_;
}
else
{
return v___x_388_;
}
}
case 5:
{
lean_object* v_fvarId_390_; lean_object* v_y_391_; uint8_t v___x_392_; 
v_fvarId_390_ = lean_ctor_get(v_decl_368_, 0);
v_y_391_ = lean_ctor_get(v_decl_368_, 3);
v___x_392_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_390_, v_s_369_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
v___x_393_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_391_, v_s_369_);
return v___x_393_;
}
else
{
return v___x_392_;
}
}
default: 
{
lean_object* v_fvarId_394_; uint8_t v___x_395_; 
v_fvarId_394_ = lean_ctor_get(v_decl_368_, 0);
v___x_395_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_394_, v_s_369_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_dependsOn___boxed(lean_object* v_pu_396_, lean_object* v_decl_397_, lean_object* v_s_398_){
_start:
{
uint8_t v_pu_boxed_399_; uint8_t v_res_400_; lean_object* v_r_401_; 
v_pu_boxed_399_ = lean_unbox(v_pu_396_);
v_res_400_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v_pu_boxed_399_, v_decl_397_, v_s_398_);
lean_dec(v_s_398_);
lean_dec_ref(v_decl_397_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Code_dependsOn(uint8_t v_pu_402_, lean_object* v_c_403_, lean_object* v_s_404_){
_start:
{
uint8_t v___x_405_; 
v___x_405_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_402_, v_c_403_, v_s_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_dependsOn___boxed(lean_object* v_pu_406_, lean_object* v_c_407_, lean_object* v_s_408_){
_start:
{
uint8_t v_pu_boxed_409_; uint8_t v_res_410_; lean_object* v_r_411_; 
v_pu_boxed_409_ = lean_unbox(v_pu_406_);
v_res_410_ = l_Lean_Compiler_LCNF_Code_dependsOn(v_pu_boxed_409_, v_c_407_, v_s_408_);
lean_dec(v_s_408_);
lean_dec_ref(v_c_407_);
v_r_411_ = lean_box(v_res_410_);
return v_r_411_;
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
