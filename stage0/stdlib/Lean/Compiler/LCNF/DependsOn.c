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
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(lean_object* v_k_1_, lean_object* v_t_2_){
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_1_ = stack[0].m_obj;
lean_object* v_t_2_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_k_1_, v_t_2_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg___boxed(lean_object* v_k_12_, lean_object* v_t_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_k_12_, v_t_13_);
lean_dec(v_t_13_);
lean_dec(v_k_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn(lean_object* v_fvarId_16_, lean_object* v_a_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_16_, v_a_17_);
return v___x_18_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_16_ = stack[0].m_obj;
lean_object* v_a_17_ = stack[1].m_obj;
uint8_t v_res_19_;
v_res_19_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn(v_fvarId_16_, v_a_17_);
stack->m_num = v_res_19_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn___boxed(lean_object* v_fvarId_20_, lean_object* v_a_21_){
_start:
{
uint8_t v_res_22_; lean_object* v_r_23_; 
v_res_22_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn(v_fvarId_20_, v_a_21_);
lean_dec(v_a_21_);
lean_dec(v_fvarId_20_);
v_r_23_ = lean_box(v_res_22_);
return v_r_23_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0(lean_object* v_00_u03b2_24_, lean_object* v_k_25_, lean_object* v_t_26_){
_start:
{
uint8_t v___x_27_; 
v___x_27_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_k_25_, v_t_26_);
return v___x_27_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_25_ = stack[1].m_obj;
lean_object* v_t_26_ = stack[2].m_obj;
uint8_t v_res_28_;
v_res_28_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0(lean_box(0), v_k_25_, v_t_26_);
stack->m_num = v_res_28_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___boxed(lean_object* v_00_u03b2_29_, lean_object* v_k_30_, lean_object* v_t_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0(v_00_u03b2_29_, v_k_30_, v_t_31_);
lean_dec(v_t_31_);
lean_dec(v_k_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
uint8_t l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(lean_object* v_a_34_, lean_object* v_e_35_){
_start:
{
uint8_t v___x_36_; lean_object* v_d_38_; lean_object* v_b_39_; 
v___x_36_ = l_Lean_Expr_hasFVar(v_e_35_);
if (v___x_36_ == 0)
{
return v___x_36_;
}
else
{
switch(lean_obj_tag(v_e_35_))
{
case 7:
{
lean_object* v_binderType_42_; lean_object* v_body_43_; 
v_binderType_42_ = lean_ctor_get(v_e_35_, 1);
v_body_43_ = lean_ctor_get(v_e_35_, 2);
v_d_38_ = v_binderType_42_;
v_b_39_ = v_body_43_;
goto v___jp_37_;
}
case 6:
{
lean_object* v_binderType_44_; lean_object* v_body_45_; 
v_binderType_44_ = lean_ctor_get(v_e_35_, 1);
v_body_45_ = lean_ctor_get(v_e_35_, 2);
v_d_38_ = v_binderType_44_;
v_b_39_ = v_body_45_;
goto v___jp_37_;
}
case 10:
{
lean_object* v_expr_46_; 
v_expr_46_ = lean_ctor_get(v_e_35_, 1);
v_e_35_ = v_expr_46_;
goto _start;
}
case 8:
{
lean_object* v_type_48_; lean_object* v_value_49_; lean_object* v_body_50_; uint8_t v___x_51_; 
v_type_48_ = lean_ctor_get(v_e_35_, 1);
v_value_49_ = lean_ctor_get(v_e_35_, 2);
v_body_50_ = lean_ctor_get(v_e_35_, 3);
v___x_51_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_34_, v_type_48_);
if (v___x_51_ == 0)
{
uint8_t v___x_52_; 
v___x_52_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_34_, v_value_49_);
if (v___x_52_ == 0)
{
v_e_35_ = v_body_50_;
goto _start;
}
else
{
return v___x_36_;
}
}
else
{
return v___x_36_;
}
}
case 5:
{
lean_object* v_fn_54_; lean_object* v_arg_55_; uint8_t v___x_56_; 
v_fn_54_ = lean_ctor_get(v_e_35_, 0);
v_arg_55_ = lean_ctor_get(v_e_35_, 1);
v___x_56_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_34_, v_fn_54_);
if (v___x_56_ == 0)
{
v_e_35_ = v_arg_55_;
goto _start;
}
else
{
return v___x_36_;
}
}
case 11:
{
lean_object* v_struct_58_; 
v_struct_58_ = lean_ctor_get(v_e_35_, 2);
v_e_35_ = v_struct_58_;
goto _start;
}
case 1:
{
lean_object* v_fvarId_60_; uint8_t v___x_61_; 
v_fvarId_60_ = lean_ctor_get(v_e_35_, 0);
v___x_61_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_60_, v_a_34_);
return v___x_61_;
}
default: 
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
}
v___jp_37_:
{
uint8_t v___x_40_; 
v___x_40_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_34_, v_d_38_);
if (v___x_40_ == 0)
{
v_e_35_ = v_b_39_;
goto _start;
}
else
{
return v___x_36_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_34_ = stack[0].m_obj;
lean_object* v_e_35_ = stack[1].m_obj;
uint8_t v_res_63_;
v_res_63_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_34_, v_e_35_);
stack->m_num = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0___boxed(lean_object* v_a_64_, lean_object* v_e_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_64_, v_e_65_);
lean_dec_ref(v_e_65_);
lean_dec(v_a_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(lean_object* v_e_68_, lean_object* v_a_69_){
_start:
{
uint8_t v___x_70_; 
v___x_70_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_69_, v_e_68_);
return v___x_70_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_68_ = stack[0].m_obj;
lean_object* v_a_69_ = stack[1].m_obj;
uint8_t v_res_71_;
v_res_71_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(v_e_68_, v_a_69_);
stack->m_num = v_res_71_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn___boxed(lean_object* v_e_72_, lean_object* v_a_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn(v_e_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_e_72_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
switch(lean_obj_tag(v_a_76_))
{
case 0:
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
case 1:
{
lean_object* v_fvarId_79_; uint8_t v___x_80_; 
v_fvarId_79_ = lean_ctor_get(v_a_76_, 0);
v___x_80_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_79_, v_a_77_);
return v___x_80_;
}
default: 
{
lean_object* v_expr_81_; uint8_t v___x_82_; 
v_expr_81_ = lean_ctor_get(v_a_76_, 0);
v___x_82_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_77_, v_expr_81_);
return v___x_82_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_76_ = stack[0].m_obj;
lean_object* v_a_77_ = stack[1].m_obj;
uint8_t v_res_83_;
v_res_83_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_a_76_, v_a_77_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg___boxed(lean_object* v_a_84_, lean_object* v_a_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_a_84_, v_a_85_);
lean_dec(v_a_85_);
lean_dec(v_a_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(uint8_t v_pu_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_a_89_, v_a_90_);
return v___x_91_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_88_ = stack[0].m_num;
lean_object* v_a_89_ = stack[1].m_obj;
lean_object* v_a_90_ = stack[2].m_obj;
uint8_t v_res_92_;
v_res_92_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v_pu_88_, v_a_89_, v_a_90_);
stack->m_num = v_res_92_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___boxed(lean_object* v_pu_93_, lean_object* v_a_94_, lean_object* v_a_95_){
_start:
{
uint8_t v_pu_boxed_96_; uint8_t v_res_97_; lean_object* v_r_98_; 
v_pu_boxed_96_ = lean_unbox(v_pu_93_);
v_res_97_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn(v_pu_boxed_96_, v_a_94_, v_a_95_);
lean_dec(v_a_95_);
lean_dec(v_a_94_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(lean_object* v_as_99_, size_t v_i_100_, size_t v_stop_101_, lean_object* v___y_102_){
_start:
{
uint8_t v___x_103_; 
v___x_103_ = lean_usize_dec_eq(v_i_100_, v_stop_101_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_104_ = lean_array_uget_borrowed(v_as_99_, v_i_100_);
v___x_105_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v___x_104_, v___y_102_);
if (v___x_105_ == 0)
{
size_t v___x_106_; size_t v___x_107_; 
v___x_106_ = ((size_t)1ULL);
v___x_107_ = lean_usize_add(v_i_100_, v___x_106_);
v_i_100_ = v___x_107_;
goto _start;
}
else
{
return v___x_105_;
}
}
else
{
uint8_t v___x_109_; 
v___x_109_ = 0;
return v___x_109_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_99_ = stack[0].m_obj;
size_t v_i_100_ = stack[1].m_num;
size_t v_stop_101_ = stack[2].m_num;
lean_object* v___y_102_ = stack[3].m_obj;
uint8_t v_res_110_;
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_as_99_, v_i_100_, v_stop_101_, v___y_102_);
stack->m_num = v_res_110_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg___boxed(lean_object* v_as_111_, lean_object* v_i_112_, lean_object* v_stop_113_, lean_object* v___y_114_){
_start:
{
size_t v_i_boxed_115_; size_t v_stop_boxed_116_; uint8_t v_res_117_; lean_object* v_r_118_; 
v_i_boxed_115_ = lean_unbox_usize(v_i_112_);
lean_dec(v_i_112_);
v_stop_boxed_116_ = lean_unbox_usize(v_stop_113_);
lean_dec(v_stop_113_);
v_res_117_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_as_111_, v_i_boxed_115_, v_stop_boxed_116_, v___y_114_);
lean_dec(v___y_114_);
lean_dec_ref(v_as_111_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(uint8_t v_pu_119_, lean_object* v_e_120_, lean_object* v_a_121_){
_start:
{
lean_object* v_args_123_; lean_object* v___y_124_; 
switch(lean_obj_tag(v_e_120_))
{
case 2:
{
lean_object* v_struct_131_; uint8_t v___x_132_; 
v_struct_131_ = lean_ctor_get(v_e_120_, 2);
v___x_132_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_struct_131_, v_a_121_);
return v___x_132_;
}
case 3:
{
lean_object* v_args_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v_args_133_ = lean_ctor_get(v_e_120_, 2);
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = lean_array_get_size(v_args_133_);
v___x_136_ = lean_nat_dec_lt(v___x_134_, v___x_135_);
if (v___x_136_ == 0)
{
return v___x_136_;
}
else
{
if (v___x_136_ == 0)
{
return v___x_136_;
}
else
{
size_t v___x_137_; size_t v___x_138_; uint8_t v___x_139_; 
v___x_137_ = ((size_t)0ULL);
v___x_138_ = lean_usize_of_nat(v___x_135_);
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_133_, v___x_137_, v___x_138_, v_a_121_);
return v___x_139_;
}
}
}
case 4:
{
lean_object* v_fvarId_140_; lean_object* v_args_141_; uint8_t v___x_142_; 
v_fvarId_140_ = lean_ctor_get(v_e_120_, 0);
v_args_141_ = lean_ctor_get(v_e_120_, 1);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_140_, v_a_121_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_143_ = lean_unsigned_to_nat(0u);
v___x_144_ = lean_array_get_size(v_args_141_);
v___x_145_ = lean_nat_dec_lt(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
return v___x_145_;
}
else
{
if (v___x_145_ == 0)
{
return v___x_145_;
}
else
{
size_t v___x_146_; size_t v___x_147_; uint8_t v___x_148_; 
v___x_146_ = ((size_t)0ULL);
v___x_147_ = lean_usize_of_nat(v___x_144_);
v___x_148_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_141_, v___x_146_, v___x_147_, v_a_121_);
return v___x_148_;
}
}
}
else
{
return v___x_142_;
}
}
case 5:
{
lean_object* v_args_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v_args_149_ = lean_ctor_get(v_e_120_, 1);
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = lean_array_get_size(v_args_149_);
v___x_152_ = lean_nat_dec_lt(v___x_150_, v___x_151_);
if (v___x_152_ == 0)
{
return v___x_152_;
}
else
{
if (v___x_152_ == 0)
{
return v___x_152_;
}
else
{
size_t v___x_153_; size_t v___x_154_; uint8_t v___x_155_; 
v___x_153_ = ((size_t)0ULL);
v___x_154_ = lean_usize_of_nat(v___x_151_);
v___x_155_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_149_, v___x_153_, v___x_154_, v_a_121_);
return v___x_155_;
}
}
}
case 6:
{
lean_object* v_var_156_; uint8_t v___x_157_; 
v_var_156_ = lean_ctor_get(v_e_120_, 1);
v___x_157_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_156_, v_a_121_);
return v___x_157_;
}
case 7:
{
lean_object* v_var_158_; uint8_t v___x_159_; 
v_var_158_ = lean_ctor_get(v_e_120_, 1);
v___x_159_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_158_, v_a_121_);
return v___x_159_;
}
case 8:
{
lean_object* v_var_160_; uint8_t v___x_161_; 
v_var_160_ = lean_ctor_get(v_e_120_, 2);
v___x_161_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_160_, v_a_121_);
return v___x_161_;
}
case 9:
{
lean_object* v_args_162_; 
v_args_162_ = lean_ctor_get(v_e_120_, 1);
v_args_123_ = v_args_162_;
v___y_124_ = v_a_121_;
goto v___jp_122_;
}
case 10:
{
lean_object* v_args_163_; 
v_args_163_ = lean_ctor_get(v_e_120_, 1);
v_args_123_ = v_args_163_;
v___y_124_ = v_a_121_;
goto v___jp_122_;
}
case 11:
{
lean_object* v_var_164_; uint8_t v___x_165_; 
v_var_164_ = lean_ctor_get(v_e_120_, 1);
v___x_165_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_164_, v_a_121_);
return v___x_165_;
}
case 12:
{
lean_object* v_var_166_; lean_object* v_args_167_; uint8_t v___x_168_; 
v_var_166_ = lean_ctor_get(v_e_120_, 0);
v_args_167_ = lean_ctor_get(v_e_120_, 2);
v___x_168_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_var_166_, v_a_121_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_array_get_size(v_args_167_);
v___x_171_ = lean_nat_dec_lt(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
if (v___x_171_ == 0)
{
return v___x_171_;
}
else
{
size_t v___x_172_; size_t v___x_173_; uint8_t v___x_174_; 
v___x_172_ = ((size_t)0ULL);
v___x_173_ = lean_usize_of_nat(v___x_170_);
v___x_174_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_167_, v___x_172_, v___x_173_, v_a_121_);
return v___x_174_;
}
}
}
else
{
return v___x_168_;
}
}
case 13:
{
lean_object* v_fvarId_175_; uint8_t v___x_176_; 
v_fvarId_175_ = lean_ctor_get(v_e_120_, 1);
v___x_176_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_175_, v_a_121_);
return v___x_176_;
}
case 14:
{
lean_object* v_fvarId_177_; uint8_t v___x_178_; 
v_fvarId_177_ = lean_ctor_get(v_e_120_, 0);
v___x_178_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_177_, v_a_121_);
return v___x_178_;
}
case 15:
{
lean_object* v_fvarId_179_; uint8_t v___x_180_; 
v_fvarId_179_ = lean_ctor_get(v_e_120_, 0);
v___x_180_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_179_, v_a_121_);
return v___x_180_;
}
default: 
{
uint8_t v___x_181_; 
v___x_181_ = 0;
return v___x_181_;
}
}
v___jp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_array_get_size(v_args_123_);
v___x_127_ = lean_nat_dec_lt(v___x_125_, v___x_126_);
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
if (v___x_127_ == 0)
{
return v___x_127_;
}
else
{
size_t v___x_128_; size_t v___x_129_; uint8_t v___x_130_; 
v___x_128_ = ((size_t)0ULL);
v___x_129_ = lean_usize_of_nat(v___x_126_);
v___x_130_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_123_, v___x_128_, v___x_129_, v___y_124_);
return v___x_130_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_119_ = stack[0].m_num;
lean_object* v_e_120_ = stack[1].m_obj;
lean_object* v_a_121_ = stack[2].m_obj;
uint8_t v_res_182_;
v_res_182_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_119_, v_e_120_, v_a_121_);
stack->m_num = v_res_182_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn___boxed(lean_object* v_pu_183_, lean_object* v_e_184_, lean_object* v_a_185_){
_start:
{
uint8_t v_pu_boxed_186_; uint8_t v_res_187_; lean_object* v_r_188_; 
v_pu_boxed_186_ = lean_unbox(v_pu_183_);
v_res_187_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_boxed_186_, v_e_184_, v_a_185_);
lean_dec(v_a_185_);
lean_dec(v_e_184_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(uint8_t v_pu_189_, lean_object* v_as_190_, size_t v_i_191_, size_t v_stop_192_, lean_object* v___y_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_as_190_, v_i_191_, v_stop_192_, v___y_193_);
return v___x_194_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_189_ = stack[0].m_num;
lean_object* v_as_190_ = stack[1].m_obj;
size_t v_i_191_ = stack[2].m_num;
size_t v_stop_192_ = stack[3].m_num;
lean_object* v___y_193_ = stack[4].m_obj;
uint8_t v_res_195_;
v_res_195_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(v_pu_189_, v_as_190_, v_i_191_, v_stop_192_, v___y_193_);
stack->m_num = v_res_195_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___boxed(lean_object* v_pu_196_, lean_object* v_as_197_, lean_object* v_i_198_, lean_object* v_stop_199_, lean_object* v___y_200_){
_start:
{
uint8_t v_pu_boxed_201_; size_t v_i_boxed_202_; size_t v_stop_boxed_203_; uint8_t v_res_204_; lean_object* v_r_205_; 
v_pu_boxed_201_ = lean_unbox(v_pu_196_);
v_i_boxed_202_ = lean_unbox_usize(v_i_198_);
lean_dec(v_i_198_);
v_stop_boxed_203_ = lean_unbox_usize(v_stop_199_);
lean_dec(v_stop_199_);
v_res_204_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0(v_pu_boxed_201_, v_as_197_, v_i_boxed_202_, v_stop_boxed_203_, v___y_200_);
lean_dec(v___y_200_);
lean_dec_ref(v_as_197_);
v_r_205_ = lean_box(v_res_204_);
return v_r_205_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(uint8_t v_pu_206_, lean_object* v_decl_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_type_209_; lean_object* v_value_210_; uint8_t v___x_211_; 
v_type_209_ = lean_ctor_get(v_decl_207_, 2);
v_value_210_ = lean_ctor_get(v_decl_207_, 3);
v___x_211_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_208_, v_type_209_);
if (v___x_211_ == 0)
{
uint8_t v___x_212_; 
v___x_212_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_206_, v_value_210_, v_a_208_);
return v___x_212_;
}
else
{
return v___x_211_;
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_206_ = stack[0].m_num;
lean_object* v_decl_207_ = stack[1].m_obj;
lean_object* v_a_208_ = stack[2].m_obj;
uint8_t v_res_213_;
v_res_213_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_206_, v_decl_207_, v_a_208_);
stack->m_num = v_res_213_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn___boxed(lean_object* v_pu_214_, lean_object* v_decl_215_, lean_object* v_a_216_){
_start:
{
uint8_t v_pu_boxed_217_; uint8_t v_res_218_; lean_object* v_r_219_; 
v_pu_boxed_217_ = lean_unbox(v_pu_214_);
v_res_218_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_boxed_217_, v_decl_215_, v_a_216_);
lean_dec(v_a_216_);
lean_dec_ref(v_decl_215_);
v_r_219_ = lean_box(v_res_218_);
return v_r_219_;
}
}
uint8_t l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(uint8_t v_pu_220_, lean_object* v_c_221_, lean_object* v_a_222_){
_start:
{
switch(lean_obj_tag(v_c_221_))
{
case 0:
{
lean_object* v_decl_223_; lean_object* v_k_224_; uint8_t v___x_225_; 
v_decl_223_ = lean_ctor_get(v_c_221_, 0);
v_k_224_ = lean_ctor_get(v_c_221_, 1);
v___x_225_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_220_, v_decl_223_, v_a_222_);
if (v___x_225_ == 0)
{
v_c_221_ = v_k_224_;
goto _start;
}
else
{
return v___x_225_;
}
}
case 3:
{
lean_object* v_fvarId_227_; lean_object* v_args_228_; uint8_t v___x_229_; 
v_fvarId_227_ = lean_ctor_get(v_c_221_, 0);
v_args_228_ = lean_ctor_get(v_c_221_, 1);
v___x_229_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_227_, v_a_222_);
if (v___x_229_ == 0)
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lean_unsigned_to_nat(0u);
v___x_231_ = lean_array_get_size(v_args_228_);
v___x_232_ = lean_nat_dec_lt(v___x_230_, v___x_231_);
if (v___x_232_ == 0)
{
return v___x_232_;
}
else
{
if (v___x_232_ == 0)
{
return v___x_232_;
}
else
{
size_t v___x_233_; size_t v___x_234_; uint8_t v___x_235_; 
v___x_233_ = ((size_t)0ULL);
v___x_234_ = lean_usize_of_nat(v___x_231_);
v___x_235_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn_spec__0___redArg(v_args_228_, v___x_233_, v___x_234_, v_a_222_);
return v___x_235_;
}
}
}
else
{
return v___x_229_;
}
}
case 4:
{
lean_object* v_cases_236_; lean_object* v_resultType_237_; lean_object* v_discr_238_; lean_object* v_alts_239_; uint8_t v___x_240_; 
v_cases_236_ = lean_ctor_get(v_c_221_, 0);
v_resultType_237_ = lean_ctor_get(v_cases_236_, 1);
v_discr_238_ = lean_ctor_get(v_cases_236_, 2);
v_alts_239_ = lean_ctor_get(v_cases_236_, 3);
v___x_240_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_222_, v_resultType_237_);
if (v___x_240_ == 0)
{
uint8_t v___x_241_; 
v___x_241_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_discr_238_, v_a_222_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_array_get_size(v_alts_239_);
v___x_244_ = lean_nat_dec_lt(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
return v___x_244_;
}
else
{
if (v___x_244_ == 0)
{
return v___x_244_;
}
else
{
size_t v___x_245_; size_t v___x_246_; uint8_t v___x_247_; 
v___x_245_ = ((size_t)0ULL);
v___x_246_ = lean_usize_of_nat(v___x_243_);
v___x_247_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(v_pu_220_, v_alts_239_, v___x_245_, v___x_246_, v_a_222_);
return v___x_247_;
}
}
}
else
{
return v___x_241_;
}
}
else
{
return v___x_240_;
}
}
case 5:
{
lean_object* v_fvarId_248_; uint8_t v___x_249_; 
v_fvarId_248_ = lean_ctor_get(v_c_221_, 0);
v___x_249_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_248_, v_a_222_);
return v___x_249_;
}
case 6:
{
uint8_t v___x_250_; 
v___x_250_ = 0;
return v___x_250_;
}
case 7:
{
lean_object* v_fvarId_251_; lean_object* v_y_252_; lean_object* v_k_253_; uint8_t v___x_254_; 
v_fvarId_251_ = lean_ctor_get(v_c_221_, 0);
v_y_252_ = lean_ctor_get(v_c_221_, 2);
v_k_253_ = lean_ctor_get(v_c_221_, 3);
v___x_254_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_251_, v_a_222_);
if (v___x_254_ == 0)
{
uint8_t v___x_255_; 
v___x_255_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_y_252_, v_a_222_);
if (v___x_255_ == 0)
{
v_c_221_ = v_k_253_;
goto _start;
}
else
{
return v___x_255_;
}
}
else
{
return v___x_254_;
}
}
case 8:
{
lean_object* v_fvarId_257_; lean_object* v_y_258_; lean_object* v_k_259_; uint8_t v___x_260_; 
v_fvarId_257_ = lean_ctor_get(v_c_221_, 0);
v_y_258_ = lean_ctor_get(v_c_221_, 2);
v_k_259_ = lean_ctor_get(v_c_221_, 3);
v___x_260_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_257_, v_a_222_);
if (v___x_260_ == 0)
{
uint8_t v___x_261_; 
v___x_261_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_258_, v_a_222_);
if (v___x_261_ == 0)
{
v_c_221_ = v_k_259_;
goto _start;
}
else
{
return v___x_261_;
}
}
else
{
return v___x_260_;
}
}
case 9:
{
lean_object* v_fvarId_263_; lean_object* v_y_264_; lean_object* v_k_265_; uint8_t v___x_266_; 
v_fvarId_263_ = lean_ctor_get(v_c_221_, 0);
v_y_264_ = lean_ctor_get(v_c_221_, 3);
v_k_265_ = lean_ctor_get(v_c_221_, 5);
v___x_266_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_263_, v_a_222_);
if (v___x_266_ == 0)
{
uint8_t v___x_267_; 
v___x_267_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_264_, v_a_222_);
if (v___x_267_ == 0)
{
v_c_221_ = v_k_265_;
goto _start;
}
else
{
return v___x_267_;
}
}
else
{
return v___x_266_;
}
}
case 10:
{
lean_object* v_fvarId_269_; lean_object* v_k_270_; uint8_t v___x_271_; 
v_fvarId_269_ = lean_ctor_get(v_c_221_, 0);
v_k_270_ = lean_ctor_get(v_c_221_, 2);
v___x_271_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_269_, v_a_222_);
if (v___x_271_ == 0)
{
v_c_221_ = v_k_270_;
goto _start;
}
else
{
return v___x_271_;
}
}
case 11:
{
lean_object* v_fvarId_273_; lean_object* v_k_274_; uint8_t v___x_275_; 
v_fvarId_273_ = lean_ctor_get(v_c_221_, 0);
v_k_274_ = lean_ctor_get(v_c_221_, 2);
v___x_275_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_273_, v_a_222_);
if (v___x_275_ == 0)
{
v_c_221_ = v_k_274_;
goto _start;
}
else
{
return v___x_275_;
}
}
case 12:
{
lean_object* v_fvarId_277_; lean_object* v_k_278_; uint8_t v___x_279_; 
v_fvarId_277_ = lean_ctor_get(v_c_221_, 0);
v_k_278_ = lean_ctor_get(v_c_221_, 3);
v___x_279_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_277_, v_a_222_);
if (v___x_279_ == 0)
{
v_c_221_ = v_k_278_;
goto _start;
}
else
{
return v___x_279_;
}
}
case 13:
{
lean_object* v_fvarId_281_; lean_object* v_k_282_; uint8_t v___x_283_; 
v_fvarId_281_ = lean_ctor_get(v_c_221_, 0);
v_k_282_ = lean_ctor_get(v_c_221_, 1);
v___x_283_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_281_, v_a_222_);
if (v___x_283_ == 0)
{
v_c_221_ = v_k_282_;
goto _start;
}
else
{
return v___x_283_;
}
}
default: 
{
lean_object* v_decl_285_; lean_object* v_k_286_; lean_object* v_type_287_; lean_object* v_value_288_; uint8_t v___x_289_; 
v_decl_285_ = lean_ctor_get(v_c_221_, 0);
v_k_286_ = lean_ctor_get(v_c_221_, 1);
v_type_287_ = lean_ctor_get(v_decl_285_, 3);
v_value_288_ = lean_ctor_get(v_decl_285_, 4);
v___x_289_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_a_222_, v_type_287_);
if (v___x_289_ == 0)
{
uint8_t v___x_290_; 
v___x_290_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_220_, v_value_288_, v_a_222_);
if (v___x_290_ == 0)
{
v_c_221_ = v_k_286_;
goto _start;
}
else
{
return v___x_290_;
}
}
else
{
return v___x_289_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_220_ = stack[0].m_num;
lean_object* v_c_221_ = stack[1].m_obj;
lean_object* v_a_222_ = stack[2].m_obj;
uint8_t v_res_292_;
v_res_292_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_220_, v_c_221_, v_a_222_);
stack->m_num = v_res_292_;
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(uint8_t v_pu_293_, lean_object* v_as_294_, size_t v_i_295_, size_t v_stop_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___x_298_; 
v___x_298_ = lean_usize_dec_eq(v_i_295_, v_stop_296_);
if (v___x_298_ == 0)
{
uint8_t v___x_299_; lean_object* v___y_301_; lean_object* v___x_306_; 
v___x_299_ = 1;
v___x_306_ = lean_array_uget_borrowed(v_as_294_, v_i_295_);
switch(lean_obj_tag(v___x_306_))
{
case 0:
{
lean_object* v_code_307_; 
v_code_307_ = lean_ctor_get(v___x_306_, 2);
v___y_301_ = v_code_307_;
goto v___jp_300_;
}
case 1:
{
lean_object* v_code_308_; 
v_code_308_ = lean_ctor_get(v___x_306_, 1);
v___y_301_ = v_code_308_;
goto v___jp_300_;
}
default: 
{
lean_object* v_code_309_; 
v_code_309_ = lean_ctor_get(v___x_306_, 0);
v___y_301_ = v_code_309_;
goto v___jp_300_;
}
}
v___jp_300_:
{
uint8_t v___x_302_; 
v___x_302_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_293_, v___y_301_, v___y_297_);
if (v___x_302_ == 0)
{
size_t v___x_303_; size_t v___x_304_; 
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_add(v_i_295_, v___x_303_);
v_i_295_ = v___x_304_;
goto _start;
}
else
{
return v___x_299_;
}
}
}
else
{
uint8_t v___x_310_; 
v___x_310_ = 0;
return v___x_310_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_293_ = stack[0].m_num;
lean_object* v_as_294_ = stack[1].m_obj;
size_t v_i_295_ = stack[2].m_num;
size_t v_stop_296_ = stack[3].m_num;
lean_object* v___y_297_ = stack[4].m_obj;
uint8_t v_res_311_;
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(v_pu_293_, v_as_294_, v_i_295_, v_stop_296_, v___y_297_);
stack->m_num = v_res_311_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0___boxed(lean_object* v_pu_312_, lean_object* v_as_313_, lean_object* v_i_314_, lean_object* v_stop_315_, lean_object* v___y_316_){
_start:
{
uint8_t v_pu_boxed_317_; size_t v_i_boxed_318_; size_t v_stop_boxed_319_; uint8_t v_res_320_; lean_object* v_r_321_; 
v_pu_boxed_317_ = lean_unbox(v_pu_312_);
v_i_boxed_318_ = lean_unbox_usize(v_i_314_);
lean_dec(v_i_314_);
v_stop_boxed_319_ = lean_unbox_usize(v_stop_315_);
lean_dec(v_stop_315_);
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn_spec__0(v_pu_boxed_317_, v_as_313_, v_i_boxed_318_, v_stop_boxed_319_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v_as_313_);
v_r_321_ = lean_box(v_res_320_);
return v_r_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn___boxed(lean_object* v_pu_322_, lean_object* v_c_323_, lean_object* v_a_324_){
_start:
{
uint8_t v_pu_boxed_325_; uint8_t v_res_326_; lean_object* v_r_327_; 
v_pu_boxed_325_ = lean_unbox(v_pu_322_);
v_res_326_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_boxed_325_, v_c_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_c_323_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
uint8_t l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(lean_object* v_arg_328_, lean_object* v_s_329_){
_start:
{
uint8_t v___x_330_; 
v___x_330_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_arg_328_, v_s_329_);
return v___x_330_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_dependsOn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_arg_328_ = stack[0].m_obj;
lean_object* v_s_329_ = stack[1].m_obj;
uint8_t v_res_331_;
v_res_331_ = l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(v_arg_328_, v_s_329_);
stack->m_num = v_res_331_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_dependsOn___redArg___boxed(lean_object* v_arg_332_, lean_object* v_s_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Lean_Compiler_LCNF_Arg_dependsOn___redArg(v_arg_332_, v_s_333_);
lean_dec(v_s_333_);
lean_dec(v_arg_332_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
uint8_t l_Lean_Compiler_LCNF_Arg_dependsOn(uint8_t v_pu_336_, lean_object* v_arg_337_, lean_object* v_s_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_arg_337_, v_s_338_);
return v___x_339_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Arg_dependsOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_336_ = stack[0].m_num;
lean_object* v_arg_337_ = stack[1].m_obj;
lean_object* v_s_338_ = stack[2].m_obj;
uint8_t v_res_340_;
v_res_340_ = l_Lean_Compiler_LCNF_Arg_dependsOn(v_pu_336_, v_arg_337_, v_s_338_);
stack->m_num = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_dependsOn___boxed(lean_object* v_pu_341_, lean_object* v_arg_342_, lean_object* v_s_343_){
_start:
{
uint8_t v_pu_boxed_344_; uint8_t v_res_345_; lean_object* v_r_346_; 
v_pu_boxed_344_ = lean_unbox(v_pu_341_);
v_res_345_ = l_Lean_Compiler_LCNF_Arg_dependsOn(v_pu_boxed_344_, v_arg_342_, v_s_343_);
lean_dec(v_s_343_);
lean_dec(v_arg_342_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
uint8_t l_Lean_Compiler_LCNF_LetValue_dependsOn(uint8_t v_pu_347_, lean_object* v_value_348_, lean_object* v_s_349_){
_start:
{
uint8_t v___x_350_; 
v___x_350_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_letValueDepOn(v_pu_347_, v_value_348_, v_s_349_);
return v___x_350_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetValue_dependsOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_347_ = stack[0].m_num;
lean_object* v_value_348_ = stack[1].m_obj;
lean_object* v_s_349_ = stack[2].m_obj;
uint8_t v_res_351_;
v_res_351_ = l_Lean_Compiler_LCNF_LetValue_dependsOn(v_pu_347_, v_value_348_, v_s_349_);
stack->m_num = v_res_351_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_dependsOn___boxed(lean_object* v_pu_352_, lean_object* v_value_353_, lean_object* v_s_354_){
_start:
{
uint8_t v_pu_boxed_355_; uint8_t v_res_356_; lean_object* v_r_357_; 
v_pu_boxed_355_ = lean_unbox(v_pu_352_);
v_res_356_ = l_Lean_Compiler_LCNF_LetValue_dependsOn(v_pu_boxed_355_, v_value_353_, v_s_354_);
lean_dec(v_s_354_);
lean_dec(v_value_353_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
uint8_t l_Lean_Compiler_LCNF_LetDecl_dependsOn(uint8_t v_pu_358_, lean_object* v_decl_359_, lean_object* v_s_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_358_, v_decl_359_, v_s_360_);
return v___x_361_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_LetDecl_dependsOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_358_ = stack[0].m_num;
lean_object* v_decl_359_ = stack[1].m_obj;
lean_object* v_s_360_ = stack[2].m_obj;
uint8_t v_res_362_;
v_res_362_ = l_Lean_Compiler_LCNF_LetDecl_dependsOn(v_pu_358_, v_decl_359_, v_s_360_);
stack->m_num = v_res_362_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_dependsOn___boxed(lean_object* v_pu_363_, lean_object* v_decl_364_, lean_object* v_s_365_){
_start:
{
uint8_t v_pu_boxed_366_; uint8_t v_res_367_; lean_object* v_r_368_; 
v_pu_boxed_366_ = lean_unbox(v_pu_363_);
v_res_367_ = l_Lean_Compiler_LCNF_LetDecl_dependsOn(v_pu_boxed_366_, v_decl_364_, v_s_365_);
lean_dec(v_s_365_);
lean_dec_ref(v_decl_364_);
v_r_368_ = lean_box(v_res_367_);
return v_r_368_;
}
}
uint8_t l_Lean_Compiler_LCNF_FunDecl_dependsOn(uint8_t v_pu_369_, lean_object* v_decl_370_, lean_object* v_s_371_){
_start:
{
lean_object* v_type_372_; lean_object* v_value_373_; uint8_t v___x_374_; 
v_type_372_ = lean_ctor_get(v_decl_370_, 3);
v_value_373_ = lean_ctor_get(v_decl_370_, 4);
v___x_374_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_371_, v_type_372_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; 
v___x_375_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_369_, v_value_373_, v_s_371_);
return v___x_375_;
}
else
{
return v___x_374_;
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_FunDecl_dependsOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_369_ = stack[0].m_num;
lean_object* v_decl_370_ = stack[1].m_obj;
lean_object* v_s_371_ = stack[2].m_obj;
uint8_t v_res_376_;
v_res_376_ = l_Lean_Compiler_LCNF_FunDecl_dependsOn(v_pu_369_, v_decl_370_, v_s_371_);
stack->m_num = v_res_376_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_dependsOn___boxed(lean_object* v_pu_377_, lean_object* v_decl_378_, lean_object* v_s_379_){
_start:
{
uint8_t v_pu_boxed_380_; uint8_t v_res_381_; lean_object* v_r_382_; 
v_pu_boxed_380_ = lean_unbox(v_pu_377_);
v_res_381_ = l_Lean_Compiler_LCNF_FunDecl_dependsOn(v_pu_boxed_380_, v_decl_378_, v_s_379_);
lean_dec(v_s_379_);
lean_dec_ref(v_decl_378_);
v_r_382_ = lean_box(v_res_381_);
return v_r_382_;
}
}
uint8_t l_Lean_Compiler_LCNF_CodeDecl_dependsOn(uint8_t v_pu_383_, lean_object* v_decl_384_, lean_object* v_s_385_){
_start:
{
switch(lean_obj_tag(v_decl_384_))
{
case 0:
{
lean_object* v_decl_386_; uint8_t v___x_387_; 
v_decl_386_ = lean_ctor_get(v_decl_384_, 0);
v___x_387_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_LetDecl_depOn(v_pu_383_, v_decl_386_, v_s_385_);
return v___x_387_;
}
case 1:
{
lean_object* v_decl_388_; lean_object* v_type_389_; lean_object* v_value_390_; uint8_t v___x_391_; 
v_decl_388_ = lean_ctor_get(v_decl_384_, 0);
v_type_389_ = lean_ctor_get(v_decl_388_, 3);
v_value_390_ = lean_ctor_get(v_decl_388_, 4);
v___x_391_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_385_, v_type_389_);
if (v___x_391_ == 0)
{
uint8_t v___x_392_; 
v___x_392_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_383_, v_value_390_, v_s_385_);
return v___x_392_;
}
else
{
return v___x_391_;
}
}
case 2:
{
lean_object* v_decl_393_; lean_object* v_type_394_; lean_object* v_value_395_; uint8_t v___x_396_; 
v_decl_393_ = lean_ctor_get(v_decl_384_, 0);
v_type_394_ = lean_ctor_get(v_decl_393_, 3);
v_value_395_ = lean_ctor_get(v_decl_393_, 4);
v___x_396_ = l___private_Lean_Expr_0__Lean_Expr_hasAnyFVar_visit___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_typeDepOn_spec__0(v_s_385_, v_type_394_);
if (v___x_396_ == 0)
{
uint8_t v___x_397_; 
v___x_397_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_383_, v_value_395_, v_s_385_);
return v___x_397_;
}
else
{
return v___x_396_;
}
}
case 3:
{
lean_object* v_fvarId_398_; lean_object* v_y_399_; uint8_t v___x_400_; 
v_fvarId_398_ = lean_ctor_get(v_decl_384_, 0);
v_y_399_ = lean_ctor_get(v_decl_384_, 2);
v___x_400_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_398_, v_s_385_);
if (v___x_400_ == 0)
{
uint8_t v___x_401_; 
v___x_401_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_argDepOn___redArg(v_y_399_, v_s_385_);
return v___x_401_;
}
else
{
return v___x_400_;
}
}
case 4:
{
lean_object* v_fvarId_402_; lean_object* v_y_403_; uint8_t v___x_404_; 
v_fvarId_402_ = lean_ctor_get(v_decl_384_, 0);
v_y_403_ = lean_ctor_get(v_decl_384_, 2);
v___x_404_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_402_, v_s_385_);
if (v___x_404_ == 0)
{
uint8_t v___x_405_; 
v___x_405_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_403_, v_s_385_);
return v___x_405_;
}
else
{
return v___x_404_;
}
}
case 5:
{
lean_object* v_fvarId_406_; lean_object* v_y_407_; uint8_t v___x_408_; 
v_fvarId_406_ = lean_ctor_get(v_decl_384_, 0);
v_y_407_ = lean_ctor_get(v_decl_384_, 3);
v___x_408_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_406_, v_s_385_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
v___x_409_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_y_407_, v_s_385_);
return v___x_409_;
}
else
{
return v___x_408_;
}
}
default: 
{
lean_object* v_fvarId_410_; uint8_t v___x_411_; 
v_fvarId_410_ = lean_ctor_get(v_decl_384_, 0);
v___x_411_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_fvarDepOn_spec__0___redArg(v_fvarId_410_, v_s_385_);
return v___x_411_;
}
}
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_CodeDecl_dependsOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_383_ = stack[0].m_num;
lean_object* v_decl_384_ = stack[1].m_obj;
lean_object* v_s_385_ = stack[2].m_obj;
uint8_t v_res_412_;
v_res_412_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v_pu_383_, v_decl_384_, v_s_385_);
stack->m_num = v_res_412_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_CodeDecl_dependsOn___boxed(lean_object* v_pu_413_, lean_object* v_decl_414_, lean_object* v_s_415_){
_start:
{
uint8_t v_pu_boxed_416_; uint8_t v_res_417_; lean_object* v_r_418_; 
v_pu_boxed_416_ = lean_unbox(v_pu_413_);
v_res_417_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(v_pu_boxed_416_, v_decl_414_, v_s_415_);
lean_dec(v_s_415_);
lean_dec_ref(v_decl_414_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
uint8_t l_Lean_Compiler_LCNF_Code_dependsOn(uint8_t v_pu_419_, lean_object* v_c_420_, lean_object* v_s_421_){
_start:
{
uint8_t v___x_422_; 
v___x_422_ = l___private_Lean_Compiler_LCNF_DependsOn_0__Lean_Compiler_LCNF_depOn(v_pu_419_, v_c_420_, v_s_421_);
return v___x_422_;
}
}
LEAN_EXPORT void l_Lean_Compiler_LCNF_Code_dependsOn_0interp(lean_interpreter_value* stack)
{
uint8_t v_pu_419_ = stack[0].m_num;
lean_object* v_c_420_ = stack[1].m_obj;
lean_object* v_s_421_ = stack[2].m_obj;
uint8_t v_res_423_;
v_res_423_ = l_Lean_Compiler_LCNF_Code_dependsOn(v_pu_419_, v_c_420_, v_s_421_);
stack->m_num = v_res_423_;
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_dependsOn___boxed(lean_object* v_pu_424_, lean_object* v_c_425_, lean_object* v_s_426_){
_start:
{
uint8_t v_pu_boxed_427_; uint8_t v_res_428_; lean_object* v_r_429_; 
v_pu_boxed_427_ = lean_unbox(v_pu_424_);
v_res_428_ = l_Lean_Compiler_LCNF_Code_dependsOn(v_pu_boxed_427_, v_c_425_, v_s_426_);
lean_dec(v_s_426_);
lean_dec_ref(v_c_425_);
v_r_429_ = lean_box(v_res_428_);
return v_r_429_;
}
}
lean_object* runtime_initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_DependsOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
