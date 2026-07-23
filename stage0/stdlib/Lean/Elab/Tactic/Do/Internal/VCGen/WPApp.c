// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.WPApp
// Imports: public import Lean.Meta.Sym.SymM import Std.Internal.Do.WP.Basic
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Prog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Prog___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Value(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Value___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_EPred(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_EPred___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post___boxed(lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__2_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__3_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "wp"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__4 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__4_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value_aux_1),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value_aux_2),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(8, 127, 121, 224, 88, 246, 48, 72)}};
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value_aux_3),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(114, 80, 184, 106, 225, 60, 114, 167)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Prog(lean_object* v_info_1_){
_start:
{
lean_object* v_args_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v_args_2_ = lean_ctor_get(v_info_1_, 1);
v___x_3_ = l_Lean_instInhabitedExpr;
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_array_get_borrowed(v___x_3_, v_args_2_, v___x_4_);
lean_inc(v___x_5_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Prog___boxed(lean_object* v_info_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Prog(v_info_6_);
lean_dec_ref(v_info_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(lean_object* v_info_8_){
_start:
{
lean_object* v_args_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; uint8_t v___x_13_; 
v_args_9_ = lean_ctor_get(v_info_8_, 1);
v___x_10_ = l_Lean_instInhabitedExpr;
v___x_11_ = lean_unsigned_to_nat(0u);
v___x_12_ = lean_array_get_borrowed(v___x_10_, v_args_9_, v___x_11_);
v___x_13_ = l_Lean_Expr_isApp(v___x_12_);
if (v___x_13_ == 0)
{
lean_inc(v___x_12_);
return v___x_12_;
}
else
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Expr_appFn_x21(v___x_12_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M___boxed(lean_object* v_info_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_M(v_info_15_);
lean_dec_ref(v_info_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Value(lean_object* v_info_17_){
_start:
{
lean_object* v_args_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v_args_18_ = lean_ctor_get(v_info_17_, 1);
v___x_19_ = l_Lean_instInhabitedExpr;
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = lean_array_get_borrowed(v___x_19_, v_args_18_, v___x_20_);
lean_inc(v___x_21_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Value___boxed(lean_object* v_info_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Value(v_info_22_);
lean_dec_ref(v_info_22_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(lean_object* v_info_24_){
_start:
{
lean_object* v_args_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v_args_25_ = lean_ctor_get(v_info_24_, 1);
v___x_26_ = l_Lean_instInhabitedExpr;
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = lean_array_get_borrowed(v___x_26_, v_args_25_, v___x_27_);
lean_inc(v___x_28_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred___boxed(lean_object* v_info_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_Pred(v_info_29_);
lean_dec_ref(v_info_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_EPred(lean_object* v_info_31_){
_start:
{
lean_object* v_args_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v_args_32_ = lean_ctor_get(v_info_31_, 1);
v___x_33_ = l_Lean_instInhabitedExpr;
v___x_34_ = lean_unsigned_to_nat(3u);
v___x_35_ = lean_array_get_borrowed(v___x_33_, v_args_32_, v___x_34_);
lean_inc(v___x_35_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_EPred___boxed(lean_object* v_info_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_EPred(v_info_36_);
lean_dec_ref(v_info_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(lean_object* v_info_38_){
_start:
{
lean_object* v_args_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v_args_39_ = lean_ctor_get(v_info_38_, 1);
v___x_40_ = l_Lean_instInhabitedExpr;
v___x_41_ = lean_unsigned_to_nat(6u);
v___x_42_ = lean_array_get_borrowed(v___x_40_, v_args_39_, v___x_41_);
lean_inc(v___x_42_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP___boxed(lean_object* v_info_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_instWP(v_info_43_);
lean_dec_ref(v_info_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(lean_object* v_info_45_){
_start:
{
lean_object* v_args_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_args_46_ = lean_ctor_get(v_info_45_, 1);
v___x_47_ = l_Lean_instInhabitedExpr;
v___x_48_ = lean_unsigned_to_nat(7u);
v___x_49_ = lean_array_get_borrowed(v___x_47_, v_args_46_, v___x_48_);
lean_inc(v___x_49_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog___boxed(lean_object* v_info_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_prog(v_info_50_);
lean_dec_ref(v_info_50_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post(lean_object* v_info_52_){
_start:
{
lean_object* v_args_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_args_53_ = lean_ctor_get(v_info_52_, 1);
v___x_54_ = l_Lean_instInhabitedExpr;
v___x_55_ = lean_unsigned_to_nat(8u);
v___x_56_ = lean_array_get_borrowed(v___x_54_, v_args_53_, v___x_55_);
lean_inc(v___x_56_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post___boxed(lean_object* v_info_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp_post(v_info_57_);
lean_dec_ref(v_info_57_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0(lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
uint8_t v___y_74_; 
if (lean_obj_tag(v_x_70_) == 5)
{
lean_object* v_fn_83_; lean_object* v_arg_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_fn_83_ = lean_ctor_get(v_x_70_, 0);
lean_inc_ref(v_fn_83_);
v_arg_84_ = lean_ctor_get(v_x_70_, 1);
lean_inc_ref(v_arg_84_);
lean_dec_ref_known(v_x_70_, 2);
v___x_85_ = lean_array_set(v_x_71_, v_x_72_, v_arg_84_);
v___x_86_ = lean_unsigned_to_nat(1u);
v___x_87_ = lean_nat_sub(v_x_72_, v___x_86_);
lean_dec(v_x_72_);
v_x_70_ = v_fn_83_;
v_x_71_ = v___x_85_;
v_x_72_ = v___x_87_;
goto _start;
}
else
{
lean_object* v___x_89_; uint8_t v___x_90_; 
lean_dec(v_x_72_);
v___x_89_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0___closed__5));
v___x_90_ = l_Lean_Expr_isConstOf(v_x_70_, v___x_89_);
if (v___x_90_ == 0)
{
v___y_74_ = v___x_90_;
goto v___jp_73_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; uint8_t v___x_93_; 
v___x_91_ = lean_unsigned_to_nat(10u);
v___x_92_ = lean_array_get_size(v_x_71_);
v___x_93_ = lean_nat_dec_le(v___x_91_, v___x_92_);
v___y_74_ = v___x_93_;
goto v___jp_73_;
}
}
v___jp_73_:
{
if (v___y_74_ == 0)
{
lean_object* v___x_75_; 
lean_dec_ref(v_x_71_);
lean_dec_ref(v_x_70_);
v___x_75_ = lean_box(0);
return v___x_75_;
}
else
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_76_ = lean_unsigned_to_nat(10u);
v___x_77_ = lean_unsigned_to_nat(0u);
v___x_78_ = l_Array_extract___redArg(v_x_71_, v___x_77_, v___x_76_);
v___x_79_ = lean_array_get_size(v_x_71_);
v___x_80_ = l_Array_extract___redArg(v_x_71_, v___x_76_, v___x_79_);
lean_dec_ref(v_x_71_);
v___x_81_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_81_, 0, v_x_70_);
lean_ctor_set(v___x_81_, 1, v___x_78_);
lean_ctor_set(v___x_81_, 2, v___x_80_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f___closed__0(void){
_start:
{
lean_object* v___x_94_; lean_object* v_dummy_95_; 
v___x_94_ = lean_box(0);
v_dummy_95_ = l_Lean_Expr_sort___override(v___x_94_);
return v_dummy_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f(lean_object* v_rhs_96_){
_start:
{
lean_object* v_dummy_97_; lean_object* v_nargs_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_dummy_97_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f___closed__0);
v_nargs_98_ = l_Lean_Expr_getAppNumArgs(v_rhs_96_);
lean_inc(v_nargs_98_);
v___x_99_ = lean_mk_array(v_nargs_98_, v_dummy_97_);
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_sub(v_nargs_98_, v___x_100_);
lean_dec(v_nargs_98_);
v___x_102_ = l_Lean_Expr_withAppAux___at___00Lean_Elab_Tactic_Do_Internal_VCGen_isWPApp_x3f_spec__0(v_rhs_96_, v___x_99_, v___x_101_);
return v___x_102_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_Do_WP_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_SymM(uint8_t builtin);
lean_object* initialize_Std_Internal_Do_WP_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_SymM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Do_WP_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_WPApp(builtin);
}
#ifdef __cplusplus
}
#endif
