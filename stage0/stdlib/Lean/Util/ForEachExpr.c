// Lean compiler output
// Module: Lean.Util.ForEachExpr
// Imports: public import Lean.Expr public import Lean.Util.MonadCache
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ForEachExpr_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExpr_visit___redArg___closed__0 = (const lean_object*)&l_Lean_ForEachExpr_visit___redArg___closed__0_value;
static const lean_closure_object l_Lean_ForEachExpr_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExpr_visit___redArg___closed__1 = (const lean_object*)&l_Lean_ForEachExpr_visit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_forEach_x27___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_forEach_x27___redArg___closed__0;
static lean_once_cell_t l_Lean_Expr_forEach_x27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_forEach_x27___redArg___closed__1;
static lean_once_cell_t l_Lean_Expr_forEach_x27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_forEach_x27___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEach(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9(lean_object* v_toApplicative_1_, lean_object* v___x_2_, lean_object* v___x_3_, lean_object* v_e_4_, lean_object* v_a_5_){
_start:
{
lean_object* v_toPure_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v_toPure_6_ = lean_ctor_get(v_toApplicative_1_, 1);
lean_inc(v_toPure_6_);
lean_dec_ref(v_toApplicative_1_);
v___x_7_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_2_, v___x_3_, v_a_5_, v_e_4_);
v___x_8_ = lean_apply_2(v_toPure_6_, lean_box(0), v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9___boxed(lean_object* v_toApplicative_9_, lean_object* v___x_10_, lean_object* v___x_11_, lean_object* v_e_12_, lean_object* v_a_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_ForEachExpr_visit___redArg___lam__9(v_toApplicative_9_, v___x_10_, v___x_11_, v_e_12_, v_a_13_);
lean_dec_ref(v_a_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__8(lean_object* v_g_15_, lean_object* v_e_16_, lean_object* v_toBind_17_, lean_object* v___f_18_, lean_object* v___f_19_, lean_object* v_toApplicative_20_, lean_object* v_a_21_){
_start:
{
if (lean_obj_tag(v_a_21_) == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec_ref(v_toApplicative_20_);
v___x_22_ = lean_apply_1(v_g_15_, v_e_16_);
lean_inc(v_toBind_17_);
v___x_23_ = lean_apply_4(v_toBind_17_, lean_box(0), lean_box(0), v___x_22_, v___f_18_);
v___x_24_ = lean_apply_4(v_toBind_17_, lean_box(0), lean_box(0), v___x_23_, v___f_19_);
return v___x_24_;
}
else
{
lean_object* v_val_25_; lean_object* v_toPure_26_; lean_object* v___x_27_; 
lean_dec(v___f_19_);
lean_dec(v___f_18_);
lean_dec(v_toBind_17_);
lean_dec_ref(v_e_16_);
lean_dec(v_g_15_);
v_val_25_ = lean_ctor_get(v_a_21_, 0);
lean_inc(v_val_25_);
lean_dec_ref_known(v_a_21_, 1);
v_toPure_26_ = lean_ctor_get(v_toApplicative_20_, 1);
lean_inc(v_toPure_26_);
lean_dec_ref(v_toApplicative_20_);
v___x_27_ = lean_apply_2(v_toPure_26_, lean_box(0), v_val_25_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__5(lean_object* v_toApplicative_28_, lean_object* v_a_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_toPure_31_; lean_object* v___x_32_; 
v_toPure_31_ = lean_ctor_get(v_toApplicative_28_, 1);
lean_inc(v_toPure_31_);
lean_dec_ref(v_toApplicative_28_);
v___x_32_ = lean_apply_2(v_toPure_31_, lean_box(0), v_a_29_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__6(lean_object* v___x_33_, lean_object* v___x_34_, lean_object* v_e_35_, lean_object* v_a_36_, lean_object* v_s_37_){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_33_, v___x_34_, v_s_37_, v_e_35_, v_a_36_);
v___x_40_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_40_, 0, v___x_38_);
lean_ctor_set(v___x_40_, 1, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__7(lean_object* v_toApplicative_41_, lean_object* v___x_42_, lean_object* v___x_43_, lean_object* v_e_44_, lean_object* v_a_45_, lean_object* v_inst_46_, lean_object* v_toBind_47_, lean_object* v_a_48_){
_start:
{
lean_object* v___f_49_; lean_object* v___f_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___f_49_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__5), 3, 2);
lean_closure_set(v___f_49_, 0, v_toApplicative_41_);
lean_closure_set(v___f_49_, 1, v_a_48_);
v___f_50_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__6), 5, 4);
lean_closure_set(v___f_50_, 0, v___x_42_);
lean_closure_set(v___f_50_, 1, v___x_43_);
lean_closure_set(v___f_50_, 2, v_e_44_);
lean_closure_set(v___f_50_, 3, v_a_48_);
lean_inc(v_a_45_);
v___x_51_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_modifyGetUnsafe___boxed), 6, 5);
lean_closure_set(v___x_51_, 0, lean_box(0));
lean_closure_set(v___x_51_, 1, lean_box(0));
lean_closure_set(v___x_51_, 2, lean_box(0));
lean_closure_set(v___x_51_, 3, v_a_45_);
lean_closure_set(v___x_51_, 4, v___f_50_);
v___x_52_ = lean_apply_2(v_inst_46_, lean_box(0), v___x_51_);
v___x_53_ = lean_apply_4(v_toBind_47_, lean_box(0), lean_box(0), v___x_52_, v___f_49_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__7___boxed(lean_object* v_toApplicative_54_, lean_object* v___x_55_, lean_object* v___x_56_, lean_object* v_e_57_, lean_object* v_a_58_, lean_object* v_inst_59_, lean_object* v_toBind_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_ForEachExpr_visit___redArg___lam__7(v_toApplicative_54_, v___x_55_, v___x_56_, v_e_57_, v_a_58_, v_inst_59_, v_toBind_60_, v_a_61_);
lean_dec(v_a_58_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0___boxed(lean_object* v_inst_63_, lean_object* v_inst_64_, lean_object* v_g_65_, lean_object* v_b_66_, lean_object* v___y_67_, lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Lean_ForEachExpr_visit___redArg___lam__0(v_inst_63_, v_inst_64_, v_g_65_, v_b_66_, v___y_67_, v_a_68_);
lean_dec(v___y_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1(lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_g_72_, lean_object* v_body_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_ForEachExpr_visit___redArg(v_inst_70_, v_inst_71_, v_g_72_, v_body_73_, v_a_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1___boxed(lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_g_79_, lean_object* v_body_80_, lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l_Lean_ForEachExpr_visit___redArg___lam__1(v_inst_77_, v_inst_78_, v_g_79_, v_body_80_, v_a_81_, v_a_82_);
lean_dec(v_a_81_);
return v_res_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2(lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_g_86_, lean_object* v_value_87_, lean_object* v_a_88_, lean_object* v_toBind_89_, lean_object* v___f_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = l_Lean_ForEachExpr_visit___redArg(v_inst_84_, v_inst_85_, v_g_86_, v_value_87_, v_a_88_);
v___x_93_ = lean_apply_4(v_toBind_89_, lean_box(0), lean_box(0), v___x_92_, v___f_90_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2___boxed(lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_g_96_, lean_object* v_value_97_, lean_object* v_a_98_, lean_object* v_toBind_99_, lean_object* v___f_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_ForEachExpr_visit___redArg___lam__2(v_inst_94_, v_inst_95_, v_g_96_, v_value_97_, v_a_98_, v_toBind_99_, v___f_100_, v_a_101_);
lean_dec(v_a_98_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3(lean_object* v_inst_103_, lean_object* v_inst_104_, lean_object* v_g_105_, lean_object* v_arg_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_ForEachExpr_visit___redArg(v_inst_103_, v_inst_104_, v_g_105_, v_arg_106_, v_a_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3___boxed(lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_g_112_, lean_object* v_arg_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_ForEachExpr_visit___redArg___lam__3(v_inst_110_, v_inst_111_, v_g_112_, v_arg_113_, v_a_114_, v_a_115_);
lean_dec(v_a_114_);
return v_res_116_;
}
}
lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4(lean_object* v_toApplicative_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_g_120_, lean_object* v_toBind_121_, lean_object* v_e_122_, lean_object* v_a_123_, uint8_t v_a_124_){
_start:
{
lean_object* v_d_126_; lean_object* v_b_127_; lean_object* v___y_128_; 
if (v_a_124_ == 0)
{
lean_object* v_toPure_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec_ref(v_e_122_);
lean_dec(v_toBind_121_);
lean_dec(v_g_120_);
lean_dec_ref(v_inst_119_);
lean_dec(v_inst_118_);
v_toPure_132_ = lean_ctor_get(v_toApplicative_117_, 1);
lean_inc(v_toPure_132_);
lean_dec_ref(v_toApplicative_117_);
v___x_133_ = lean_box(0);
v___x_134_ = lean_apply_2(v_toPure_132_, lean_box(0), v___x_133_);
return v___x_134_;
}
else
{
switch(lean_obj_tag(v_e_122_))
{
case 7:
{
lean_object* v_binderType_135_; lean_object* v_body_136_; 
lean_dec_ref(v_toApplicative_117_);
v_binderType_135_ = lean_ctor_get(v_e_122_, 1);
lean_inc_ref(v_binderType_135_);
v_body_136_ = lean_ctor_get(v_e_122_, 2);
lean_inc_ref(v_body_136_);
lean_dec_ref_known(v_e_122_, 3);
v_d_126_ = v_binderType_135_;
v_b_127_ = v_body_136_;
v___y_128_ = v_a_123_;
goto v___jp_125_;
}
case 6:
{
lean_object* v_binderType_137_; lean_object* v_body_138_; 
lean_dec_ref(v_toApplicative_117_);
v_binderType_137_ = lean_ctor_get(v_e_122_, 1);
lean_inc_ref(v_binderType_137_);
v_body_138_ = lean_ctor_get(v_e_122_, 2);
lean_inc_ref(v_body_138_);
lean_dec_ref_known(v_e_122_, 3);
v_d_126_ = v_binderType_137_;
v_b_127_ = v_body_138_;
v___y_128_ = v_a_123_;
goto v___jp_125_;
}
case 8:
{
lean_object* v_type_139_; lean_object* v_value_140_; lean_object* v_body_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec_ref(v_toApplicative_117_);
v_type_139_ = lean_ctor_get(v_e_122_, 1);
lean_inc_ref(v_type_139_);
v_value_140_ = lean_ctor_get(v_e_122_, 2);
lean_inc_ref(v_value_140_);
v_body_141_ = lean_ctor_get(v_e_122_, 3);
lean_inc_ref(v_body_141_);
lean_dec_ref_known(v_e_122_, 4);
lean_inc_n(v_a_123_, 2);
lean_inc_n(v_g_120_, 2);
lean_inc_ref_n(v_inst_119_, 2);
lean_inc_n(v_inst_118_, 2);
v___f_142_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_142_, 0, v_inst_118_);
lean_closure_set(v___f_142_, 1, v_inst_119_);
lean_closure_set(v___f_142_, 2, v_g_120_);
lean_closure_set(v___f_142_, 3, v_body_141_);
lean_closure_set(v___f_142_, 4, v_a_123_);
lean_inc(v_toBind_121_);
v___f_143_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_143_, 0, v_inst_118_);
lean_closure_set(v___f_143_, 1, v_inst_119_);
lean_closure_set(v___f_143_, 2, v_g_120_);
lean_closure_set(v___f_143_, 3, v_value_140_);
lean_closure_set(v___f_143_, 4, v_a_123_);
lean_closure_set(v___f_143_, 5, v_toBind_121_);
lean_closure_set(v___f_143_, 6, v___f_142_);
v___x_144_ = l_Lean_ForEachExpr_visit___redArg(v_inst_118_, v_inst_119_, v_g_120_, v_type_139_, v_a_123_);
v___x_145_ = lean_apply_4(v_toBind_121_, lean_box(0), lean_box(0), v___x_144_, v___f_143_);
return v___x_145_;
}
case 5:
{
lean_object* v_fn_146_; lean_object* v_arg_147_; lean_object* v___f_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
lean_dec_ref(v_toApplicative_117_);
v_fn_146_ = lean_ctor_get(v_e_122_, 0);
lean_inc_ref(v_fn_146_);
v_arg_147_ = lean_ctor_get(v_e_122_, 1);
lean_inc_ref(v_arg_147_);
lean_dec_ref_known(v_e_122_, 2);
lean_inc(v_a_123_);
lean_inc(v_g_120_);
lean_inc_ref(v_inst_119_);
lean_inc(v_inst_118_);
v___f_148_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__3___boxed), 6, 5);
lean_closure_set(v___f_148_, 0, v_inst_118_);
lean_closure_set(v___f_148_, 1, v_inst_119_);
lean_closure_set(v___f_148_, 2, v_g_120_);
lean_closure_set(v___f_148_, 3, v_arg_147_);
lean_closure_set(v___f_148_, 4, v_a_123_);
v___x_149_ = l_Lean_ForEachExpr_visit___redArg(v_inst_118_, v_inst_119_, v_g_120_, v_fn_146_, v_a_123_);
v___x_150_ = lean_apply_4(v_toBind_121_, lean_box(0), lean_box(0), v___x_149_, v___f_148_);
return v___x_150_;
}
case 10:
{
lean_object* v_expr_151_; lean_object* v___x_152_; 
lean_dec(v_toBind_121_);
lean_dec_ref(v_toApplicative_117_);
v_expr_151_ = lean_ctor_get(v_e_122_, 1);
lean_inc_ref(v_expr_151_);
lean_dec_ref_known(v_e_122_, 2);
v___x_152_ = l_Lean_ForEachExpr_visit___redArg(v_inst_118_, v_inst_119_, v_g_120_, v_expr_151_, v_a_123_);
return v___x_152_;
}
case 11:
{
lean_object* v_struct_153_; lean_object* v___x_154_; 
lean_dec(v_toBind_121_);
lean_dec_ref(v_toApplicative_117_);
v_struct_153_ = lean_ctor_get(v_e_122_, 2);
lean_inc_ref(v_struct_153_);
lean_dec_ref_known(v_e_122_, 3);
v___x_154_ = l_Lean_ForEachExpr_visit___redArg(v_inst_118_, v_inst_119_, v_g_120_, v_struct_153_, v_a_123_);
return v___x_154_;
}
default: 
{
lean_object* v_toPure_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec_ref(v_e_122_);
lean_dec(v_toBind_121_);
lean_dec(v_g_120_);
lean_dec_ref(v_inst_119_);
lean_dec(v_inst_118_);
v_toPure_155_ = lean_ctor_get(v_toApplicative_117_, 1);
lean_inc(v_toPure_155_);
lean_dec_ref(v_toApplicative_117_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_apply_2(v_toPure_155_, lean_box(0), v___x_156_);
return v___x_157_;
}
}
}
v___jp_125_:
{
lean_object* v___f_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
lean_inc(v___y_128_);
lean_inc(v_g_120_);
lean_inc_ref(v_inst_119_);
lean_inc(v_inst_118_);
v___f_129_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_129_, 0, v_inst_118_);
lean_closure_set(v___f_129_, 1, v_inst_119_);
lean_closure_set(v___f_129_, 2, v_g_120_);
lean_closure_set(v___f_129_, 3, v_b_127_);
lean_closure_set(v___f_129_, 4, v___y_128_);
v___x_130_ = l_Lean_ForEachExpr_visit___redArg(v_inst_118_, v_inst_119_, v_g_120_, v_d_126_, v___y_128_);
v___x_131_ = lean_apply_4(v_toBind_121_, lean_box(0), lean_box(0), v___x_130_, v___f_129_);
return v___x_131_;
}
}
}
LEAN_EXPORT void l_Lean_ForEachExpr_visit___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_toApplicative_117_ = stack[0].m_obj;
lean_object* v_inst_118_ = stack[1].m_obj;
lean_object* v_inst_119_ = stack[2].m_obj;
lean_object* v_g_120_ = stack[3].m_obj;
lean_object* v_toBind_121_ = stack[4].m_obj;
lean_object* v_e_122_ = stack[5].m_obj;
lean_object* v_a_123_ = stack[6].m_obj;
uint8_t v_a_124_ = stack[7].m_num;
lean_object* v_res_158_;
v_res_158_ = l_Lean_ForEachExpr_visit___redArg___lam__4(v_toApplicative_117_, v_inst_118_, v_inst_119_, v_g_120_, v_toBind_121_, v_e_122_, v_a_123_, v_a_124_);
stack->m_obj
 = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4___boxed(lean_object* v_toApplicative_159_, lean_object* v_inst_160_, lean_object* v_inst_161_, lean_object* v_g_162_, lean_object* v_toBind_163_, lean_object* v_e_164_, lean_object* v_a_165_, lean_object* v_a_166_){
_start:
{
uint8_t v_a_boxed_167_; lean_object* v_res_168_; 
v_a_boxed_167_ = lean_unbox(v_a_166_);
v_res_168_ = l_Lean_ForEachExpr_visit___redArg___lam__4(v_toApplicative_159_, v_inst_160_, v_inst_161_, v_g_162_, v_toBind_163_, v_e_164_, v_a_165_, v_a_boxed_167_);
lean_dec(v_a_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_g_173_, lean_object* v_e_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_toApplicative_176_; lean_object* v_toBind_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___f_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_toApplicative_176_ = lean_ctor_get(v_inst_172_, 0);
lean_inc_ref_n(v_toApplicative_176_, 4);
v_toBind_177_ = lean_ctor_get(v_inst_172_, 1);
lean_inc_n(v_toBind_177_, 5);
lean_inc_n(v_a_175_, 3);
lean_inc_ref_n(v_e_174_, 3);
lean_inc(v_g_173_);
lean_inc_n(v_inst_171_, 2);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_178_, 0, v_toApplicative_176_);
lean_closure_set(v___f_178_, 1, v_inst_171_);
lean_closure_set(v___f_178_, 2, v_inst_172_);
lean_closure_set(v___f_178_, 3, v_g_173_);
lean_closure_set(v___f_178_, 4, v_toBind_177_);
lean_closure_set(v___f_178_, 5, v_e_174_);
lean_closure_set(v___f_178_, 6, v_a_175_);
v___x_179_ = ((lean_object*)(l_Lean_ForEachExpr_visit___redArg___closed__0));
v___x_180_ = ((lean_object*)(l_Lean_ForEachExpr_visit___redArg___closed__1));
v___f_181_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__7___boxed), 8, 7);
lean_closure_set(v___f_181_, 0, v_toApplicative_176_);
lean_closure_set(v___f_181_, 1, v___x_179_);
lean_closure_set(v___f_181_, 2, v___x_180_);
lean_closure_set(v___f_181_, 3, v_e_174_);
lean_closure_set(v___f_181_, 4, v_a_175_);
lean_closure_set(v___f_181_, 5, v_inst_171_);
lean_closure_set(v___f_181_, 6, v_toBind_177_);
v___f_182_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__8), 7, 6);
lean_closure_set(v___f_182_, 0, v_g_173_);
lean_closure_set(v___f_182_, 1, v_e_174_);
lean_closure_set(v___f_182_, 2, v_toBind_177_);
lean_closure_set(v___f_182_, 3, v___f_178_);
lean_closure_set(v___f_182_, 4, v___f_181_);
lean_closure_set(v___f_182_, 5, v_toApplicative_176_);
v___f_183_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__9___boxed), 5, 4);
lean_closure_set(v___f_183_, 0, v_toApplicative_176_);
lean_closure_set(v___f_183_, 1, v___x_179_);
lean_closure_set(v___f_183_, 2, v___x_180_);
lean_closure_set(v___f_183_, 3, v_e_174_);
v___x_184_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_184_, 0, lean_box(0));
lean_closure_set(v___x_184_, 1, lean_box(0));
lean_closure_set(v___x_184_, 2, v_a_175_);
v___x_185_ = lean_apply_2(v_inst_171_, lean_box(0), v___x_184_);
v___x_186_ = lean_apply_4(v_toBind_177_, lean_box(0), lean_box(0), v___x_185_, v___f_183_);
v___x_187_ = lean_apply_4(v_toBind_177_, lean_box(0), lean_box(0), v___x_186_, v___f_182_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0(lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_g_190_, lean_object* v_b_191_, lean_object* v___y_192_, lean_object* v_a_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_ForEachExpr_visit___redArg(v_inst_188_, v_inst_189_, v_g_190_, v_b_191_, v___y_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___boxed(lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_g_197_, lean_object* v_e_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_ForEachExpr_visit___redArg(v_inst_195_, v_inst_196_, v_g_197_, v_e_198_, v_a_199_);
lean_dec(v_a_199_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit(lean_object* v_00_u03c9_201_, lean_object* v_m_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_g_206_, lean_object* v_e_207_, lean_object* v_a_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_ForEachExpr_visit___redArg(v_inst_204_, v_inst_205_, v_g_206_, v_e_207_, v_a_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___boxed(lean_object* v_00_u03c9_210_, lean_object* v_m_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_g_215_, lean_object* v_e_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_ForEachExpr_visit(v_00_u03c9_210_, v_m_211_, v_inst_212_, v_inst_213_, v_inst_214_, v_g_215_, v_e_216_, v_a_217_);
lean_dec(v_a_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__0(lean_object* v_toPure_219_, lean_object* v_____x_220_){
_start:
{
lean_object* v_fst_221_; lean_object* v___x_222_; 
v_fst_221_ = lean_ctor_get(v_____x_220_, 0);
lean_inc(v_fst_221_);
lean_dec_ref(v_____x_220_);
v___x_222_ = lean_apply_2(v_toPure_219_, lean_box(0), v_fst_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__1(lean_object* v_a_223_, lean_object* v_toPure_224_, lean_object* v_s_225_){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_226_, 0, v_a_223_);
lean_ctor_set(v___x_226_, 1, v_s_225_);
v___x_227_ = lean_apply_2(v_toPure_224_, lean_box(0), v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__2(lean_object* v_toPure_228_, lean_object* v_ref_229_, lean_object* v_inst_230_, lean_object* v_toBind_231_, lean_object* v_a_232_){
_start:
{
lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___f_233_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_233_, 0, v_a_232_);
lean_closure_set(v___f_233_, 1, v_toPure_228_);
v___x_234_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_234_, 0, lean_box(0));
lean_closure_set(v___x_234_, 1, lean_box(0));
lean_closure_set(v___x_234_, 2, v_ref_229_);
v___x_235_ = lean_apply_2(v_inst_230_, lean_box(0), v___x_234_);
v___x_236_ = lean_apply_4(v_toBind_231_, lean_box(0), lean_box(0), v___x_235_, v___f_233_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__3(lean_object* v_toPure_237_, lean_object* v_inst_238_, lean_object* v_toBind_239_, lean_object* v_inst_240_, lean_object* v_f_241_, lean_object* v_e_242_, lean_object* v_ref_243_){
_start:
{
lean_object* v___f_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
lean_inc(v_toBind_239_);
lean_inc(v_inst_238_);
lean_inc(v_ref_243_);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__2), 5, 4);
lean_closure_set(v___f_244_, 0, v_toPure_237_);
lean_closure_set(v___f_244_, 1, v_ref_243_);
lean_closure_set(v___f_244_, 2, v_inst_238_);
lean_closure_set(v___f_244_, 3, v_toBind_239_);
v___x_245_ = l_Lean_ForEachExpr_visit___redArg(v_inst_238_, v_inst_240_, v_f_241_, v_e_242_, v_ref_243_);
lean_dec(v_ref_243_);
v___x_246_ = lean_apply_4(v_toBind_239_, lean_box(0), lean_box(0), v___x_245_, v___f_244_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_247_ = lean_box(0);
v___x_248_ = lean_unsigned_to_nat(16u);
v___x_249_ = lean_mk_array(v___x_248_, v___x_247_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_250_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__0, &l_Lean_Expr_forEach_x27___redArg___closed__0_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__0);
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_250_);
return v___x_252_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__1, &l_Lean_Expr_forEach_x27___redArg___closed__1_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__1);
v___x_254_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_254_, 0, lean_box(0));
lean_closure_set(v___x_254_, 1, lean_box(0));
lean_closure_set(v___x_254_, 2, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg(lean_object* v_inst_255_, lean_object* v_inst_256_, lean_object* v_e_257_, lean_object* v_f_258_){
_start:
{
lean_object* v_toApplicative_259_; lean_object* v_toBind_260_; lean_object* v_toPure_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___f_264_; lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v_toApplicative_259_ = lean_ctor_get(v_inst_256_, 0);
v_toBind_260_ = lean_ctor_get(v_inst_256_, 1);
lean_inc_n(v_toBind_260_, 3);
v_toPure_261_ = lean_ctor_get(v_toApplicative_259_, 1);
lean_inc_n(v_toPure_261_, 2);
v___x_262_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__2, &l_Lean_Expr_forEach_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__2);
lean_inc(v_inst_255_);
v___x_263_ = lean_apply_2(v_inst_255_, lean_box(0), v___x_262_);
v___f_264_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_264_, 0, v_toPure_261_);
v___f_265_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_265_, 0, v_toPure_261_);
lean_closure_set(v___f_265_, 1, v_inst_255_);
lean_closure_set(v___f_265_, 2, v_toBind_260_);
lean_closure_set(v___f_265_, 3, v_inst_256_);
lean_closure_set(v___f_265_, 4, v_f_258_);
lean_closure_set(v___f_265_, 5, v_e_257_);
v___x_266_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___x_263_, v___f_265_);
v___x_267_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v___x_266_, v___f_264_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27(lean_object* v_00_u03c9_268_, lean_object* v_m_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_e_273_, lean_object* v_f_274_){
_start:
{
lean_object* v_toApplicative_275_; lean_object* v_toBind_276_; lean_object* v_toPure_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___f_280_; lean_object* v___f_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_toApplicative_275_ = lean_ctor_get(v_inst_272_, 0);
v_toBind_276_ = lean_ctor_get(v_inst_272_, 1);
lean_inc_n(v_toBind_276_, 3);
v_toPure_277_ = lean_ctor_get(v_toApplicative_275_, 1);
lean_inc_n(v_toPure_277_, 2);
v___x_278_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__2, &l_Lean_Expr_forEach_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__2);
lean_inc(v_inst_271_);
v___x_279_ = lean_apply_2(v_inst_271_, lean_box(0), v___x_278_);
v___f_280_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_280_, 0, v_toPure_277_);
v___f_281_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_281_, 0, v_toPure_277_);
lean_closure_set(v___f_281_, 1, v_inst_271_);
lean_closure_set(v___f_281_, 2, v_toBind_276_);
lean_closure_set(v___f_281_, 3, v_inst_272_);
lean_closure_set(v___f_281_, 4, v_f_274_);
lean_closure_set(v___f_281_, 5, v_e_273_);
v___x_282_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v___x_279_, v___f_281_);
v___x_283_ = lean_apply_4(v_toBind_276_, lean_box(0), lean_box(0), v___x_282_, v___f_280_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__1(lean_object* v_toPure_284_, lean_object* v_____r_285_){
_start:
{
uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = 1;
v___x_287_ = lean_box(v___x_286_);
v___x_288_ = lean_apply_2(v_toPure_284_, lean_box(0), v___x_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__0(lean_object* v_f_289_, lean_object* v_toBind_290_, lean_object* v___f_291_, lean_object* v_e_292_){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_apply_1(v_f_289_, v_e_292_);
v___x_294_ = lean_apply_4(v_toBind_290_, lean_box(0), lean_box(0), v___x_293_, v___f_291_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__4(lean_object* v_toPure_295_, lean_object* v_inst_296_, lean_object* v_toBind_297_, lean_object* v_inst_298_, lean_object* v___f_299_, lean_object* v_e_300_, lean_object* v_ref_301_){
_start:
{
lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
lean_inc(v_toBind_297_);
lean_inc(v_inst_296_);
lean_inc(v_ref_301_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__2), 5, 4);
lean_closure_set(v___f_302_, 0, v_toPure_295_);
lean_closure_set(v___f_302_, 1, v_ref_301_);
lean_closure_set(v___f_302_, 2, v_inst_296_);
lean_closure_set(v___f_302_, 3, v_toBind_297_);
v___x_303_ = l_Lean_ForEachExpr_visit___redArg(v_inst_296_, v_inst_298_, v___f_299_, v_e_300_, v_ref_301_);
lean_dec(v_ref_301_);
v___x_304_ = lean_apply_4(v_toBind_297_, lean_box(0), lean_box(0), v___x_303_, v___f_302_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg(lean_object* v_inst_305_, lean_object* v_inst_306_, lean_object* v_e_307_, lean_object* v_f_308_){
_start:
{
lean_object* v_toApplicative_309_; lean_object* v_toBind_310_; lean_object* v_toPure_311_; lean_object* v___f_312_; lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v_toApplicative_309_ = lean_ctor_get(v_inst_306_, 0);
v_toBind_310_ = lean_ctor_get(v_inst_306_, 1);
lean_inc_n(v_toBind_310_, 4);
v_toPure_311_ = lean_ctor_get(v_toApplicative_309_, 1);
lean_inc_n(v_toPure_311_, 3);
v___f_312_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_312_, 0, v_toPure_311_);
v___f_313_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__1), 2, 1);
lean_closure_set(v___f_313_, 0, v_toPure_311_);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__0), 4, 3);
lean_closure_set(v___f_314_, 0, v_f_308_);
lean_closure_set(v___f_314_, 1, v_toBind_310_);
lean_closure_set(v___f_314_, 2, v___f_313_);
lean_inc(v_inst_305_);
v___f_315_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__4), 7, 6);
lean_closure_set(v___f_315_, 0, v_toPure_311_);
lean_closure_set(v___f_315_, 1, v_inst_305_);
lean_closure_set(v___f_315_, 2, v_toBind_310_);
lean_closure_set(v___f_315_, 3, v_inst_306_);
lean_closure_set(v___f_315_, 4, v___f_314_);
lean_closure_set(v___f_315_, 5, v_e_307_);
v___x_316_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__2, &l_Lean_Expr_forEach_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__2);
v___x_317_ = lean_apply_2(v_inst_305_, lean_box(0), v___x_316_);
v___x_318_ = lean_apply_4(v_toBind_310_, lean_box(0), lean_box(0), v___x_317_, v___f_315_);
v___x_319_ = lean_apply_4(v_toBind_310_, lean_box(0), lean_box(0), v___x_318_, v___f_312_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach(lean_object* v_00_u03c9_320_, lean_object* v_m_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_e_325_, lean_object* v_f_326_){
_start:
{
lean_object* v_toApplicative_327_; lean_object* v_toBind_328_; lean_object* v_toPure_329_; lean_object* v___f_330_; lean_object* v___f_331_; lean_object* v___f_332_; lean_object* v___f_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_toApplicative_327_ = lean_ctor_get(v_inst_324_, 0);
v_toBind_328_ = lean_ctor_get(v_inst_324_, 1);
lean_inc_n(v_toBind_328_, 4);
v_toPure_329_ = lean_ctor_get(v_toApplicative_327_, 1);
lean_inc_n(v_toPure_329_, 3);
v___f_330_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_330_, 0, v_toPure_329_);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__1), 2, 1);
lean_closure_set(v___f_331_, 0, v_toPure_329_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__0), 4, 3);
lean_closure_set(v___f_332_, 0, v_f_326_);
lean_closure_set(v___f_332_, 1, v_toBind_328_);
lean_closure_set(v___f_332_, 2, v___f_331_);
lean_inc(v_inst_323_);
v___f_333_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__4), 7, 6);
lean_closure_set(v___f_333_, 0, v_toPure_329_);
lean_closure_set(v___f_333_, 1, v_inst_323_);
lean_closure_set(v___f_333_, 2, v_toBind_328_);
lean_closure_set(v___f_333_, 3, v_inst_324_);
lean_closure_set(v___f_333_, 4, v___f_332_);
lean_closure_set(v___f_333_, 5, v_e_325_);
v___x_334_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__2, &l_Lean_Expr_forEach_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__2);
v___x_335_ = lean_apply_2(v_inst_323_, lean_box(0), v___x_334_);
v___x_336_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_335_, v___f_333_);
v___x_337_ = lean_apply_4(v_toBind_328_, lean_box(0), lean_box(0), v___x_336_, v___f_330_);
return v___x_337_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_ForEachExpr(builtin);
}
#ifdef __cplusplus
}
#endif
