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
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_modifyGetUnsafe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ST_Prim_mkRef___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ForEachExpr_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExpr_visit___redArg___closed__0 = (const lean_object*)&l_Lean_ForEachExpr_visit___redArg___closed__0_value;
static const lean_closure_object l_Lean_ForEachExpr_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExpr_visit___redArg___closed__1 = (const lean_object*)&l_Lean_ForEachExpr_visit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_21_);
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
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__1(lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_g_56_, lean_object* v_body_57_, lean_object* v_a_58_, lean_object* v_a_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Lean_ForEachExpr_visit___redArg(v_inst_54_, v_inst_55_, v_g_56_, v_body_57_, v_a_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__2(lean_object* v_inst_61_, lean_object* v_inst_62_, lean_object* v_g_63_, lean_object* v_value_64_, lean_object* v_a_65_, lean_object* v_toBind_66_, lean_object* v___f_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = l_Lean_ForEachExpr_visit___redArg(v_inst_61_, v_inst_62_, v_g_63_, v_value_64_, v_a_65_);
v___x_70_ = lean_apply_4(v_toBind_66_, lean_box(0), lean_box(0), v___x_69_, v___f_67_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__3(lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_g_73_, lean_object* v_arg_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_ForEachExpr_visit___redArg(v_inst_71_, v_inst_72_, v_g_73_, v_arg_74_, v_a_75_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4(lean_object* v_toApplicative_78_, lean_object* v_inst_79_, lean_object* v_inst_80_, lean_object* v_g_81_, lean_object* v_toBind_82_, lean_object* v_e_83_, lean_object* v_a_84_, uint8_t v_a_85_){
_start:
{
lean_object* v_d_87_; lean_object* v_b_88_; lean_object* v___y_89_; 
if (v_a_85_ == 0)
{
lean_object* v_toPure_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v_a_84_);
lean_dec_ref(v_e_83_);
lean_dec(v_toBind_82_);
lean_dec(v_g_81_);
lean_dec_ref(v_inst_80_);
lean_dec(v_inst_79_);
v_toPure_93_ = lean_ctor_get(v_toApplicative_78_, 1);
lean_inc(v_toPure_93_);
lean_dec_ref(v_toApplicative_78_);
v___x_94_ = lean_box(0);
v___x_95_ = lean_apply_2(v_toPure_93_, lean_box(0), v___x_94_);
return v___x_95_;
}
else
{
switch(lean_obj_tag(v_e_83_))
{
case 7:
{
lean_object* v_binderType_96_; lean_object* v_body_97_; 
lean_dec_ref(v_toApplicative_78_);
v_binderType_96_ = lean_ctor_get(v_e_83_, 1);
lean_inc_ref(v_binderType_96_);
v_body_97_ = lean_ctor_get(v_e_83_, 2);
lean_inc_ref(v_body_97_);
lean_dec_ref(v_e_83_);
v_d_87_ = v_binderType_96_;
v_b_88_ = v_body_97_;
v___y_89_ = v_a_84_;
goto v___jp_86_;
}
case 6:
{
lean_object* v_binderType_98_; lean_object* v_body_99_; 
lean_dec_ref(v_toApplicative_78_);
v_binderType_98_ = lean_ctor_get(v_e_83_, 1);
lean_inc_ref(v_binderType_98_);
v_body_99_ = lean_ctor_get(v_e_83_, 2);
lean_inc_ref(v_body_99_);
lean_dec_ref(v_e_83_);
v_d_87_ = v_binderType_98_;
v_b_88_ = v_body_99_;
v___y_89_ = v_a_84_;
goto v___jp_86_;
}
case 8:
{
lean_object* v_type_100_; lean_object* v_value_101_; lean_object* v_body_102_; lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec_ref(v_toApplicative_78_);
v_type_100_ = lean_ctor_get(v_e_83_, 1);
lean_inc_ref(v_type_100_);
v_value_101_ = lean_ctor_get(v_e_83_, 2);
lean_inc_ref(v_value_101_);
v_body_102_ = lean_ctor_get(v_e_83_, 3);
lean_inc_ref(v_body_102_);
lean_dec_ref(v_e_83_);
lean_inc(v_a_84_);
lean_inc(v_g_81_);
lean_inc_ref(v_inst_80_);
lean_inc(v_inst_79_);
v___f_103_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__1), 6, 5);
lean_closure_set(v___f_103_, 0, v_inst_79_);
lean_closure_set(v___f_103_, 1, v_inst_80_);
lean_closure_set(v___f_103_, 2, v_g_81_);
lean_closure_set(v___f_103_, 3, v_body_102_);
lean_closure_set(v___f_103_, 4, v_a_84_);
lean_inc(v_toBind_82_);
lean_inc(v_a_84_);
lean_inc(v_g_81_);
lean_inc_ref(v_inst_80_);
lean_inc(v_inst_79_);
v___f_104_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__2), 8, 7);
lean_closure_set(v___f_104_, 0, v_inst_79_);
lean_closure_set(v___f_104_, 1, v_inst_80_);
lean_closure_set(v___f_104_, 2, v_g_81_);
lean_closure_set(v___f_104_, 3, v_value_101_);
lean_closure_set(v___f_104_, 4, v_a_84_);
lean_closure_set(v___f_104_, 5, v_toBind_82_);
lean_closure_set(v___f_104_, 6, v___f_103_);
v___x_105_ = l_Lean_ForEachExpr_visit___redArg(v_inst_79_, v_inst_80_, v_g_81_, v_type_100_, v_a_84_);
v___x_106_ = lean_apply_4(v_toBind_82_, lean_box(0), lean_box(0), v___x_105_, v___f_104_);
return v___x_106_;
}
case 5:
{
lean_object* v_fn_107_; lean_object* v_arg_108_; lean_object* v___f_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec_ref(v_toApplicative_78_);
v_fn_107_ = lean_ctor_get(v_e_83_, 0);
lean_inc_ref(v_fn_107_);
v_arg_108_ = lean_ctor_get(v_e_83_, 1);
lean_inc_ref(v_arg_108_);
lean_dec_ref(v_e_83_);
lean_inc(v_a_84_);
lean_inc(v_g_81_);
lean_inc_ref(v_inst_80_);
lean_inc(v_inst_79_);
v___f_109_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__3), 6, 5);
lean_closure_set(v___f_109_, 0, v_inst_79_);
lean_closure_set(v___f_109_, 1, v_inst_80_);
lean_closure_set(v___f_109_, 2, v_g_81_);
lean_closure_set(v___f_109_, 3, v_arg_108_);
lean_closure_set(v___f_109_, 4, v_a_84_);
v___x_110_ = l_Lean_ForEachExpr_visit___redArg(v_inst_79_, v_inst_80_, v_g_81_, v_fn_107_, v_a_84_);
v___x_111_ = lean_apply_4(v_toBind_82_, lean_box(0), lean_box(0), v___x_110_, v___f_109_);
return v___x_111_;
}
case 10:
{
lean_object* v_expr_112_; lean_object* v___x_113_; 
lean_dec(v_toBind_82_);
lean_dec_ref(v_toApplicative_78_);
v_expr_112_ = lean_ctor_get(v_e_83_, 1);
lean_inc_ref(v_expr_112_);
lean_dec_ref(v_e_83_);
v___x_113_ = l_Lean_ForEachExpr_visit___redArg(v_inst_79_, v_inst_80_, v_g_81_, v_expr_112_, v_a_84_);
return v___x_113_;
}
case 11:
{
lean_object* v_struct_114_; lean_object* v___x_115_; 
lean_dec(v_toBind_82_);
lean_dec_ref(v_toApplicative_78_);
v_struct_114_ = lean_ctor_get(v_e_83_, 2);
lean_inc_ref(v_struct_114_);
lean_dec_ref(v_e_83_);
v___x_115_ = l_Lean_ForEachExpr_visit___redArg(v_inst_79_, v_inst_80_, v_g_81_, v_struct_114_, v_a_84_);
return v___x_115_;
}
default: 
{
lean_object* v_toPure_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_a_84_);
lean_dec_ref(v_e_83_);
lean_dec(v_toBind_82_);
lean_dec(v_g_81_);
lean_dec_ref(v_inst_80_);
lean_dec(v_inst_79_);
v_toPure_116_ = lean_ctor_get(v_toApplicative_78_, 1);
lean_inc(v_toPure_116_);
lean_dec_ref(v_toApplicative_78_);
v___x_117_ = lean_box(0);
v___x_118_ = lean_apply_2(v_toPure_116_, lean_box(0), v___x_117_);
return v___x_118_;
}
}
}
v___jp_86_:
{
lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
lean_inc(v___y_89_);
lean_inc(v_g_81_);
lean_inc_ref(v_inst_80_);
lean_inc(v_inst_79_);
v___f_90_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__0), 6, 5);
lean_closure_set(v___f_90_, 0, v_inst_79_);
lean_closure_set(v___f_90_, 1, v_inst_80_);
lean_closure_set(v___f_90_, 2, v_g_81_);
lean_closure_set(v___f_90_, 3, v_b_88_);
lean_closure_set(v___f_90_, 4, v___y_89_);
v___x_91_ = l_Lean_ForEachExpr_visit___redArg(v_inst_79_, v_inst_80_, v_g_81_, v_d_87_, v___y_89_);
v___x_92_ = lean_apply_4(v_toBind_82_, lean_box(0), lean_box(0), v___x_91_, v___f_90_);
return v___x_92_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__4___boxed(lean_object* v_toApplicative_119_, lean_object* v_inst_120_, lean_object* v_inst_121_, lean_object* v_g_122_, lean_object* v_toBind_123_, lean_object* v_e_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
uint8_t v_a_boxed_127_; lean_object* v_res_128_; 
v_a_boxed_127_ = lean_unbox(v_a_126_);
v_res_128_ = l_Lean_ForEachExpr_visit___redArg___lam__4(v_toApplicative_119_, v_inst_120_, v_inst_121_, v_g_122_, v_toBind_123_, v_e_124_, v_a_125_, v_a_boxed_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg(lean_object* v_inst_131_, lean_object* v_inst_132_, lean_object* v_g_133_, lean_object* v_e_134_, lean_object* v_a_135_){
_start:
{
lean_object* v_toApplicative_136_; lean_object* v_toBind_137_; lean_object* v___f_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___f_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_toApplicative_136_ = lean_ctor_get(v_inst_132_, 0);
lean_inc_ref(v_toApplicative_136_);
v_toBind_137_ = lean_ctor_get(v_inst_132_, 1);
lean_inc(v_toBind_137_);
lean_inc(v_a_135_);
lean_inc_ref(v_e_134_);
lean_inc(v_toBind_137_);
lean_inc(v_g_133_);
lean_inc(v_inst_131_);
lean_inc_ref(v_toApplicative_136_);
v___f_138_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_138_, 0, v_toApplicative_136_);
lean_closure_set(v___f_138_, 1, v_inst_131_);
lean_closure_set(v___f_138_, 2, v_inst_132_);
lean_closure_set(v___f_138_, 3, v_g_133_);
lean_closure_set(v___f_138_, 4, v_toBind_137_);
lean_closure_set(v___f_138_, 5, v_e_134_);
lean_closure_set(v___f_138_, 6, v_a_135_);
v___x_139_ = ((lean_object*)(l_Lean_ForEachExpr_visit___redArg___closed__0));
v___x_140_ = ((lean_object*)(l_Lean_ForEachExpr_visit___redArg___closed__1));
lean_inc(v_toBind_137_);
lean_inc(v_inst_131_);
lean_inc(v_a_135_);
lean_inc_ref(v_e_134_);
lean_inc_ref(v_toApplicative_136_);
v___f_141_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__7), 8, 7);
lean_closure_set(v___f_141_, 0, v_toApplicative_136_);
lean_closure_set(v___f_141_, 1, v___x_139_);
lean_closure_set(v___f_141_, 2, v___x_140_);
lean_closure_set(v___f_141_, 3, v_e_134_);
lean_closure_set(v___f_141_, 4, v_a_135_);
lean_closure_set(v___f_141_, 5, v_inst_131_);
lean_closure_set(v___f_141_, 6, v_toBind_137_);
lean_inc_ref(v_toApplicative_136_);
lean_inc(v_toBind_137_);
lean_inc_ref(v_e_134_);
v___f_142_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__8), 7, 6);
lean_closure_set(v___f_142_, 0, v_g_133_);
lean_closure_set(v___f_142_, 1, v_e_134_);
lean_closure_set(v___f_142_, 2, v_toBind_137_);
lean_closure_set(v___f_142_, 3, v___f_138_);
lean_closure_set(v___f_142_, 4, v___f_141_);
lean_closure_set(v___f_142_, 5, v_toApplicative_136_);
v___f_143_ = lean_alloc_closure((void*)(l_Lean_ForEachExpr_visit___redArg___lam__9___boxed), 5, 4);
lean_closure_set(v___f_143_, 0, v_toApplicative_136_);
lean_closure_set(v___f_143_, 1, v___x_139_);
lean_closure_set(v___f_143_, 2, v___x_140_);
lean_closure_set(v___f_143_, 3, v_e_134_);
v___x_144_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_144_, 0, lean_box(0));
lean_closure_set(v___x_144_, 1, lean_box(0));
lean_closure_set(v___x_144_, 2, v_a_135_);
v___x_145_ = lean_apply_2(v_inst_131_, lean_box(0), v___x_144_);
lean_inc(v_toBind_137_);
v___x_146_ = lean_apply_4(v_toBind_137_, lean_box(0), lean_box(0), v___x_145_, v___f_143_);
v___x_147_ = lean_apply_4(v_toBind_137_, lean_box(0), lean_box(0), v___x_146_, v___f_142_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit___redArg___lam__0(lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_g_150_, lean_object* v_b_151_, lean_object* v___y_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_ForEachExpr_visit___redArg(v_inst_148_, v_inst_149_, v_g_150_, v_b_151_, v___y_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExpr_visit(lean_object* v_00_u03c9_155_, lean_object* v_m_156_, lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_g_160_, lean_object* v_e_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Lean_ForEachExpr_visit___redArg(v_inst_158_, v_inst_159_, v_g_160_, v_e_161_, v_a_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__0(lean_object* v_toPure_164_, lean_object* v_____x_165_){
_start:
{
lean_object* v_fst_166_; lean_object* v___x_167_; 
v_fst_166_ = lean_ctor_get(v_____x_165_, 0);
lean_inc(v_fst_166_);
lean_dec_ref(v_____x_165_);
v___x_167_ = lean_apply_2(v_toPure_164_, lean_box(0), v_fst_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__1(lean_object* v_a_168_, lean_object* v_toPure_169_, lean_object* v_s_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v_a_168_);
lean_ctor_set(v___x_171_, 1, v_s_170_);
v___x_172_ = lean_apply_2(v_toPure_169_, lean_box(0), v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__2(lean_object* v_toPure_173_, lean_object* v_ref_174_, lean_object* v_inst_175_, lean_object* v_toBind_176_, lean_object* v_a_177_){
_start:
{
lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___f_178_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__1), 3, 2);
lean_closure_set(v___f_178_, 0, v_a_177_);
lean_closure_set(v___f_178_, 1, v_toPure_173_);
v___x_179_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_179_, 0, lean_box(0));
lean_closure_set(v___x_179_, 1, lean_box(0));
lean_closure_set(v___x_179_, 2, v_ref_174_);
v___x_180_ = lean_apply_2(v_inst_175_, lean_box(0), v___x_179_);
v___x_181_ = lean_apply_4(v_toBind_176_, lean_box(0), lean_box(0), v___x_180_, v___f_178_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg___lam__3(lean_object* v_toPure_182_, lean_object* v_inst_183_, lean_object* v_toBind_184_, lean_object* v_inst_185_, lean_object* v_f_186_, lean_object* v_e_187_, lean_object* v_ref_188_){
_start:
{
lean_object* v___f_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
lean_inc(v_toBind_184_);
lean_inc(v_inst_183_);
lean_inc(v_ref_188_);
v___f_189_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__2), 5, 4);
lean_closure_set(v___f_189_, 0, v_toPure_182_);
lean_closure_set(v___f_189_, 1, v_ref_188_);
lean_closure_set(v___f_189_, 2, v_inst_183_);
lean_closure_set(v___f_189_, 3, v_toBind_184_);
v___x_190_ = l_Lean_ForEachExpr_visit___redArg(v_inst_183_, v_inst_185_, v_f_186_, v_e_187_, v_ref_188_);
v___x_191_ = lean_apply_4(v_toBind_184_, lean_box(0), lean_box(0), v___x_190_, v___f_189_);
return v___x_191_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__0(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = lean_box(0);
v___x_193_ = lean_unsigned_to_nat(16u);
v___x_194_ = lean_mk_array(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__0, &l_Lean_Expr_forEach_x27___redArg___closed__0_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__0);
v___x_196_ = lean_unsigned_to_nat(0u);
v___x_197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set(v___x_197_, 1, v___x_195_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_Expr_forEach_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__1, &l_Lean_Expr_forEach_x27___redArg___closed__1_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__1);
v___x_199_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_199_, 0, lean_box(0));
lean_closure_set(v___x_199_, 1, lean_box(0));
lean_closure_set(v___x_199_, 2, v___x_198_);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27___redArg(lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_e_202_, lean_object* v_f_203_){
_start:
{
lean_object* v_toApplicative_204_; lean_object* v_toBind_205_; lean_object* v_toPure_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_toApplicative_204_ = lean_ctor_get(v_inst_201_, 0);
v_toBind_205_ = lean_ctor_get(v_inst_201_, 1);
lean_inc(v_toBind_205_);
v_toPure_206_ = lean_ctor_get(v_toApplicative_204_, 1);
lean_inc(v_toPure_206_);
v___x_207_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__2, &l_Lean_Expr_forEach_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__2);
lean_inc(v_inst_200_);
v___x_208_ = lean_apply_2(v_inst_200_, lean_box(0), v___x_207_);
lean_inc(v_toPure_206_);
v___f_209_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_209_, 0, v_toPure_206_);
lean_inc(v_toBind_205_);
v___f_210_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_210_, 0, v_toPure_206_);
lean_closure_set(v___f_210_, 1, v_inst_200_);
lean_closure_set(v___f_210_, 2, v_toBind_205_);
lean_closure_set(v___f_210_, 3, v_inst_201_);
lean_closure_set(v___f_210_, 4, v_f_203_);
lean_closure_set(v___f_210_, 5, v_e_202_);
lean_inc(v_toBind_205_);
v___x_211_ = lean_apply_4(v_toBind_205_, lean_box(0), lean_box(0), v___x_208_, v___f_210_);
v___x_212_ = lean_apply_4(v_toBind_205_, lean_box(0), lean_box(0), v___x_211_, v___f_209_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach_x27(lean_object* v_00_u03c9_213_, lean_object* v_m_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_e_218_, lean_object* v_f_219_){
_start:
{
lean_object* v_toApplicative_220_; lean_object* v_toBind_221_; lean_object* v_toPure_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___f_225_; lean_object* v___f_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_toApplicative_220_ = lean_ctor_get(v_inst_217_, 0);
v_toBind_221_ = lean_ctor_get(v_inst_217_, 1);
lean_inc(v_toBind_221_);
v_toPure_222_ = lean_ctor_get(v_toApplicative_220_, 1);
lean_inc(v_toPure_222_);
v___x_223_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__2, &l_Lean_Expr_forEach_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__2);
lean_inc(v_inst_216_);
v___x_224_ = lean_apply_2(v_inst_216_, lean_box(0), v___x_223_);
lean_inc(v_toPure_222_);
v___f_225_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_225_, 0, v_toPure_222_);
lean_inc(v_toBind_221_);
v___f_226_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__3), 7, 6);
lean_closure_set(v___f_226_, 0, v_toPure_222_);
lean_closure_set(v___f_226_, 1, v_inst_216_);
lean_closure_set(v___f_226_, 2, v_toBind_221_);
lean_closure_set(v___f_226_, 3, v_inst_217_);
lean_closure_set(v___f_226_, 4, v_f_219_);
lean_closure_set(v___f_226_, 5, v_e_218_);
lean_inc(v_toBind_221_);
v___x_227_ = lean_apply_4(v_toBind_221_, lean_box(0), lean_box(0), v___x_224_, v___f_226_);
v___x_228_ = lean_apply_4(v_toBind_221_, lean_box(0), lean_box(0), v___x_227_, v___f_225_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__1(lean_object* v_toPure_229_, lean_object* v_____r_230_){
_start:
{
uint8_t v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v___x_231_ = 1;
v___x_232_ = lean_box(v___x_231_);
v___x_233_ = lean_apply_2(v_toPure_229_, lean_box(0), v___x_232_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__0(lean_object* v_f_234_, lean_object* v_toBind_235_, lean_object* v___f_236_, lean_object* v_e_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_apply_1(v_f_234_, v_e_237_);
v___x_239_ = lean_apply_4(v_toBind_235_, lean_box(0), lean_box(0), v___x_238_, v___f_236_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg___lam__4(lean_object* v_toPure_240_, lean_object* v_inst_241_, lean_object* v_toBind_242_, lean_object* v_inst_243_, lean_object* v___f_244_, lean_object* v_e_245_, lean_object* v_ref_246_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
lean_inc(v_toBind_242_);
lean_inc(v_inst_241_);
lean_inc(v_ref_246_);
v___f_247_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__2), 5, 4);
lean_closure_set(v___f_247_, 0, v_toPure_240_);
lean_closure_set(v___f_247_, 1, v_ref_246_);
lean_closure_set(v___f_247_, 2, v_inst_241_);
lean_closure_set(v___f_247_, 3, v_toBind_242_);
v___x_248_ = l_Lean_ForEachExpr_visit___redArg(v_inst_241_, v_inst_243_, v___f_244_, v_e_245_, v_ref_246_);
v___x_249_ = lean_apply_4(v_toBind_242_, lean_box(0), lean_box(0), v___x_248_, v___f_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach___redArg(lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_e_252_, lean_object* v_f_253_){
_start:
{
lean_object* v_toApplicative_254_; lean_object* v_toBind_255_; lean_object* v_toPure_256_; lean_object* v___f_257_; lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___f_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_toApplicative_254_ = lean_ctor_get(v_inst_251_, 0);
v_toBind_255_ = lean_ctor_get(v_inst_251_, 1);
lean_inc(v_toBind_255_);
v_toPure_256_ = lean_ctor_get(v_toApplicative_254_, 1);
lean_inc(v_toPure_256_);
lean_inc(v_toPure_256_);
v___f_257_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_257_, 0, v_toPure_256_);
lean_inc(v_toPure_256_);
v___f_258_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__1), 2, 1);
lean_closure_set(v___f_258_, 0, v_toPure_256_);
lean_inc(v_toBind_255_);
v___f_259_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__0), 4, 3);
lean_closure_set(v___f_259_, 0, v_f_253_);
lean_closure_set(v___f_259_, 1, v_toBind_255_);
lean_closure_set(v___f_259_, 2, v___f_258_);
lean_inc(v_toBind_255_);
lean_inc(v_inst_250_);
v___f_260_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__4), 7, 6);
lean_closure_set(v___f_260_, 0, v_toPure_256_);
lean_closure_set(v___f_260_, 1, v_inst_250_);
lean_closure_set(v___f_260_, 2, v_toBind_255_);
lean_closure_set(v___f_260_, 3, v_inst_251_);
lean_closure_set(v___f_260_, 4, v___f_259_);
lean_closure_set(v___f_260_, 5, v_e_252_);
v___x_261_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__2, &l_Lean_Expr_forEach_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__2);
v___x_262_ = lean_apply_2(v_inst_250_, lean_box(0), v___x_261_);
lean_inc(v_toBind_255_);
v___x_263_ = lean_apply_4(v_toBind_255_, lean_box(0), lean_box(0), v___x_262_, v___f_260_);
v___x_264_ = lean_apply_4(v_toBind_255_, lean_box(0), lean_box(0), v___x_263_, v___f_257_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEach(lean_object* v_00_u03c9_265_, lean_object* v_m_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_e_270_, lean_object* v_f_271_){
_start:
{
lean_object* v_toApplicative_272_; lean_object* v_toBind_273_; lean_object* v_toPure_274_; lean_object* v___f_275_; lean_object* v___f_276_; lean_object* v___f_277_; lean_object* v___f_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_toApplicative_272_ = lean_ctor_get(v_inst_269_, 0);
v_toBind_273_ = lean_ctor_get(v_inst_269_, 1);
lean_inc(v_toBind_273_);
v_toPure_274_ = lean_ctor_get(v_toApplicative_272_, 1);
lean_inc(v_toPure_274_);
lean_inc(v_toPure_274_);
v___f_275_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach_x27___redArg___lam__0), 2, 1);
lean_closure_set(v___f_275_, 0, v_toPure_274_);
lean_inc(v_toPure_274_);
v___f_276_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__1), 2, 1);
lean_closure_set(v___f_276_, 0, v_toPure_274_);
lean_inc(v_toBind_273_);
v___f_277_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__0), 4, 3);
lean_closure_set(v___f_277_, 0, v_f_271_);
lean_closure_set(v___f_277_, 1, v_toBind_273_);
lean_closure_set(v___f_277_, 2, v___f_276_);
lean_inc(v_toBind_273_);
lean_inc(v_inst_268_);
v___f_278_ = lean_alloc_closure((void*)(l_Lean_Expr_forEach___redArg___lam__4), 7, 6);
lean_closure_set(v___f_278_, 0, v_toPure_274_);
lean_closure_set(v___f_278_, 1, v_inst_268_);
lean_closure_set(v___f_278_, 2, v_toBind_273_);
lean_closure_set(v___f_278_, 3, v_inst_269_);
lean_closure_set(v___f_278_, 4, v___f_277_);
lean_closure_set(v___f_278_, 5, v_e_270_);
v___x_279_ = lean_obj_once(&l_Lean_Expr_forEach_x27___redArg___closed__2, &l_Lean_Expr_forEach_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEach_x27___redArg___closed__2);
v___x_280_ = lean_apply_2(v_inst_268_, lean_box(0), v___x_279_);
lean_inc(v_toBind_273_);
v___x_281_ = lean_apply_4(v_toBind_273_, lean_box(0), lean_box(0), v___x_280_, v___f_278_);
v___x_282_ = lean_apply_4(v_toBind_273_, lean_box(0), lean_box(0), v___x_281_, v___f_275_);
return v___x_282_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_ForEachExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
