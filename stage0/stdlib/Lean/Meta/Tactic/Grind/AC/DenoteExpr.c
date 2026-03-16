// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.DenoteExpr
// Imports: public import Lean.Meta.Tactic.Grind.AC.Util
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
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0(lean_object* v_x_1_, lean_object* v___x_2_, lean_object* v_toPure_3_, lean_object* v_____do__lift_4_){
_start:
{
lean_object* v_vars_5_; lean_object* v_size_6_; uint8_t v___x_7_; 
v_vars_5_ = lean_ctor_get(v_____do__lift_4_, 10);
lean_inc_ref(v_vars_5_);
lean_dec_ref(v_____do__lift_4_);
v_size_6_ = lean_ctor_get(v_vars_5_, 2);
v___x_7_ = lean_nat_dec_lt(v_x_1_, v_size_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; lean_object* v___x_9_; 
lean_dec_ref(v_vars_5_);
v___x_8_ = l_outOfBounds___redArg(v___x_2_);
v___x_9_ = lean_apply_2(v_toPure_3_, lean_box(0), v___x_8_);
return v___x_9_;
}
else
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2_, v_vars_5_, v_x_1_);
v___x_11_ = lean_apply_2(v_toPure_3_, lean_box(0), v___x_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed(lean_object* v_x_12_, lean_object* v___x_13_, lean_object* v_toPure_14_, lean_object* v_____do__lift_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0(v_x_12_, v___x_13_, v_toPure_14_, v_____do__lift_15_);
lean_dec(v_x_12_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1(lean_object* v_____do__lift_17_, lean_object* v_____do__lift_18_, lean_object* v_toPure_19_, lean_object* v_x_20_, lean_object* v___x_21_, lean_object* v_____do__lift_22_){
_start:
{
lean_object* v_op_23_; lean_object* v___y_25_; lean_object* v_vars_28_; lean_object* v_size_29_; uint8_t v___x_30_; 
v_op_23_ = lean_ctor_get(v_____do__lift_17_, 3);
lean_inc_ref(v_op_23_);
lean_dec_ref(v_____do__lift_17_);
v_vars_28_ = lean_ctor_get(v_____do__lift_18_, 10);
lean_inc_ref(v_vars_28_);
lean_dec_ref(v_____do__lift_18_);
v_size_29_ = lean_ctor_get(v_vars_28_, 2);
v___x_30_ = lean_nat_dec_lt(v_x_20_, v_size_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; 
lean_dec_ref(v_vars_28_);
v___x_31_ = l_outOfBounds___redArg(v___x_21_);
v___y_25_ = v___x_31_;
goto v___jp_24_;
}
else
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_PersistentArray_get_x21___redArg(v___x_21_, v_vars_28_, v_x_20_);
v___y_25_ = v___x_32_;
goto v___jp_24_;
}
v___jp_24_:
{
lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_26_ = l_Lean_mkAppB(v_op_23_, v___y_25_, v_____do__lift_22_);
v___x_27_ = lean_apply_2(v_toPure_19_, lean_box(0), v___x_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1___boxed(lean_object* v_____do__lift_33_, lean_object* v_____do__lift_34_, lean_object* v_toPure_35_, lean_object* v_x_36_, lean_object* v___x_37_, lean_object* v_____do__lift_38_){
_start:
{
lean_object* v_res_39_; 
v_res_39_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1(v_____do__lift_33_, v_____do__lift_34_, v_toPure_35_, v_x_36_, v___x_37_, v_____do__lift_38_);
lean_dec(v_x_36_);
return v_res_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg(lean_object* v_inst_40_, lean_object* v_inst_41_, lean_object* v_s_42_){
_start:
{
lean_object* v_toApplicative_43_; lean_object* v_toBind_44_; lean_object* v_toPure_45_; lean_object* v___x_46_; 
v_toApplicative_43_ = lean_ctor_get(v_inst_40_, 0);
v_toBind_44_ = lean_ctor_get(v_inst_40_, 1);
lean_inc(v_toBind_44_);
v_toPure_45_ = lean_ctor_get(v_toApplicative_43_, 1);
lean_inc(v_toPure_45_);
v___x_46_ = l_Lean_instInhabitedExpr;
if (lean_obj_tag(v_s_42_) == 0)
{
lean_object* v_x_47_; lean_object* v___f_48_; lean_object* v___x_49_; 
lean_dec_ref(v_inst_40_);
v_x_47_ = lean_ctor_get(v_s_42_, 0);
lean_inc(v_x_47_);
lean_dec_ref(v_s_42_);
v___f_48_ = lean_alloc_closure((void*)(l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_48_, 0, v_x_47_);
lean_closure_set(v___f_48_, 1, v___x_46_);
lean_closure_set(v___f_48_, 2, v_toPure_45_);
v___x_49_ = lean_apply_4(v_toBind_44_, lean_box(0), lean_box(0), v_inst_41_, v___f_48_);
return v___x_49_;
}
else
{
lean_object* v_x_50_; lean_object* v_s_51_; lean_object* v___f_52_; lean_object* v___x_53_; 
v_x_50_ = lean_ctor_get(v_s_42_, 0);
lean_inc(v_x_50_);
v_s_51_ = lean_ctor_get(v_s_42_, 1);
lean_inc_ref(v_s_51_);
lean_dec_ref(v_s_42_);
lean_inc(v_toBind_44_);
lean_inc(v_inst_41_);
v___f_52_ = lean_alloc_closure((void*)(l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__3), 8, 7);
lean_closure_set(v___f_52_, 0, v_toPure_45_);
lean_closure_set(v___f_52_, 1, v_x_50_);
lean_closure_set(v___f_52_, 2, v___x_46_);
lean_closure_set(v___f_52_, 3, v_inst_40_);
lean_closure_set(v___f_52_, 4, v_inst_41_);
lean_closure_set(v___f_52_, 5, v_s_51_);
lean_closure_set(v___f_52_, 6, v_toBind_44_);
v___x_53_ = lean_apply_4(v_toBind_44_, lean_box(0), lean_box(0), v_inst_41_, v___f_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__2(lean_object* v_____do__lift_54_, lean_object* v_toPure_55_, lean_object* v_x_56_, lean_object* v___x_57_, lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_s_60_, lean_object* v_toBind_61_, lean_object* v_____do__lift_62_){
_start:
{
lean_object* v___f_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___f_63_ = lean_alloc_closure((void*)(l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_63_, 0, v_____do__lift_54_);
lean_closure_set(v___f_63_, 1, v_____do__lift_62_);
lean_closure_set(v___f_63_, 2, v_toPure_55_);
lean_closure_set(v___f_63_, 3, v_x_56_);
lean_closure_set(v___f_63_, 4, v___x_57_);
v___x_64_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_58_, v_inst_59_, v_s_60_);
v___x_65_ = lean_apply_4(v_toBind_61_, lean_box(0), lean_box(0), v___x_64_, v___f_63_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__3(lean_object* v_toPure_66_, lean_object* v_x_67_, lean_object* v___x_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_s_71_, lean_object* v_toBind_72_, lean_object* v_____do__lift_73_){
_start:
{
lean_object* v___f_74_; lean_object* v___x_75_; 
lean_inc(v_toBind_72_);
lean_inc(v_inst_70_);
v___f_74_ = lean_alloc_closure((void*)(l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__2), 9, 8);
lean_closure_set(v___f_74_, 0, v_____do__lift_73_);
lean_closure_set(v___f_74_, 1, v_toPure_66_);
lean_closure_set(v___f_74_, 2, v_x_67_);
lean_closure_set(v___f_74_, 3, v___x_68_);
lean_closure_set(v___f_74_, 4, v_inst_69_);
lean_closure_set(v___f_74_, 5, v_inst_70_);
lean_closure_set(v___f_74_, 6, v_s_71_);
lean_closure_set(v___f_74_, 7, v_toBind_72_);
v___x_75_ = lean_apply_4(v_toBind_72_, lean_box(0), lean_box(0), v_inst_70_, v___f_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_denoteExpr(lean_object* v_M_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_s_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_77_, v_inst_78_, v_s_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__1(lean_object* v_____do__lift_81_, lean_object* v_____do__lift_82_, lean_object* v_toPure_83_, lean_object* v_____do__lift_84_){
_start:
{
lean_object* v_op_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_op_85_ = lean_ctor_get(v_____do__lift_81_, 3);
lean_inc_ref(v_op_85_);
lean_dec_ref(v_____do__lift_81_);
v___x_86_ = l_Lean_mkAppB(v_op_85_, v_____do__lift_82_, v_____do__lift_84_);
v___x_87_ = lean_apply_2(v_toPure_83_, lean_box(0), v___x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__2(lean_object* v_toPure_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_rhs_91_, lean_object* v_toBind_92_, lean_object* v_lhs_93_, lean_object* v_____do__lift_94_){
_start:
{
lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
lean_inc(v_toBind_92_);
lean_inc(v_inst_90_);
lean_inc_ref(v_inst_89_);
v___f_95_ = lean_alloc_closure((void*)(l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__0), 7, 6);
lean_closure_set(v___f_95_, 0, v_____do__lift_94_);
lean_closure_set(v___f_95_, 1, v_toPure_88_);
lean_closure_set(v___f_95_, 2, v_inst_89_);
lean_closure_set(v___f_95_, 3, v_inst_90_);
lean_closure_set(v___f_95_, 4, v_rhs_91_);
lean_closure_set(v___f_95_, 5, v_toBind_92_);
v___x_96_ = l_Lean_Grind_AC_Expr_denoteExpr___redArg(v_inst_89_, v_inst_90_, v_lhs_93_);
v___x_97_ = lean_apply_4(v_toBind_92_, lean_box(0), lean_box(0), v___x_96_, v___f_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___redArg(lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_e_100_){
_start:
{
if (lean_obj_tag(v_e_100_) == 0)
{
lean_object* v_toApplicative_101_; lean_object* v_toBind_102_; lean_object* v_toPure_103_; lean_object* v_x_104_; lean_object* v___x_105_; lean_object* v___f_106_; lean_object* v___x_107_; 
v_toApplicative_101_ = lean_ctor_get(v_inst_98_, 0);
lean_inc_ref(v_toApplicative_101_);
v_toBind_102_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_102_);
lean_dec_ref(v_inst_98_);
v_toPure_103_ = lean_ctor_get(v_toApplicative_101_, 1);
lean_inc(v_toPure_103_);
lean_dec_ref(v_toApplicative_101_);
v_x_104_ = lean_ctor_get(v_e_100_, 0);
lean_inc(v_x_104_);
lean_dec_ref(v_e_100_);
v___x_105_ = l_Lean_instInhabitedExpr;
v___f_106_ = lean_alloc_closure((void*)(l_Lean_Grind_AC_Seq_denoteExpr___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_106_, 0, v_x_104_);
lean_closure_set(v___f_106_, 1, v___x_105_);
lean_closure_set(v___f_106_, 2, v_toPure_103_);
v___x_107_ = lean_apply_4(v_toBind_102_, lean_box(0), lean_box(0), v_inst_99_, v___f_106_);
return v___x_107_;
}
else
{
lean_object* v_toApplicative_108_; lean_object* v_toBind_109_; lean_object* v_toPure_110_; lean_object* v_lhs_111_; lean_object* v_rhs_112_; lean_object* v___f_113_; lean_object* v___x_114_; 
v_toApplicative_108_ = lean_ctor_get(v_inst_98_, 0);
v_toBind_109_ = lean_ctor_get(v_inst_98_, 1);
lean_inc(v_toBind_109_);
v_toPure_110_ = lean_ctor_get(v_toApplicative_108_, 1);
lean_inc(v_toPure_110_);
v_lhs_111_ = lean_ctor_get(v_e_100_, 0);
lean_inc_ref(v_lhs_111_);
v_rhs_112_ = lean_ctor_get(v_e_100_, 1);
lean_inc_ref(v_rhs_112_);
lean_dec_ref(v_e_100_);
lean_inc(v_toBind_109_);
lean_inc(v_inst_99_);
v___f_113_ = lean_alloc_closure((void*)(l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__2), 7, 6);
lean_closure_set(v___f_113_, 0, v_toPure_110_);
lean_closure_set(v___f_113_, 1, v_inst_98_);
lean_closure_set(v___f_113_, 2, v_inst_99_);
lean_closure_set(v___f_113_, 3, v_rhs_112_);
lean_closure_set(v___f_113_, 4, v_toBind_109_);
lean_closure_set(v___f_113_, 5, v_lhs_111_);
v___x_114_ = lean_apply_4(v_toBind_109_, lean_box(0), lean_box(0), v_inst_99_, v___f_113_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__0(lean_object* v_____do__lift_115_, lean_object* v_toPure_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_rhs_119_, lean_object* v_toBind_120_, lean_object* v_____do__lift_121_){
_start:
{
lean_object* v___f_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___f_122_ = lean_alloc_closure((void*)(l_Lean_Grind_AC_Expr_denoteExpr___redArg___lam__1), 4, 3);
lean_closure_set(v___f_122_, 0, v_____do__lift_115_);
lean_closure_set(v___f_122_, 1, v_____do__lift_121_);
lean_closure_set(v___f_122_, 2, v_toPure_116_);
v___x_123_ = l_Lean_Grind_AC_Expr_denoteExpr___redArg(v_inst_117_, v_inst_118_, v_rhs_119_);
v___x_124_ = lean_apply_4(v_toBind_120_, lean_box(0), lean_box(0), v___x_123_, v___f_122_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_denoteExpr(lean_object* v_M_125_, lean_object* v_inst_126_, lean_object* v_inst_127_, lean_object* v_e_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Lean_Grind_AC_Expr_denoteExpr___redArg(v_inst_126_, v_inst_127_, v_e_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0(lean_object* v_s_133_, lean_object* v_____do__lift_134_, lean_object* v_toPure_135_, lean_object* v_____do__lift_136_){
_start:
{
lean_object* v_type_137_; lean_object* v_u_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_type_137_ = lean_ctor_get(v_s_133_, 1);
lean_inc_ref(v_type_137_);
v_u_138_ = lean_ctor_get(v_s_133_, 2);
lean_inc(v_u_138_);
lean_dec_ref(v_s_133_);
v___x_139_ = ((lean_object*)(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0___closed__1));
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v_u_138_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = l_Lean_mkConst(v___x_139_, v___x_141_);
v___x_143_ = l_Lean_mkApp3(v___x_142_, v_type_137_, v_____do__lift_134_, v_____do__lift_136_);
v___x_144_ = lean_apply_2(v_toPure_135_, lean_box(0), v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__1(lean_object* v_s_145_, lean_object* v_toPure_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_rhs_149_, lean_object* v_toBind_150_, lean_object* v_____do__lift_151_){
_start:
{
lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___f_152_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__0), 4, 3);
lean_closure_set(v___f_152_, 0, v_s_145_);
lean_closure_set(v___f_152_, 1, v_____do__lift_151_);
lean_closure_set(v___f_152_, 2, v_toPure_146_);
v___x_153_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_147_, v_inst_148_, v_rhs_149_);
v___x_154_ = lean_apply_4(v_toBind_150_, lean_box(0), lean_box(0), v___x_153_, v___f_152_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__2(lean_object* v_c_155_, lean_object* v_toPure_156_, lean_object* v_inst_157_, lean_object* v_inst_158_, lean_object* v_toBind_159_, lean_object* v_s_160_){
_start:
{
lean_object* v_lhs_161_; lean_object* v_rhs_162_; lean_object* v___f_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v_lhs_161_ = lean_ctor_get(v_c_155_, 0);
lean_inc_ref(v_lhs_161_);
v_rhs_162_ = lean_ctor_get(v_c_155_, 1);
lean_inc_ref(v_rhs_162_);
lean_dec_ref(v_c_155_);
lean_inc(v_toBind_159_);
lean_inc(v_inst_158_);
lean_inc_ref(v_inst_157_);
v___f_163_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__1), 7, 6);
lean_closure_set(v___f_163_, 0, v_s_160_);
lean_closure_set(v___f_163_, 1, v_toPure_156_);
lean_closure_set(v___f_163_, 2, v_inst_157_);
lean_closure_set(v___f_163_, 3, v_inst_158_);
lean_closure_set(v___f_163_, 4, v_rhs_162_);
lean_closure_set(v___f_163_, 5, v_toBind_159_);
v___x_164_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_157_, v_inst_158_, v_lhs_161_);
v___x_165_ = lean_apply_4(v_toBind_159_, lean_box(0), lean_box(0), v___x_164_, v___f_163_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg(lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_c_168_){
_start:
{
lean_object* v_toApplicative_169_; lean_object* v_toBind_170_; lean_object* v_toPure_171_; lean_object* v___f_172_; lean_object* v___x_173_; 
v_toApplicative_169_ = lean_ctor_get(v_inst_166_, 0);
v_toBind_170_ = lean_ctor_get(v_inst_166_, 1);
lean_inc(v_toBind_170_);
v_toPure_171_ = lean_ctor_get(v_toApplicative_169_, 1);
lean_inc(v_toPure_171_);
lean_inc(v_toBind_170_);
lean_inc(v_inst_167_);
v___f_172_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg___lam__2), 6, 5);
lean_closure_set(v___f_172_, 0, v_c_168_);
lean_closure_set(v___f_172_, 1, v_toPure_171_);
lean_closure_set(v___f_172_, 2, v_inst_166_);
lean_closure_set(v___f_172_, 3, v_inst_167_);
lean_closure_set(v___f_172_, 4, v_toBind_170_);
v___x_173_ = lean_apply_4(v_toBind_170_, lean_box(0), lean_box(0), v_inst_167_, v___f_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr(lean_object* v_M_174_, lean_object* v_inst_175_, lean_object* v_inst_176_, lean_object* v_c_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Meta_Grind_AC_EqCnstr_denoteExpr___redArg(v_inst_175_, v_inst_176_, v_c_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0(lean_object* v_s_182_, lean_object* v_____do__lift_183_, lean_object* v_toPure_184_, lean_object* v_____do__lift_185_){
_start:
{
lean_object* v_type_186_; lean_object* v_u_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_type_186_ = lean_ctor_get(v_s_182_, 1);
lean_inc_ref(v_type_186_);
v_u_187_ = lean_ctor_get(v_s_182_, 2);
lean_inc(v_u_187_);
lean_dec_ref(v_s_182_);
v___x_188_ = ((lean_object*)(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0___closed__1));
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v_u_187_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = l_Lean_mkConst(v___x_188_, v___x_190_);
v___x_192_ = l_Lean_mkApp3(v___x_191_, v_type_186_, v_____do__lift_183_, v_____do__lift_185_);
v___x_193_ = lean_apply_2(v_toPure_184_, lean_box(0), v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__1(lean_object* v_s_194_, lean_object* v_toPure_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_rhs_198_, lean_object* v_toBind_199_, lean_object* v_____do__lift_200_){
_start:
{
lean_object* v___f_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___f_201_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__0), 4, 3);
lean_closure_set(v___f_201_, 0, v_s_194_);
lean_closure_set(v___f_201_, 1, v_____do__lift_200_);
lean_closure_set(v___f_201_, 2, v_toPure_195_);
v___x_202_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_196_, v_inst_197_, v_rhs_198_);
v___x_203_ = lean_apply_4(v_toBind_199_, lean_box(0), lean_box(0), v___x_202_, v___f_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__2(lean_object* v_c_204_, lean_object* v_toPure_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_toBind_208_, lean_object* v_s_209_){
_start:
{
lean_object* v_lhs_210_; lean_object* v_rhs_211_; lean_object* v___f_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_lhs_210_ = lean_ctor_get(v_c_204_, 0);
lean_inc_ref(v_lhs_210_);
v_rhs_211_ = lean_ctor_get(v_c_204_, 1);
lean_inc_ref(v_rhs_211_);
lean_dec_ref(v_c_204_);
lean_inc(v_toBind_208_);
lean_inc(v_inst_207_);
lean_inc_ref(v_inst_206_);
v___f_212_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__1), 7, 6);
lean_closure_set(v___f_212_, 0, v_s_209_);
lean_closure_set(v___f_212_, 1, v_toPure_205_);
lean_closure_set(v___f_212_, 2, v_inst_206_);
lean_closure_set(v___f_212_, 3, v_inst_207_);
lean_closure_set(v___f_212_, 4, v_rhs_211_);
lean_closure_set(v___f_212_, 5, v_toBind_208_);
v___x_213_ = l_Lean_Grind_AC_Seq_denoteExpr___redArg(v_inst_206_, v_inst_207_, v_lhs_210_);
v___x_214_ = lean_apply_4(v_toBind_208_, lean_box(0), lean_box(0), v___x_213_, v___f_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg(lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_c_217_){
_start:
{
lean_object* v_toApplicative_218_; lean_object* v_toBind_219_; lean_object* v_toPure_220_; lean_object* v___f_221_; lean_object* v___x_222_; 
v_toApplicative_218_ = lean_ctor_get(v_inst_215_, 0);
v_toBind_219_ = lean_ctor_get(v_inst_215_, 1);
lean_inc(v_toBind_219_);
v_toPure_220_ = lean_ctor_get(v_toApplicative_218_, 1);
lean_inc(v_toPure_220_);
lean_inc(v_toBind_219_);
lean_inc(v_inst_216_);
v___f_221_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg___lam__2), 6, 5);
lean_closure_set(v___f_221_, 0, v_c_217_);
lean_closure_set(v___f_221_, 1, v_toPure_220_);
lean_closure_set(v___f_221_, 2, v_inst_215_);
lean_closure_set(v___f_221_, 3, v_inst_216_);
lean_closure_set(v___f_221_, 4, v_toBind_219_);
v___x_222_ = lean_apply_4(v_toBind_219_, lean_box(0), lean_box(0), v_inst_216_, v___f_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr(lean_object* v_M_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_c_226_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Grind_AC_DiseqCnstr_denoteExpr___redArg(v_inst_224_, v_inst_225_, v_c_226_);
return v___x_227_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_AC_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
}
#ifdef __cplusplus
}
#endif
