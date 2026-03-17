// Lean compiler output
// Module: Lean.Meta.ExprTraverse
// Imports: public import Lean.SubExpr
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
lean_object* l_Lean_Meta_mkLambdaFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushBindingBody(lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_SubExpr_Pos_pushBindingDomain(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushLetBody(lean_object*);
lean_object* l_Lean_Meta_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_SubExpr_Pos_pushLetValue(lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushLetVarType(lean_object*);
lean_object* l_Lean_Meta_mkLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_SubExpr_Pos_root;
lean_object* l_Lean_Expr_traverseAppWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
lean_object* l_Lean_SubExpr_Pos_pushProj(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(lean_object* v_visit_1_, lean_object* v_x_2_, lean_object* v___y_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_1(v_visit_1_, v___y_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed(lean_object* v_visit_5_, lean_object* v_x_6_, lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0(v_visit_5_, v_x_6_, v___y_7_);
lean_dec(v_x_6_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(lean_object* v_t_9_, lean_object* v_visit_10_, lean_object* v_e_11_){
_start:
{
lean_object* v___f_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___f_12_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_12_, 0, v_visit_10_);
v___x_13_ = l_Lean_SubExpr_Pos_root;
v___x_14_ = lean_apply_3(v_t_9_, v___f_12_, v___x_13_, v_e_11_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos(lean_object* v_M_15_, lean_object* v_t_16_, lean_object* v_visit_17_, lean_object* v_e_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v_t_16_, v_visit_17_, v_e_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2(lean_object* v_fvars_20_, lean_object* v_inst_21_, lean_object* v_body_22_){
_start:
{
uint8_t v___x_23_; uint8_t v___x_24_; uint8_t v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_23_ = 0;
v___x_24_ = 1;
v___x_25_ = 1;
v___x_26_ = lean_box(v___x_23_);
v___x_27_ = lean_box(v___x_24_);
v___x_28_ = lean_box(v___x_23_);
v___x_29_ = lean_box(v___x_24_);
v___x_30_ = lean_box(v___x_25_);
v___x_31_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLambdaFVars___boxed), 12, 7);
lean_closure_set(v___x_31_, 0, v_fvars_20_);
lean_closure_set(v___x_31_, 1, v_body_22_);
lean_closure_set(v___x_31_, 2, v___x_26_);
lean_closure_set(v___x_31_, 3, v___x_27_);
lean_closure_set(v___x_31_, 4, v___x_28_);
lean_closure_set(v___x_31_, 5, v___x_29_);
lean_closure_set(v___x_31_, 6, v___x_30_);
v___x_32_ = lean_apply_2(v_inst_21_, lean_box(0), v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_binderName_35_, uint8_t v_binderInfo_36_, lean_object* v___f_37_, lean_object* v_d_38_){
_start:
{
uint8_t v___x_39_; lean_object* v___x_40_; 
v___x_39_ = 0;
v___x_40_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_33_, v_inst_34_, v_binderName_35_, v_binderInfo_36_, v_d_38_, v___f_37_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed(lean_object* v_inst_41_, lean_object* v_inst_42_, lean_object* v_binderName_43_, lean_object* v_binderInfo_44_, lean_object* v___f_45_, lean_object* v_d_46_){
_start:
{
uint8_t v_binderInfo_120__boxed_47_; lean_object* v_res_48_; 
v_binderInfo_120__boxed_47_ = lean_unbox(v_binderInfo_44_);
v_res_48_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(v_inst_41_, v_inst_42_, v_binderName_43_, v_binderInfo_120__boxed_47_, v___f_45_, v_d_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed(lean_object* v_fvars_49_, lean_object* v_p_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_f_54_, lean_object* v_body_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(v_fvars_49_, v_p_50_, v_inst_51_, v_inst_52_, v_inst_53_, v_f_54_, v_body_55_, v_x_56_);
lean_dec(v_p_50_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(lean_object* v_inst_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_f_61_, lean_object* v_fvars_62_, lean_object* v_p_63_, lean_object* v_a_64_){
_start:
{
if (lean_obj_tag(v_a_64_) == 6)
{
lean_object* v_toBind_65_; lean_object* v_binderName_66_; lean_object* v_binderType_67_; lean_object* v_body_68_; uint8_t v_binderInfo_69_; lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___f_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_toBind_65_ = lean_ctor_get(v_inst_58_, 1);
lean_inc(v_toBind_65_);
v_binderName_66_ = lean_ctor_get(v_a_64_, 0);
lean_inc(v_binderName_66_);
v_binderType_67_ = lean_ctor_get(v_a_64_, 1);
lean_inc_ref(v_binderType_67_);
v_body_68_ = lean_ctor_get(v_a_64_, 2);
lean_inc_ref(v_body_68_);
v_binderInfo_69_ = lean_ctor_get_uint8(v_a_64_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_64_);
lean_inc(v_f_61_);
lean_inc_ref(v_inst_60_);
lean_inc_ref(v_inst_58_);
lean_inc(v_p_63_);
lean_inc_ref(v_fvars_62_);
v___f_70_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_70_, 0, v_fvars_62_);
lean_closure_set(v___f_70_, 1, v_p_63_);
lean_closure_set(v___f_70_, 2, v_inst_58_);
lean_closure_set(v___f_70_, 3, v_inst_59_);
lean_closure_set(v___f_70_, 4, v_inst_60_);
lean_closure_set(v___f_70_, 5, v_f_61_);
lean_closure_set(v___f_70_, 6, v_body_68_);
v___x_71_ = lean_box(v_binderInfo_69_);
v___f_72_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_72_, 0, v_inst_60_);
lean_closure_set(v___f_72_, 1, v_inst_58_);
lean_closure_set(v___f_72_, 2, v_binderName_66_);
lean_closure_set(v___f_72_, 3, v___x_71_);
lean_closure_set(v___f_72_, 4, v___f_70_);
v___x_73_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_63_);
lean_dec(v_p_63_);
v___x_74_ = lean_expr_instantiate_rev(v_binderType_67_, v_fvars_62_);
lean_dec_ref(v_fvars_62_);
lean_dec_ref(v_binderType_67_);
v___x_75_ = lean_apply_2(v_f_61_, v___x_73_, v___x_74_);
v___x_76_ = lean_apply_4(v_toBind_65_, lean_box(0), lean_box(0), v___x_75_, v___f_72_);
return v___x_76_;
}
else
{
lean_object* v_toBind_77_; lean_object* v___f_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec_ref(v_inst_60_);
v_toBind_77_ = lean_ctor_get(v_inst_58_, 1);
lean_inc(v_toBind_77_);
lean_dec_ref(v_inst_58_);
lean_inc_ref(v_fvars_62_);
v___f_78_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2), 3, 2);
lean_closure_set(v___f_78_, 0, v_fvars_62_);
lean_closure_set(v___f_78_, 1, v_inst_59_);
v___x_79_ = lean_expr_instantiate_rev(v_a_64_, v_fvars_62_);
lean_dec_ref(v_fvars_62_);
lean_dec_ref(v_a_64_);
v___x_80_ = lean_apply_2(v_f_61_, v_p_63_, v___x_79_);
v___x_81_ = lean_apply_4(v_toBind_77_, lean_box(0), lean_box(0), v___x_80_, v___f_78_);
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(lean_object* v_fvars_82_, lean_object* v_p_83_, lean_object* v_inst_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_f_87_, lean_object* v_body_88_, lean_object* v_x_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_array_push(v_fvars_82_, v_x_89_);
v___x_91_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_83_);
v___x_92_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(v_inst_84_, v_inst_85_, v_inst_86_, v_f_87_, v___x_90_, v___x_91_, v_body_88_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit(lean_object* v_M_93_, lean_object* v_inst_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_f_97_, lean_object* v_fvars_98_, lean_object* v_p_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(v_inst_94_, v_inst_95_, v_inst_96_, v_f_97_, v_fvars_98_, v_p_99_, v_a_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos___redArg(lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_f_107_, lean_object* v_p_108_, lean_object* v_e_109_){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_110_ = ((lean_object*)(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0));
v___x_111_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(v_inst_104_, v_inst_105_, v_inst_106_, v_f_107_, v___x_110_, v_p_108_, v_e_109_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos(lean_object* v_M_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_f_116_, lean_object* v_p_117_, lean_object* v_e_118_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_traverseLambdaWithPos___redArg(v_inst_113_, v_inst_114_, v_inst_115_, v_f_116_, v_p_117_, v_e_118_);
return v___x_119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(lean_object* v_fvars_120_, lean_object* v_inst_121_, lean_object* v_body_122_){
_start:
{
uint8_t v___x_123_; uint8_t v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_123_ = 0;
v___x_124_ = 1;
v___x_125_ = 1;
v___x_126_ = lean_box(v___x_123_);
v___x_127_ = lean_box(v___x_124_);
v___x_128_ = lean_box(v___x_124_);
v___x_129_ = lean_box(v___x_125_);
v___x_130_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_130_, 0, v_fvars_120_);
lean_closure_set(v___x_130_, 1, v_body_122_);
lean_closure_set(v___x_130_, 2, v___x_126_);
lean_closure_set(v___x_130_, 3, v___x_127_);
lean_closure_set(v___x_130_, 4, v___x_128_);
lean_closure_set(v___x_130_, 5, v___x_129_);
v___x_131_ = lean_apply_2(v_inst_121_, lean_box(0), v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed(lean_object* v_fvars_132_, lean_object* v_p_133_, lean_object* v_inst_134_, lean_object* v_inst_135_, lean_object* v_inst_136_, lean_object* v_f_137_, lean_object* v_body_138_, lean_object* v_x_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(v_fvars_132_, v_p_133_, v_inst_134_, v_inst_135_, v_inst_136_, v_f_137_, v_body_138_, v_x_139_);
lean_dec(v_p_133_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_inst_143_, lean_object* v_f_144_, lean_object* v_fvars_145_, lean_object* v_p_146_, lean_object* v_a_147_){
_start:
{
if (lean_obj_tag(v_a_147_) == 7)
{
lean_object* v_toBind_148_; lean_object* v_binderName_149_; lean_object* v_binderType_150_; lean_object* v_body_151_; uint8_t v_binderInfo_152_; lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___f_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v_toBind_148_ = lean_ctor_get(v_inst_141_, 1);
lean_inc(v_toBind_148_);
v_binderName_149_ = lean_ctor_get(v_a_147_, 0);
lean_inc(v_binderName_149_);
v_binderType_150_ = lean_ctor_get(v_a_147_, 1);
lean_inc_ref(v_binderType_150_);
v_body_151_ = lean_ctor_get(v_a_147_, 2);
lean_inc_ref(v_body_151_);
v_binderInfo_152_ = lean_ctor_get_uint8(v_a_147_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_147_);
lean_inc(v_f_144_);
lean_inc_ref(v_inst_143_);
lean_inc_ref(v_inst_141_);
lean_inc(v_p_146_);
lean_inc_ref(v_fvars_145_);
v___f_153_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_153_, 0, v_fvars_145_);
lean_closure_set(v___f_153_, 1, v_p_146_);
lean_closure_set(v___f_153_, 2, v_inst_141_);
lean_closure_set(v___f_153_, 3, v_inst_142_);
lean_closure_set(v___f_153_, 4, v_inst_143_);
lean_closure_set(v___f_153_, 5, v_f_144_);
lean_closure_set(v___f_153_, 6, v_body_151_);
v___x_154_ = lean_box(v_binderInfo_152_);
v___f_155_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_155_, 0, v_inst_143_);
lean_closure_set(v___f_155_, 1, v_inst_141_);
lean_closure_set(v___f_155_, 2, v_binderName_149_);
lean_closure_set(v___f_155_, 3, v___x_154_);
lean_closure_set(v___f_155_, 4, v___f_153_);
v___x_156_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_146_);
lean_dec(v_p_146_);
v___x_157_ = lean_expr_instantiate_rev(v_binderType_150_, v_fvars_145_);
lean_dec_ref(v_fvars_145_);
lean_dec_ref(v_binderType_150_);
v___x_158_ = lean_apply_2(v_f_144_, v___x_156_, v___x_157_);
v___x_159_ = lean_apply_4(v_toBind_148_, lean_box(0), lean_box(0), v___x_158_, v___f_155_);
return v___x_159_;
}
else
{
lean_object* v_toBind_160_; lean_object* v___f_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec_ref(v_inst_143_);
v_toBind_160_ = lean_ctor_get(v_inst_141_, 1);
lean_inc(v_toBind_160_);
lean_dec_ref(v_inst_141_);
lean_inc_ref(v_fvars_145_);
v___f_161_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2), 3, 2);
lean_closure_set(v___f_161_, 0, v_fvars_145_);
lean_closure_set(v___f_161_, 1, v_inst_142_);
v___x_162_ = lean_expr_instantiate_rev(v_a_147_, v_fvars_145_);
lean_dec_ref(v_fvars_145_);
lean_dec_ref(v_a_147_);
v___x_163_ = lean_apply_2(v_f_144_, v_p_146_, v___x_162_);
v___x_164_ = lean_apply_4(v_toBind_160_, lean_box(0), lean_box(0), v___x_163_, v___f_161_);
return v___x_164_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(lean_object* v_fvars_165_, lean_object* v_p_166_, lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_inst_169_, lean_object* v_f_170_, lean_object* v_body_171_, lean_object* v_x_172_){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_array_push(v_fvars_165_, v_x_172_);
v___x_174_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_166_);
v___x_175_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_167_, v_inst_168_, v_inst_169_, v_f_170_, v___x_173_, v___x_174_, v_body_171_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(lean_object* v_M_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_f_180_, lean_object* v_fvars_181_, lean_object* v_p_182_, lean_object* v_a_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_177_, v_inst_178_, v_inst_179_, v_f_180_, v_fvars_181_, v_p_182_, v_a_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos___redArg(lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_f_188_, lean_object* v_p_189_, lean_object* v_e_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0));
v___x_192_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_185_, v_inst_186_, v_inst_187_, v_f_188_, v___x_191_, v_p_189_, v_e_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos(lean_object* v_M_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_f_197_, lean_object* v_p_198_, lean_object* v_e_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_Meta_traverseForallWithPos___redArg(v_inst_194_, v_inst_195_, v_inst_196_, v_f_197_, v_p_198_, v_e_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1(lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_declName_203_, lean_object* v_type_204_, lean_object* v___f_205_, lean_object* v_value_206_){
_start:
{
uint8_t v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; 
v___x_207_ = 0;
v___x_208_ = 0;
v___x_209_ = l_Lean_Meta_withLetDecl___redArg(v_inst_201_, v_inst_202_, v_declName_203_, v_type_204_, v_value_206_, v___f_205_, v___x_207_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_declName_212_, lean_object* v___f_213_, lean_object* v_p_214_, lean_object* v_value_215_, lean_object* v_fvars_216_, lean_object* v_f_217_, lean_object* v_toBind_218_, lean_object* v_type_219_){
_start:
{
lean_object* v___f_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___f_220_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1), 6, 5);
lean_closure_set(v___f_220_, 0, v_inst_210_);
lean_closure_set(v___f_220_, 1, v_inst_211_);
lean_closure_set(v___f_220_, 2, v_declName_212_);
lean_closure_set(v___f_220_, 3, v_type_219_);
lean_closure_set(v___f_220_, 4, v___f_213_);
v___x_221_ = l_Lean_SubExpr_Pos_pushLetValue(v_p_214_);
v___x_222_ = lean_expr_instantiate_rev(v_value_215_, v_fvars_216_);
v___x_223_ = lean_apply_2(v_f_217_, v___x_221_, v___x_222_);
v___x_224_ = lean_apply_4(v_toBind_218_, lean_box(0), lean_box(0), v___x_223_, v___f_220_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed(lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_declName_227_, lean_object* v___f_228_, lean_object* v_p_229_, lean_object* v_value_230_, lean_object* v_fvars_231_, lean_object* v_f_232_, lean_object* v_toBind_233_, lean_object* v_type_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(v_inst_225_, v_inst_226_, v_declName_227_, v___f_228_, v_p_229_, v_value_230_, v_fvars_231_, v_f_232_, v_toBind_233_, v_type_234_);
lean_dec_ref(v_fvars_231_);
lean_dec_ref(v_value_230_);
lean_dec(v_p_229_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3(lean_object* v_fvars_236_, lean_object* v_inst_237_, lean_object* v_body_238_){
_start:
{
uint8_t v___x_239_; uint8_t v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_239_ = 0;
v___x_240_ = 1;
v___x_241_ = 1;
v___x_242_ = lean_box(v___x_239_);
v___x_243_ = lean_box(v___x_240_);
v___x_244_ = lean_box(v___x_241_);
v___x_245_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_245_, 0, v_fvars_236_);
lean_closure_set(v___x_245_, 1, v_body_238_);
lean_closure_set(v___x_245_, 2, v___x_242_);
lean_closure_set(v___x_245_, 3, v___x_243_);
lean_closure_set(v___x_245_, 4, v___x_244_);
v___x_246_ = lean_apply_2(v_inst_237_, lean_box(0), v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed(lean_object* v_fvars_247_, lean_object* v_p_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_f_252_, lean_object* v_body_253_, lean_object* v_x_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(v_fvars_247_, v_p_248_, v_inst_249_, v_inst_250_, v_inst_251_, v_f_252_, v_body_253_, v_x_254_);
lean_dec(v_p_248_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_inst_258_, lean_object* v_f_259_, lean_object* v_fvars_260_, lean_object* v_p_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 8)
{
lean_object* v_toBind_263_; lean_object* v_declName_264_; lean_object* v_type_265_; lean_object* v_value_266_; lean_object* v_body_267_; lean_object* v___f_268_; lean_object* v___f_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_toBind_263_ = lean_ctor_get(v_inst_256_, 1);
lean_inc(v_toBind_263_);
v_declName_264_ = lean_ctor_get(v_x_262_, 0);
lean_inc(v_declName_264_);
v_type_265_ = lean_ctor_get(v_x_262_, 1);
lean_inc_ref(v_type_265_);
v_value_266_ = lean_ctor_get(v_x_262_, 2);
lean_inc_ref(v_value_266_);
v_body_267_ = lean_ctor_get(v_x_262_, 3);
lean_inc_ref(v_body_267_);
lean_dec_ref(v_x_262_);
lean_inc(v_f_259_);
lean_inc_ref(v_inst_258_);
lean_inc_ref(v_inst_256_);
lean_inc(v_p_261_);
lean_inc_ref(v_fvars_260_);
v___f_268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_268_, 0, v_fvars_260_);
lean_closure_set(v___f_268_, 1, v_p_261_);
lean_closure_set(v___f_268_, 2, v_inst_256_);
lean_closure_set(v___f_268_, 3, v_inst_257_);
lean_closure_set(v___f_268_, 4, v_inst_258_);
lean_closure_set(v___f_268_, 5, v_f_259_);
lean_closure_set(v___f_268_, 6, v_body_267_);
lean_inc(v_toBind_263_);
lean_inc(v_f_259_);
lean_inc_ref(v_fvars_260_);
lean_inc(v_p_261_);
v___f_269_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_269_, 0, v_inst_258_);
lean_closure_set(v___f_269_, 1, v_inst_256_);
lean_closure_set(v___f_269_, 2, v_declName_264_);
lean_closure_set(v___f_269_, 3, v___f_268_);
lean_closure_set(v___f_269_, 4, v_p_261_);
lean_closure_set(v___f_269_, 5, v_value_266_);
lean_closure_set(v___f_269_, 6, v_fvars_260_);
lean_closure_set(v___f_269_, 7, v_f_259_);
lean_closure_set(v___f_269_, 8, v_toBind_263_);
v___x_270_ = l_Lean_SubExpr_Pos_pushLetVarType(v_p_261_);
lean_dec(v_p_261_);
v___x_271_ = lean_expr_instantiate_rev(v_type_265_, v_fvars_260_);
lean_dec_ref(v_fvars_260_);
lean_dec_ref(v_type_265_);
v___x_272_ = lean_apply_2(v_f_259_, v___x_270_, v___x_271_);
v___x_273_ = lean_apply_4(v_toBind_263_, lean_box(0), lean_box(0), v___x_272_, v___f_269_);
return v___x_273_;
}
else
{
lean_object* v_toBind_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec_ref(v_inst_258_);
v_toBind_274_ = lean_ctor_get(v_inst_256_, 1);
lean_inc(v_toBind_274_);
lean_dec_ref(v_inst_256_);
lean_inc_ref(v_fvars_260_);
v___f_275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3), 3, 2);
lean_closure_set(v___f_275_, 0, v_fvars_260_);
lean_closure_set(v___f_275_, 1, v_inst_257_);
v___x_276_ = lean_expr_instantiate_rev(v_x_262_, v_fvars_260_);
lean_dec_ref(v_fvars_260_);
lean_dec_ref(v_x_262_);
v___x_277_ = lean_apply_2(v_f_259_, v_p_261_, v___x_276_);
v___x_278_ = lean_apply_4(v_toBind_274_, lean_box(0), lean_box(0), v___x_277_, v___f_275_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(lean_object* v_fvars_279_, lean_object* v_p_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_f_284_, lean_object* v_body_285_, lean_object* v_x_286_){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_array_push(v_fvars_279_, v_x_286_);
v___x_288_ = l_Lean_SubExpr_Pos_pushLetBody(v_p_280_);
v___x_289_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(v_inst_281_, v_inst_282_, v_inst_283_, v_f_284_, v___x_287_, v___x_288_, v_body_285_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit(lean_object* v_M_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_f_294_, lean_object* v_fvars_295_, lean_object* v_p_296_, lean_object* v_x_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(v_inst_291_, v_inst_292_, v_inst_293_, v_f_294_, v_fvars_295_, v_p_296_, v_x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos___redArg(lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_f_302_, lean_object* v_p_303_, lean_object* v_e_304_){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_305_ = ((lean_object*)(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0));
v___x_306_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(v_inst_299_, v_inst_300_, v_inst_301_, v_f_302_, v___x_305_, v_p_303_, v_e_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos(lean_object* v_M_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_f_311_, lean_object* v_p_312_, lean_object* v_e_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Meta_traverseLetWithPos___redArg(v_inst_308_, v_inst_309_, v_inst_310_, v_f_311_, v_p_312_, v_e_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos___redArg(lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_visit_318_, lean_object* v_p_319_, lean_object* v_e_320_){
_start:
{
switch(lean_obj_tag(v_e_320_))
{
case 7:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Meta_traverseForallWithPos___redArg(v_inst_315_, v_inst_316_, v_inst_317_, v_visit_318_, v_p_319_, v_e_320_);
return v___x_321_;
}
case 6:
{
lean_object* v___x_322_; 
v___x_322_ = l_Lean_Meta_traverseLambdaWithPos___redArg(v_inst_315_, v_inst_316_, v_inst_317_, v_visit_318_, v_p_319_, v_e_320_);
return v___x_322_;
}
case 8:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Meta_traverseLetWithPos___redArg(v_inst_315_, v_inst_316_, v_inst_317_, v_visit_318_, v_p_319_, v_e_320_);
return v___x_323_;
}
case 5:
{
lean_object* v___x_324_; 
lean_dec_ref(v_inst_317_);
lean_dec(v_inst_316_);
v___x_324_ = l_Lean_Expr_traverseAppWithPos___redArg(v_inst_315_, v_visit_318_, v_p_319_, v_e_320_);
return v___x_324_;
}
case 10:
{
lean_object* v_toApplicative_325_; lean_object* v_toFunctor_326_; lean_object* v_expr_327_; lean_object* v_map_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v_toApplicative_325_ = lean_ctor_get(v_inst_315_, 0);
lean_inc_ref(v_toApplicative_325_);
lean_dec_ref(v_inst_317_);
lean_dec(v_inst_316_);
lean_dec_ref(v_inst_315_);
v_toFunctor_326_ = lean_ctor_get(v_toApplicative_325_, 0);
lean_inc_ref(v_toFunctor_326_);
lean_dec_ref(v_toApplicative_325_);
v_expr_327_ = lean_ctor_get(v_e_320_, 1);
lean_inc_ref(v_expr_327_);
v_map_328_ = lean_ctor_get(v_toFunctor_326_, 0);
lean_inc(v_map_328_);
lean_dec_ref(v_toFunctor_326_);
v___x_329_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_329_, 0, v_e_320_);
v___x_330_ = lean_apply_2(v_visit_318_, v_p_319_, v_expr_327_);
v___x_331_ = lean_apply_4(v_map_328_, lean_box(0), lean_box(0), v___x_329_, v___x_330_);
return v___x_331_;
}
case 11:
{
lean_object* v_toApplicative_332_; lean_object* v_toFunctor_333_; lean_object* v_struct_334_; lean_object* v_map_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_toApplicative_332_ = lean_ctor_get(v_inst_315_, 0);
lean_inc_ref(v_toApplicative_332_);
lean_dec_ref(v_inst_317_);
lean_dec(v_inst_316_);
lean_dec_ref(v_inst_315_);
v_toFunctor_333_ = lean_ctor_get(v_toApplicative_332_, 0);
lean_inc_ref(v_toFunctor_333_);
lean_dec_ref(v_toApplicative_332_);
v_struct_334_ = lean_ctor_get(v_e_320_, 2);
lean_inc_ref(v_struct_334_);
v_map_335_ = lean_ctor_get(v_toFunctor_333_, 0);
lean_inc(v_map_335_);
lean_dec_ref(v_toFunctor_333_);
v___x_336_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_336_, 0, v_e_320_);
v___x_337_ = l_Lean_SubExpr_Pos_pushProj(v_p_319_);
lean_dec(v_p_319_);
v___x_338_ = lean_apply_2(v_visit_318_, v___x_337_, v_struct_334_);
v___x_339_ = lean_apply_4(v_map_335_, lean_box(0), lean_box(0), v___x_336_, v___x_338_);
return v___x_339_;
}
default: 
{
lean_object* v_toApplicative_340_; lean_object* v_toPure_341_; lean_object* v___x_342_; 
v_toApplicative_340_ = lean_ctor_get(v_inst_315_, 0);
lean_inc_ref(v_toApplicative_340_);
lean_dec(v_p_319_);
lean_dec(v_visit_318_);
lean_dec_ref(v_inst_317_);
lean_dec(v_inst_316_);
lean_dec_ref(v_inst_315_);
v_toPure_341_ = lean_ctor_get(v_toApplicative_340_, 1);
lean_inc(v_toPure_341_);
lean_dec_ref(v_toApplicative_340_);
v___x_342_ = lean_apply_2(v_toPure_341_, lean_box(0), v_e_320_);
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos(lean_object* v_M_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_visit_347_, lean_object* v_p_348_, lean_object* v_e_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l_Lean_Meta_traverseChildrenWithPos___redArg(v_inst_344_, v_inst_345_, v_inst_346_, v_visit_347_, v_p_348_, v_e_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda___redArg(lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_visit_354_, lean_object* v_e_355_){
_start:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_356_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseLambdaWithPos), 7, 4);
lean_closure_set(v___x_356_, 0, lean_box(0));
lean_closure_set(v___x_356_, 1, v_inst_351_);
lean_closure_set(v___x_356_, 2, v_inst_352_);
lean_closure_set(v___x_356_, 3, v_inst_353_);
v___x_357_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_356_, v_visit_354_, v_e_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda(lean_object* v_M_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_visit_362_, lean_object* v_e_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = l_Lean_Meta_traverseLambda___redArg(v_inst_359_, v_inst_360_, v_inst_361_, v_visit_362_, v_e_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall___redArg(lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_visit_368_, lean_object* v_e_369_){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseForallWithPos), 7, 4);
lean_closure_set(v___x_370_, 0, lean_box(0));
lean_closure_set(v___x_370_, 1, v_inst_365_);
lean_closure_set(v___x_370_, 2, v_inst_366_);
lean_closure_set(v___x_370_, 3, v_inst_367_);
v___x_371_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_370_, v_visit_368_, v_e_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall(lean_object* v_M_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_visit_376_, lean_object* v_e_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Lean_Meta_traverseForall___redArg(v_inst_373_, v_inst_374_, v_inst_375_, v_visit_376_, v_e_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet___redArg(lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_visit_382_, lean_object* v_e_383_){
_start:
{
lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_384_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseLetWithPos), 7, 4);
lean_closure_set(v___x_384_, 0, lean_box(0));
lean_closure_set(v___x_384_, 1, v_inst_379_);
lean_closure_set(v___x_384_, 2, v_inst_380_);
lean_closure_set(v___x_384_, 3, v_inst_381_);
v___x_385_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_384_, v_visit_382_, v_e_383_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet(lean_object* v_M_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_visit_390_, lean_object* v_e_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Meta_traverseLet___redArg(v_inst_387_, v_inst_388_, v_inst_389_, v_visit_390_, v_e_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren___redArg(lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_visit_396_, lean_object* v_e_397_){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_398_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseChildrenWithPos), 7, 4);
lean_closure_set(v___x_398_, 0, lean_box(0));
lean_closure_set(v___x_398_, 1, v_inst_393_);
lean_closure_set(v___x_398_, 2, v_inst_394_);
lean_closure_set(v___x_398_, 3, v_inst_395_);
v___x_399_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_398_, v_visit_396_, v_e_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren(lean_object* v_M_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_visit_404_, lean_object* v_e_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Lean_Meta_traverseChildren___redArg(v_inst_401_, v_inst_402_, v_inst_403_, v_visit_404_, v_e_405_);
return v___x_406_;
}
}
lean_object* runtime_initialize_Lean_SubExpr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ExprTraverse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_ExprTraverse(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_SubExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_ExprTraverse(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_SubExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_ExprTraverse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_ExprTraverse(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_ExprTraverse(builtin);
}
#ifdef __cplusplus
}
#endif
