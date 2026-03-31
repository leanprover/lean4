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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_ref(v_fvars_120_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2___boxed(lean_object* v_fvars_132_, lean_object* v_inst_133_, lean_object* v_body_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(v_fvars_132_, v_inst_133_, v_body_134_);
lean_dec_ref(v_fvars_132_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed(lean_object* v_fvars_136_, lean_object* v_p_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_f_141_, lean_object* v_body_142_, lean_object* v_x_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(v_fvars_136_, v_p_137_, v_inst_138_, v_inst_139_, v_inst_140_, v_f_141_, v_body_142_, v_x_143_);
lean_dec(v_p_137_);
lean_dec_ref(v_fvars_136_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(lean_object* v_inst_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_f_148_, lean_object* v_fvars_149_, lean_object* v_p_150_, lean_object* v_a_151_){
_start:
{
if (lean_obj_tag(v_a_151_) == 7)
{
lean_object* v_toBind_152_; lean_object* v_binderName_153_; lean_object* v_binderType_154_; lean_object* v_body_155_; uint8_t v_binderInfo_156_; lean_object* v___f_157_; lean_object* v___x_158_; lean_object* v___f_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_toBind_152_ = lean_ctor_get(v_inst_145_, 1);
lean_inc(v_toBind_152_);
v_binderName_153_ = lean_ctor_get(v_a_151_, 0);
lean_inc(v_binderName_153_);
v_binderType_154_ = lean_ctor_get(v_a_151_, 1);
lean_inc_ref(v_binderType_154_);
v_body_155_ = lean_ctor_get(v_a_151_, 2);
lean_inc_ref(v_body_155_);
v_binderInfo_156_ = lean_ctor_get_uint8(v_a_151_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_151_);
lean_inc(v_f_148_);
lean_inc_ref(v_inst_147_);
lean_inc_ref(v_inst_145_);
lean_inc(v_p_150_);
lean_inc_ref(v_fvars_149_);
v___f_157_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_157_, 0, v_fvars_149_);
lean_closure_set(v___f_157_, 1, v_p_150_);
lean_closure_set(v___f_157_, 2, v_inst_145_);
lean_closure_set(v___f_157_, 3, v_inst_146_);
lean_closure_set(v___f_157_, 4, v_inst_147_);
lean_closure_set(v___f_157_, 5, v_f_148_);
lean_closure_set(v___f_157_, 6, v_body_155_);
v___x_158_ = lean_box(v_binderInfo_156_);
v___f_159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_159_, 0, v_inst_147_);
lean_closure_set(v___f_159_, 1, v_inst_145_);
lean_closure_set(v___f_159_, 2, v_binderName_153_);
lean_closure_set(v___f_159_, 3, v___x_158_);
lean_closure_set(v___f_159_, 4, v___f_157_);
v___x_160_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_150_);
lean_dec(v_p_150_);
v___x_161_ = lean_expr_instantiate_rev(v_binderType_154_, v_fvars_149_);
lean_dec_ref(v_binderType_154_);
v___x_162_ = lean_apply_2(v_f_148_, v___x_160_, v___x_161_);
v___x_163_ = lean_apply_4(v_toBind_152_, lean_box(0), lean_box(0), v___x_162_, v___f_159_);
return v___x_163_;
}
else
{
lean_object* v_toBind_164_; lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec_ref(v_inst_147_);
v_toBind_164_ = lean_ctor_get(v_inst_145_, 1);
lean_inc(v_toBind_164_);
lean_dec_ref(v_inst_145_);
lean_inc_ref(v_fvars_149_);
v___f_165_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_165_, 0, v_fvars_149_);
lean_closure_set(v___f_165_, 1, v_inst_146_);
v___x_166_ = lean_expr_instantiate_rev(v_a_151_, v_fvars_149_);
lean_dec_ref(v_a_151_);
v___x_167_ = lean_apply_2(v_f_148_, v_p_150_, v___x_166_);
v___x_168_ = lean_apply_4(v_toBind_164_, lean_box(0), lean_box(0), v___x_167_, v___f_165_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(lean_object* v_fvars_169_, lean_object* v_p_170_, lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_f_174_, lean_object* v_body_175_, lean_object* v_x_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc_ref(v_fvars_169_);
v___x_177_ = lean_array_push(v_fvars_169_, v_x_176_);
v___x_178_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_170_);
v___x_179_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_171_, v_inst_172_, v_inst_173_, v_f_174_, v___x_177_, v___x_178_, v_body_175_);
lean_dec_ref(v___x_177_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___boxed(lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_f_183_, lean_object* v_fvars_184_, lean_object* v_p_185_, lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_180_, v_inst_181_, v_inst_182_, v_f_183_, v_fvars_184_, v_p_185_, v_a_186_);
lean_dec_ref(v_fvars_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(lean_object* v_M_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_f_192_, lean_object* v_fvars_193_, lean_object* v_p_194_, lean_object* v_a_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_189_, v_inst_190_, v_inst_191_, v_f_192_, v_fvars_193_, v_p_194_, v_a_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___boxed(lean_object* v_M_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_f_201_, lean_object* v_fvars_202_, lean_object* v_p_203_, lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(v_M_197_, v_inst_198_, v_inst_199_, v_inst_200_, v_f_201_, v_fvars_202_, v_p_203_, v_a_204_);
lean_dec_ref(v_fvars_202_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos___redArg(lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_f_209_, lean_object* v_p_210_, lean_object* v_e_211_){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = ((lean_object*)(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0));
v___x_213_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_206_, v_inst_207_, v_inst_208_, v_f_209_, v___x_212_, v_p_210_, v_e_211_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos(lean_object* v_M_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_f_218_, lean_object* v_p_219_, lean_object* v_e_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = l_Lean_Meta_traverseForallWithPos___redArg(v_inst_215_, v_inst_216_, v_inst_217_, v_f_218_, v_p_219_, v_e_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1(lean_object* v_inst_222_, lean_object* v_inst_223_, lean_object* v_declName_224_, lean_object* v_type_225_, lean_object* v___f_226_, lean_object* v_value_227_){
_start:
{
uint8_t v___x_228_; uint8_t v___x_229_; lean_object* v___x_230_; 
v___x_228_ = 0;
v___x_229_ = 0;
v___x_230_ = l_Lean_Meta_withLetDecl___redArg(v_inst_222_, v_inst_223_, v_declName_224_, v_type_225_, v_value_227_, v___f_226_, v___x_228_, v___x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(lean_object* v_inst_231_, lean_object* v_inst_232_, lean_object* v_declName_233_, lean_object* v___f_234_, lean_object* v_p_235_, lean_object* v_value_236_, lean_object* v_fvars_237_, lean_object* v_f_238_, lean_object* v_toBind_239_, lean_object* v_type_240_){
_start:
{
lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___f_241_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1), 6, 5);
lean_closure_set(v___f_241_, 0, v_inst_231_);
lean_closure_set(v___f_241_, 1, v_inst_232_);
lean_closure_set(v___f_241_, 2, v_declName_233_);
lean_closure_set(v___f_241_, 3, v_type_240_);
lean_closure_set(v___f_241_, 4, v___f_234_);
v___x_242_ = l_Lean_SubExpr_Pos_pushLetValue(v_p_235_);
v___x_243_ = lean_expr_instantiate_rev(v_value_236_, v_fvars_237_);
v___x_244_ = lean_apply_2(v_f_238_, v___x_242_, v___x_243_);
v___x_245_ = lean_apply_4(v_toBind_239_, lean_box(0), lean_box(0), v___x_244_, v___f_241_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed(lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_declName_248_, lean_object* v___f_249_, lean_object* v_p_250_, lean_object* v_value_251_, lean_object* v_fvars_252_, lean_object* v_f_253_, lean_object* v_toBind_254_, lean_object* v_type_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(v_inst_246_, v_inst_247_, v_declName_248_, v___f_249_, v_p_250_, v_value_251_, v_fvars_252_, v_f_253_, v_toBind_254_, v_type_255_);
lean_dec_ref(v_fvars_252_);
lean_dec_ref(v_value_251_);
lean_dec(v_p_250_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3(lean_object* v_fvars_257_, lean_object* v_inst_258_, lean_object* v_body_259_){
_start:
{
uint8_t v___x_260_; uint8_t v___x_261_; uint8_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_260_ = 0;
v___x_261_ = 1;
v___x_262_ = 1;
v___x_263_ = lean_box(v___x_260_);
v___x_264_ = lean_box(v___x_261_);
v___x_265_ = lean_box(v___x_262_);
v___x_266_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_266_, 0, v_fvars_257_);
lean_closure_set(v___x_266_, 1, v_body_259_);
lean_closure_set(v___x_266_, 2, v___x_263_);
lean_closure_set(v___x_266_, 3, v___x_264_);
lean_closure_set(v___x_266_, 4, v___x_265_);
v___x_267_ = lean_apply_2(v_inst_258_, lean_box(0), v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed(lean_object* v_fvars_268_, lean_object* v_p_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_f_273_, lean_object* v_body_274_, lean_object* v_x_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(v_fvars_268_, v_p_269_, v_inst_270_, v_inst_271_, v_inst_272_, v_f_273_, v_body_274_, v_x_275_);
lean_dec(v_p_269_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_f_280_, lean_object* v_fvars_281_, lean_object* v_p_282_, lean_object* v_x_283_){
_start:
{
if (lean_obj_tag(v_x_283_) == 8)
{
lean_object* v_toBind_284_; lean_object* v_declName_285_; lean_object* v_type_286_; lean_object* v_value_287_; lean_object* v_body_288_; lean_object* v___f_289_; lean_object* v___f_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v_toBind_284_ = lean_ctor_get(v_inst_277_, 1);
lean_inc_n(v_toBind_284_, 2);
v_declName_285_ = lean_ctor_get(v_x_283_, 0);
lean_inc(v_declName_285_);
v_type_286_ = lean_ctor_get(v_x_283_, 1);
lean_inc_ref(v_type_286_);
v_value_287_ = lean_ctor_get(v_x_283_, 2);
lean_inc_ref(v_value_287_);
v_body_288_ = lean_ctor_get(v_x_283_, 3);
lean_inc_ref(v_body_288_);
lean_dec_ref(v_x_283_);
lean_inc_n(v_f_280_, 2);
lean_inc_ref(v_inst_279_);
lean_inc_ref(v_inst_277_);
lean_inc_n(v_p_282_, 2);
lean_inc_ref_n(v_fvars_281_, 2);
v___f_289_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_289_, 0, v_fvars_281_);
lean_closure_set(v___f_289_, 1, v_p_282_);
lean_closure_set(v___f_289_, 2, v_inst_277_);
lean_closure_set(v___f_289_, 3, v_inst_278_);
lean_closure_set(v___f_289_, 4, v_inst_279_);
lean_closure_set(v___f_289_, 5, v_f_280_);
lean_closure_set(v___f_289_, 6, v_body_288_);
v___f_290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_290_, 0, v_inst_279_);
lean_closure_set(v___f_290_, 1, v_inst_277_);
lean_closure_set(v___f_290_, 2, v_declName_285_);
lean_closure_set(v___f_290_, 3, v___f_289_);
lean_closure_set(v___f_290_, 4, v_p_282_);
lean_closure_set(v___f_290_, 5, v_value_287_);
lean_closure_set(v___f_290_, 6, v_fvars_281_);
lean_closure_set(v___f_290_, 7, v_f_280_);
lean_closure_set(v___f_290_, 8, v_toBind_284_);
v___x_291_ = l_Lean_SubExpr_Pos_pushLetVarType(v_p_282_);
lean_dec(v_p_282_);
v___x_292_ = lean_expr_instantiate_rev(v_type_286_, v_fvars_281_);
lean_dec_ref(v_fvars_281_);
lean_dec_ref(v_type_286_);
v___x_293_ = lean_apply_2(v_f_280_, v___x_291_, v___x_292_);
v___x_294_ = lean_apply_4(v_toBind_284_, lean_box(0), lean_box(0), v___x_293_, v___f_290_);
return v___x_294_;
}
else
{
lean_object* v_toBind_295_; lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec_ref(v_inst_279_);
v_toBind_295_ = lean_ctor_get(v_inst_277_, 1);
lean_inc(v_toBind_295_);
lean_dec_ref(v_inst_277_);
lean_inc_ref(v_fvars_281_);
v___f_296_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3), 3, 2);
lean_closure_set(v___f_296_, 0, v_fvars_281_);
lean_closure_set(v___f_296_, 1, v_inst_278_);
v___x_297_ = lean_expr_instantiate_rev(v_x_283_, v_fvars_281_);
lean_dec_ref(v_fvars_281_);
lean_dec_ref(v_x_283_);
v___x_298_ = lean_apply_2(v_f_280_, v_p_282_, v___x_297_);
v___x_299_ = lean_apply_4(v_toBind_295_, lean_box(0), lean_box(0), v___x_298_, v___f_296_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(lean_object* v_fvars_300_, lean_object* v_p_301_, lean_object* v_inst_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_f_305_, lean_object* v_body_306_, lean_object* v_x_307_){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_array_push(v_fvars_300_, v_x_307_);
v___x_309_ = l_Lean_SubExpr_Pos_pushLetBody(v_p_301_);
v___x_310_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(v_inst_302_, v_inst_303_, v_inst_304_, v_f_305_, v___x_308_, v___x_309_, v_body_306_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit(lean_object* v_M_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_f_315_, lean_object* v_fvars_316_, lean_object* v_p_317_, lean_object* v_x_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(v_inst_312_, v_inst_313_, v_inst_314_, v_f_315_, v_fvars_316_, v_p_317_, v_x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos___redArg(lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_f_323_, lean_object* v_p_324_, lean_object* v_e_325_){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = ((lean_object*)(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0));
v___x_327_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(v_inst_320_, v_inst_321_, v_inst_322_, v_f_323_, v___x_326_, v_p_324_, v_e_325_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos(lean_object* v_M_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_f_332_, lean_object* v_p_333_, lean_object* v_e_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = l_Lean_Meta_traverseLetWithPos___redArg(v_inst_329_, v_inst_330_, v_inst_331_, v_f_332_, v_p_333_, v_e_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos___redArg(lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_visit_339_, lean_object* v_p_340_, lean_object* v_e_341_){
_start:
{
switch(lean_obj_tag(v_e_341_))
{
case 7:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_Meta_traverseForallWithPos___redArg(v_inst_336_, v_inst_337_, v_inst_338_, v_visit_339_, v_p_340_, v_e_341_);
return v___x_342_;
}
case 6:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Meta_traverseLambdaWithPos___redArg(v_inst_336_, v_inst_337_, v_inst_338_, v_visit_339_, v_p_340_, v_e_341_);
return v___x_343_;
}
case 8:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Meta_traverseLetWithPos___redArg(v_inst_336_, v_inst_337_, v_inst_338_, v_visit_339_, v_p_340_, v_e_341_);
return v___x_344_;
}
case 5:
{
lean_object* v___x_345_; 
lean_dec_ref(v_inst_338_);
lean_dec(v_inst_337_);
v___x_345_ = l_Lean_Expr_traverseAppWithPos___redArg(v_inst_336_, v_visit_339_, v_p_340_, v_e_341_);
return v___x_345_;
}
case 10:
{
lean_object* v_toApplicative_346_; lean_object* v_toFunctor_347_; lean_object* v_expr_348_; lean_object* v_map_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_toApplicative_346_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_346_);
lean_dec_ref(v_inst_338_);
lean_dec(v_inst_337_);
lean_dec_ref(v_inst_336_);
v_toFunctor_347_ = lean_ctor_get(v_toApplicative_346_, 0);
lean_inc_ref(v_toFunctor_347_);
lean_dec_ref(v_toApplicative_346_);
v_expr_348_ = lean_ctor_get(v_e_341_, 1);
lean_inc_ref(v_expr_348_);
v_map_349_ = lean_ctor_get(v_toFunctor_347_, 0);
lean_inc(v_map_349_);
lean_dec_ref(v_toFunctor_347_);
v___x_350_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_350_, 0, v_e_341_);
v___x_351_ = lean_apply_2(v_visit_339_, v_p_340_, v_expr_348_);
v___x_352_ = lean_apply_4(v_map_349_, lean_box(0), lean_box(0), v___x_350_, v___x_351_);
return v___x_352_;
}
case 11:
{
lean_object* v_toApplicative_353_; lean_object* v_toFunctor_354_; lean_object* v_struct_355_; lean_object* v_map_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_toApplicative_353_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_353_);
lean_dec_ref(v_inst_338_);
lean_dec(v_inst_337_);
lean_dec_ref(v_inst_336_);
v_toFunctor_354_ = lean_ctor_get(v_toApplicative_353_, 0);
lean_inc_ref(v_toFunctor_354_);
lean_dec_ref(v_toApplicative_353_);
v_struct_355_ = lean_ctor_get(v_e_341_, 2);
lean_inc_ref(v_struct_355_);
v_map_356_ = lean_ctor_get(v_toFunctor_354_, 0);
lean_inc(v_map_356_);
lean_dec_ref(v_toFunctor_354_);
v___x_357_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_357_, 0, v_e_341_);
v___x_358_ = l_Lean_SubExpr_Pos_pushProj(v_p_340_);
lean_dec(v_p_340_);
v___x_359_ = lean_apply_2(v_visit_339_, v___x_358_, v_struct_355_);
v___x_360_ = lean_apply_4(v_map_356_, lean_box(0), lean_box(0), v___x_357_, v___x_359_);
return v___x_360_;
}
default: 
{
lean_object* v_toApplicative_361_; lean_object* v_toPure_362_; lean_object* v___x_363_; 
v_toApplicative_361_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_361_);
lean_dec(v_p_340_);
lean_dec(v_visit_339_);
lean_dec_ref(v_inst_338_);
lean_dec(v_inst_337_);
lean_dec_ref(v_inst_336_);
v_toPure_362_ = lean_ctor_get(v_toApplicative_361_, 1);
lean_inc(v_toPure_362_);
lean_dec_ref(v_toApplicative_361_);
v___x_363_ = lean_apply_2(v_toPure_362_, lean_box(0), v_e_341_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos(lean_object* v_M_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_visit_368_, lean_object* v_p_369_, lean_object* v_e_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Meta_traverseChildrenWithPos___redArg(v_inst_365_, v_inst_366_, v_inst_367_, v_visit_368_, v_p_369_, v_e_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda___redArg(lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_visit_375_, lean_object* v_e_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_377_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseLambdaWithPos), 7, 4);
lean_closure_set(v___x_377_, 0, lean_box(0));
lean_closure_set(v___x_377_, 1, v_inst_372_);
lean_closure_set(v___x_377_, 2, v_inst_373_);
lean_closure_set(v___x_377_, 3, v_inst_374_);
v___x_378_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_377_, v_visit_375_, v_e_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda(lean_object* v_M_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_visit_383_, lean_object* v_e_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_Meta_traverseLambda___redArg(v_inst_380_, v_inst_381_, v_inst_382_, v_visit_383_, v_e_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall___redArg(lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_visit_389_, lean_object* v_e_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseForallWithPos), 7, 4);
lean_closure_set(v___x_391_, 0, lean_box(0));
lean_closure_set(v___x_391_, 1, v_inst_386_);
lean_closure_set(v___x_391_, 2, v_inst_387_);
lean_closure_set(v___x_391_, 3, v_inst_388_);
v___x_392_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_391_, v_visit_389_, v_e_390_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall(lean_object* v_M_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_visit_397_, lean_object* v_e_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Lean_Meta_traverseForall___redArg(v_inst_394_, v_inst_395_, v_inst_396_, v_visit_397_, v_e_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet___redArg(lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_visit_403_, lean_object* v_e_404_){
_start:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_405_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseLetWithPos), 7, 4);
lean_closure_set(v___x_405_, 0, lean_box(0));
lean_closure_set(v___x_405_, 1, v_inst_400_);
lean_closure_set(v___x_405_, 2, v_inst_401_);
lean_closure_set(v___x_405_, 3, v_inst_402_);
v___x_406_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_405_, v_visit_403_, v_e_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet(lean_object* v_M_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_visit_411_, lean_object* v_e_412_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_traverseLet___redArg(v_inst_408_, v_inst_409_, v_inst_410_, v_visit_411_, v_e_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren___redArg(lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_visit_417_, lean_object* v_e_418_){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseChildrenWithPos), 7, 4);
lean_closure_set(v___x_419_, 0, lean_box(0));
lean_closure_set(v___x_419_, 1, v_inst_414_);
lean_closure_set(v___x_419_, 2, v_inst_415_);
lean_closure_set(v___x_419_, 3, v_inst_416_);
v___x_420_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_419_, v_visit_417_, v_e_418_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren(lean_object* v_M_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_visit_425_, lean_object* v_e_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Meta_traverseChildren___redArg(v_inst_422_, v_inst_423_, v_inst_424_, v_visit_425_, v_e_426_);
return v___x_427_;
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
