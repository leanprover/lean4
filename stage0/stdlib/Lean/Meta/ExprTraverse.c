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
lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_binderName_35_, uint8_t v_binderInfo_36_, lean_object* v___f_37_, lean_object* v_d_38_){
_start:
{
uint8_t v___x_39_; lean_object* v___x_40_; 
v___x_39_ = 0;
v___x_40_ = l_Lean_Meta_withLocalDecl___redArg(v_inst_33_, v_inst_34_, v_binderName_35_, v_binderInfo_36_, v_d_38_, v___f_37_, v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_33_ = stack[0].m_obj;
lean_object* v_inst_34_ = stack[1].m_obj;
lean_object* v_binderName_35_ = stack[2].m_obj;
uint8_t v_binderInfo_36_ = stack[3].m_num;
lean_object* v___f_37_ = stack[4].m_obj;
lean_object* v_d_38_ = stack[5].m_obj;
lean_object* v_res_41_;
v_res_41_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(v_inst_33_, v_inst_34_, v_binderName_35_, v_binderInfo_36_, v___f_37_, v_d_38_);
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed(lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_binderName_44_, lean_object* v_binderInfo_45_, lean_object* v___f_46_, lean_object* v_d_47_){
_start:
{
uint8_t v_binderInfo_128__boxed_48_; lean_object* v_res_49_; 
v_binderInfo_128__boxed_48_ = lean_unbox(v_binderInfo_45_);
v_res_49_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1(v_inst_42_, v_inst_43_, v_binderName_44_, v_binderInfo_128__boxed_48_, v___f_46_, v_d_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed(lean_object* v_fvars_50_, lean_object* v_p_51_, lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_f_55_, lean_object* v_body_56_, lean_object* v_x_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(v_fvars_50_, v_p_51_, v_inst_52_, v_inst_53_, v_inst_54_, v_f_55_, v_body_56_, v_x_57_);
lean_dec(v_p_51_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_f_62_, lean_object* v_fvars_63_, lean_object* v_p_64_, lean_object* v_a_65_){
_start:
{
if (lean_obj_tag(v_a_65_) == 6)
{
lean_object* v_toBind_66_; lean_object* v_binderName_67_; lean_object* v_binderType_68_; lean_object* v_body_69_; uint8_t v_binderInfo_70_; lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___f_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v_toBind_66_ = lean_ctor_get(v_inst_59_, 1);
lean_inc(v_toBind_66_);
v_binderName_67_ = lean_ctor_get(v_a_65_, 0);
lean_inc(v_binderName_67_);
v_binderType_68_ = lean_ctor_get(v_a_65_, 1);
lean_inc_ref(v_binderType_68_);
v_body_69_ = lean_ctor_get(v_a_65_, 2);
lean_inc_ref(v_body_69_);
v_binderInfo_70_ = lean_ctor_get_uint8(v_a_65_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_65_, 3);
lean_inc(v_f_62_);
lean_inc_ref(v_inst_61_);
lean_inc_ref(v_inst_59_);
lean_inc(v_p_64_);
lean_inc_ref(v_fvars_63_);
v___f_71_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_71_, 0, v_fvars_63_);
lean_closure_set(v___f_71_, 1, v_p_64_);
lean_closure_set(v___f_71_, 2, v_inst_59_);
lean_closure_set(v___f_71_, 3, v_inst_60_);
lean_closure_set(v___f_71_, 4, v_inst_61_);
lean_closure_set(v___f_71_, 5, v_f_62_);
lean_closure_set(v___f_71_, 6, v_body_69_);
v___x_72_ = lean_box(v_binderInfo_70_);
v___f_73_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_73_, 0, v_inst_61_);
lean_closure_set(v___f_73_, 1, v_inst_59_);
lean_closure_set(v___f_73_, 2, v_binderName_67_);
lean_closure_set(v___f_73_, 3, v___x_72_);
lean_closure_set(v___f_73_, 4, v___f_71_);
v___x_74_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_64_);
lean_dec(v_p_64_);
v___x_75_ = lean_expr_instantiate_rev(v_binderType_68_, v_fvars_63_);
lean_dec_ref(v_fvars_63_);
lean_dec_ref(v_binderType_68_);
v___x_76_ = lean_apply_2(v_f_62_, v___x_74_, v___x_75_);
v___x_77_ = lean_apply_4(v_toBind_66_, lean_box(0), lean_box(0), v___x_76_, v___f_73_);
return v___x_77_;
}
else
{
lean_object* v_toBind_78_; lean_object* v___f_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec_ref(v_inst_61_);
v_toBind_78_ = lean_ctor_get(v_inst_59_, 1);
lean_inc(v_toBind_78_);
lean_dec_ref(v_inst_59_);
lean_inc_ref(v_fvars_63_);
v___f_79_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__2), 3, 2);
lean_closure_set(v___f_79_, 0, v_fvars_63_);
lean_closure_set(v___f_79_, 1, v_inst_60_);
v___x_80_ = lean_expr_instantiate_rev(v_a_65_, v_fvars_63_);
lean_dec_ref(v_fvars_63_);
lean_dec_ref(v_a_65_);
v___x_81_ = lean_apply_2(v_f_62_, v_p_64_, v___x_80_);
v___x_82_ = lean_apply_4(v_toBind_78_, lean_box(0), lean_box(0), v___x_81_, v___f_79_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__0(lean_object* v_fvars_83_, lean_object* v_p_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_inst_87_, lean_object* v_f_88_, lean_object* v_body_89_, lean_object* v_x_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_91_ = lean_array_push(v_fvars_83_, v_x_90_);
v___x_92_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_84_);
v___x_93_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(v_inst_85_, v_inst_86_, v_inst_87_, v_f_88_, v___x_91_, v___x_92_, v_body_89_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit(lean_object* v_M_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_inst_97_, lean_object* v_f_98_, lean_object* v_fvars_99_, lean_object* v_p_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(v_inst_95_, v_inst_96_, v_inst_97_, v_f_98_, v_fvars_99_, v_p_100_, v_a_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos___redArg(lean_object* v_inst_105_, lean_object* v_inst_106_, lean_object* v_inst_107_, lean_object* v_f_108_, lean_object* v_p_109_, lean_object* v_e_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = ((lean_object*)(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0));
v___x_112_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg(v_inst_105_, v_inst_106_, v_inst_107_, v_f_108_, v___x_111_, v_p_109_, v_e_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambdaWithPos(lean_object* v_M_113_, lean_object* v_inst_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_f_117_, lean_object* v_p_118_, lean_object* v_e_119_){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_traverseLambdaWithPos___redArg(v_inst_114_, v_inst_115_, v_inst_116_, v_f_117_, v_p_118_, v_e_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(lean_object* v_fvars_121_, lean_object* v_inst_122_, lean_object* v_body_123_){
_start:
{
uint8_t v___x_124_; uint8_t v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_124_ = 0;
v___x_125_ = 1;
v___x_126_ = 1;
v___x_127_ = lean_box(v___x_124_);
v___x_128_ = lean_box(v___x_125_);
v___x_129_ = lean_box(v___x_125_);
v___x_130_ = lean_box(v___x_126_);
lean_inc_ref(v_fvars_121_);
v___x_131_ = lean_alloc_closure((void*)(l_Lean_Meta_mkForallFVars___boxed), 11, 6);
lean_closure_set(v___x_131_, 0, v_fvars_121_);
lean_closure_set(v___x_131_, 1, v_body_123_);
lean_closure_set(v___x_131_, 2, v___x_127_);
lean_closure_set(v___x_131_, 3, v___x_128_);
lean_closure_set(v___x_131_, 4, v___x_129_);
lean_closure_set(v___x_131_, 5, v___x_130_);
v___x_132_ = lean_apply_2(v_inst_122_, lean_box(0), v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2___boxed(lean_object* v_fvars_133_, lean_object* v_inst_134_, lean_object* v_body_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2(v_fvars_133_, v_inst_134_, v_body_135_);
lean_dec_ref(v_fvars_133_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed(lean_object* v_fvars_137_, lean_object* v_p_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_inst_141_, lean_object* v_f_142_, lean_object* v_body_143_, lean_object* v_x_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(v_fvars_137_, v_p_138_, v_inst_139_, v_inst_140_, v_inst_141_, v_f_142_, v_body_143_, v_x_144_);
lean_dec(v_p_138_);
lean_dec_ref(v_fvars_137_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_f_149_, lean_object* v_fvars_150_, lean_object* v_p_151_, lean_object* v_a_152_){
_start:
{
if (lean_obj_tag(v_a_152_) == 7)
{
lean_object* v_toBind_153_; lean_object* v_binderName_154_; lean_object* v_binderType_155_; lean_object* v_body_156_; uint8_t v_binderInfo_157_; lean_object* v___f_158_; lean_object* v___x_159_; lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_toBind_153_ = lean_ctor_get(v_inst_146_, 1);
lean_inc(v_toBind_153_);
v_binderName_154_ = lean_ctor_get(v_a_152_, 0);
lean_inc(v_binderName_154_);
v_binderType_155_ = lean_ctor_get(v_a_152_, 1);
lean_inc_ref(v_binderType_155_);
v_body_156_ = lean_ctor_get(v_a_152_, 2);
lean_inc_ref(v_body_156_);
v_binderInfo_157_ = lean_ctor_get_uint8(v_a_152_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_152_, 3);
lean_inc(v_f_149_);
lean_inc_ref(v_inst_148_);
lean_inc_ref(v_inst_146_);
lean_inc(v_p_151_);
lean_inc_ref(v_fvars_150_);
v___f_158_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_158_, 0, v_fvars_150_);
lean_closure_set(v___f_158_, 1, v_p_151_);
lean_closure_set(v___f_158_, 2, v_inst_146_);
lean_closure_set(v___f_158_, 3, v_inst_147_);
lean_closure_set(v___f_158_, 4, v_inst_148_);
lean_closure_set(v___f_158_, 5, v_f_149_);
lean_closure_set(v___f_158_, 6, v_body_156_);
v___x_159_ = lean_box(v_binderInfo_157_);
v___f_160_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLambdaWithPos_visit___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_160_, 0, v_inst_148_);
lean_closure_set(v___f_160_, 1, v_inst_146_);
lean_closure_set(v___f_160_, 2, v_binderName_154_);
lean_closure_set(v___f_160_, 3, v___x_159_);
lean_closure_set(v___f_160_, 4, v___f_158_);
v___x_161_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_151_);
lean_dec(v_p_151_);
v___x_162_ = lean_expr_instantiate_rev(v_binderType_155_, v_fvars_150_);
lean_dec_ref(v_binderType_155_);
v___x_163_ = lean_apply_2(v_f_149_, v___x_161_, v___x_162_);
v___x_164_ = lean_apply_4(v_toBind_153_, lean_box(0), lean_box(0), v___x_163_, v___f_160_);
return v___x_164_;
}
else
{
lean_object* v_toBind_165_; lean_object* v___f_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec_ref(v_inst_148_);
v_toBind_165_ = lean_ctor_get(v_inst_146_, 1);
lean_inc(v_toBind_165_);
lean_dec_ref(v_inst_146_);
lean_inc_ref(v_fvars_150_);
v___f_166_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__2___boxed), 3, 2);
lean_closure_set(v___f_166_, 0, v_fvars_150_);
lean_closure_set(v___f_166_, 1, v_inst_147_);
v___x_167_ = lean_expr_instantiate_rev(v_a_152_, v_fvars_150_);
lean_dec_ref(v_a_152_);
v___x_168_ = lean_apply_2(v_f_149_, v_p_151_, v___x_167_);
v___x_169_ = lean_apply_4(v_toBind_165_, lean_box(0), lean_box(0), v___x_168_, v___f_166_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___lam__0(lean_object* v_fvars_170_, lean_object* v_p_171_, lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_f_175_, lean_object* v_body_176_, lean_object* v_x_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_inc_ref(v_fvars_170_);
v___x_178_ = lean_array_push(v_fvars_170_, v_x_177_);
v___x_179_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_171_);
v___x_180_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_172_, v_inst_173_, v_inst_174_, v_f_175_, v___x_178_, v___x_179_, v_body_176_);
lean_dec_ref(v___x_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg___boxed(lean_object* v_inst_181_, lean_object* v_inst_182_, lean_object* v_inst_183_, lean_object* v_f_184_, lean_object* v_fvars_185_, lean_object* v_p_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_181_, v_inst_182_, v_inst_183_, v_f_184_, v_fvars_185_, v_p_186_, v_a_187_);
lean_dec_ref(v_fvars_185_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(lean_object* v_M_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_f_193_, lean_object* v_fvars_194_, lean_object* v_p_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_190_, v_inst_191_, v_inst_192_, v_f_193_, v_fvars_194_, v_p_195_, v_a_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___boxed(lean_object* v_M_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_f_202_, lean_object* v_fvars_203_, lean_object* v_p_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit(v_M_198_, v_inst_199_, v_inst_200_, v_inst_201_, v_f_202_, v_fvars_203_, v_p_204_, v_a_205_);
lean_dec_ref(v_fvars_203_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos___redArg(lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_f_210_, lean_object* v_p_211_, lean_object* v_e_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = ((lean_object*)(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0));
v___x_214_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseForallWithPos_visit___redArg(v_inst_207_, v_inst_208_, v_inst_209_, v_f_210_, v___x_213_, v_p_211_, v_e_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForallWithPos(lean_object* v_M_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_f_219_, lean_object* v_p_220_, lean_object* v_e_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Lean_Meta_traverseForallWithPos___redArg(v_inst_216_, v_inst_217_, v_inst_218_, v_f_219_, v_p_220_, v_e_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1(lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_declName_225_, lean_object* v_type_226_, lean_object* v___f_227_, lean_object* v_value_228_){
_start:
{
uint8_t v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_229_ = 0;
v___x_230_ = 0;
v___x_231_ = l_Lean_Meta_withLetDecl___redArg(v_inst_223_, v_inst_224_, v_declName_225_, v_type_226_, v_value_228_, v___f_227_, v___x_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_declName_234_, lean_object* v___f_235_, lean_object* v_p_236_, lean_object* v_value_237_, lean_object* v_fvars_238_, lean_object* v_f_239_, lean_object* v_toBind_240_, lean_object* v_type_241_){
_start:
{
lean_object* v___f_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___f_242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__1), 6, 5);
lean_closure_set(v___f_242_, 0, v_inst_232_);
lean_closure_set(v___f_242_, 1, v_inst_233_);
lean_closure_set(v___f_242_, 2, v_declName_234_);
lean_closure_set(v___f_242_, 3, v_type_241_);
lean_closure_set(v___f_242_, 4, v___f_235_);
v___x_243_ = l_Lean_SubExpr_Pos_pushLetValue(v_p_236_);
v___x_244_ = lean_expr_instantiate_rev(v_value_237_, v_fvars_238_);
v___x_245_ = lean_apply_2(v_f_239_, v___x_243_, v___x_244_);
v___x_246_ = lean_apply_4(v_toBind_240_, lean_box(0), lean_box(0), v___x_245_, v___f_242_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed(lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_declName_249_, lean_object* v___f_250_, lean_object* v_p_251_, lean_object* v_value_252_, lean_object* v_fvars_253_, lean_object* v_f_254_, lean_object* v_toBind_255_, lean_object* v_type_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2(v_inst_247_, v_inst_248_, v_declName_249_, v___f_250_, v_p_251_, v_value_252_, v_fvars_253_, v_f_254_, v_toBind_255_, v_type_256_);
lean_dec_ref(v_fvars_253_);
lean_dec_ref(v_value_252_);
lean_dec(v_p_251_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3(lean_object* v_fvars_258_, lean_object* v_inst_259_, lean_object* v_body_260_){
_start:
{
uint8_t v___x_261_; uint8_t v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_261_ = 0;
v___x_262_ = 1;
v___x_263_ = 1;
v___x_264_ = lean_box(v___x_261_);
v___x_265_ = lean_box(v___x_262_);
v___x_266_ = lean_box(v___x_263_);
v___x_267_ = lean_alloc_closure((void*)(l_Lean_Meta_mkLetFVars___boxed), 10, 5);
lean_closure_set(v___x_267_, 0, v_fvars_258_);
lean_closure_set(v___x_267_, 1, v_body_260_);
lean_closure_set(v___x_267_, 2, v___x_264_);
lean_closure_set(v___x_267_, 3, v___x_265_);
lean_closure_set(v___x_267_, 4, v___x_266_);
v___x_268_ = lean_apply_2(v_inst_259_, lean_box(0), v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed(lean_object* v_fvars_269_, lean_object* v_p_270_, lean_object* v_inst_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_f_274_, lean_object* v_body_275_, lean_object* v_x_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(v_fvars_269_, v_p_270_, v_inst_271_, v_inst_272_, v_inst_273_, v_f_274_, v_body_275_, v_x_276_);
lean_dec(v_p_270_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_f_281_, lean_object* v_fvars_282_, lean_object* v_p_283_, lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 8)
{
lean_object* v_toBind_285_; lean_object* v_declName_286_; lean_object* v_type_287_; lean_object* v_value_288_; lean_object* v_body_289_; lean_object* v___f_290_; lean_object* v___f_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v_toBind_285_ = lean_ctor_get(v_inst_278_, 1);
lean_inc_n(v_toBind_285_, 2);
v_declName_286_ = lean_ctor_get(v_x_284_, 0);
lean_inc(v_declName_286_);
v_type_287_ = lean_ctor_get(v_x_284_, 1);
lean_inc_ref(v_type_287_);
v_value_288_ = lean_ctor_get(v_x_284_, 2);
lean_inc_ref(v_value_288_);
v_body_289_ = lean_ctor_get(v_x_284_, 3);
lean_inc_ref(v_body_289_);
lean_dec_ref_known(v_x_284_, 4);
lean_inc_n(v_f_281_, 2);
lean_inc_ref(v_inst_280_);
lean_inc_ref(v_inst_278_);
lean_inc_n(v_p_283_, 2);
lean_inc_ref_n(v_fvars_282_, 2);
v___f_290_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_290_, 0, v_fvars_282_);
lean_closure_set(v___f_290_, 1, v_p_283_);
lean_closure_set(v___f_290_, 2, v_inst_278_);
lean_closure_set(v___f_290_, 3, v_inst_279_);
lean_closure_set(v___f_290_, 4, v_inst_280_);
lean_closure_set(v___f_290_, 5, v_f_281_);
lean_closure_set(v___f_290_, 6, v_body_289_);
v___f_291_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_291_, 0, v_inst_280_);
lean_closure_set(v___f_291_, 1, v_inst_278_);
lean_closure_set(v___f_291_, 2, v_declName_286_);
lean_closure_set(v___f_291_, 3, v___f_290_);
lean_closure_set(v___f_291_, 4, v_p_283_);
lean_closure_set(v___f_291_, 5, v_value_288_);
lean_closure_set(v___f_291_, 6, v_fvars_282_);
lean_closure_set(v___f_291_, 7, v_f_281_);
lean_closure_set(v___f_291_, 8, v_toBind_285_);
v___x_292_ = l_Lean_SubExpr_Pos_pushLetVarType(v_p_283_);
lean_dec(v_p_283_);
v___x_293_ = lean_expr_instantiate_rev(v_type_287_, v_fvars_282_);
lean_dec_ref(v_fvars_282_);
lean_dec_ref(v_type_287_);
v___x_294_ = lean_apply_2(v_f_281_, v___x_292_, v___x_293_);
v___x_295_ = lean_apply_4(v_toBind_285_, lean_box(0), lean_box(0), v___x_294_, v___f_291_);
return v___x_295_;
}
else
{
lean_object* v_toBind_296_; lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
lean_dec_ref(v_inst_280_);
v_toBind_296_ = lean_ctor_get(v_inst_278_, 1);
lean_inc(v_toBind_296_);
lean_dec_ref(v_inst_278_);
lean_inc_ref(v_fvars_282_);
v___f_297_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__3), 3, 2);
lean_closure_set(v___f_297_, 0, v_fvars_282_);
lean_closure_set(v___f_297_, 1, v_inst_279_);
v___x_298_ = lean_expr_instantiate_rev(v_x_284_, v_fvars_282_);
lean_dec_ref(v_fvars_282_);
lean_dec_ref(v_x_284_);
v___x_299_ = lean_apply_2(v_f_281_, v_p_283_, v___x_298_);
v___x_300_ = lean_apply_4(v_toBind_296_, lean_box(0), lean_box(0), v___x_299_, v___f_297_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg___lam__0(lean_object* v_fvars_301_, lean_object* v_p_302_, lean_object* v_inst_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_f_306_, lean_object* v_body_307_, lean_object* v_x_308_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_array_push(v_fvars_301_, v_x_308_);
v___x_310_ = l_Lean_SubExpr_Pos_pushLetBody(v_p_302_);
v___x_311_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(v_inst_303_, v_inst_304_, v_inst_305_, v_f_306_, v___x_309_, v___x_310_, v_body_307_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit(lean_object* v_M_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_f_316_, lean_object* v_fvars_317_, lean_object* v_p_318_, lean_object* v_x_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(v_inst_313_, v_inst_314_, v_inst_315_, v_f_316_, v_fvars_317_, v_p_318_, v_x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos___redArg(lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_f_324_, lean_object* v_p_325_, lean_object* v_e_326_){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = ((lean_object*)(l_Lean_Meta_traverseLambdaWithPos___redArg___closed__0));
v___x_328_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_traverseLetWithPos_visit___redArg(v_inst_321_, v_inst_322_, v_inst_323_, v_f_324_, v___x_327_, v_p_325_, v_e_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLetWithPos(lean_object* v_M_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_f_333_, lean_object* v_p_334_, lean_object* v_e_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Lean_Meta_traverseLetWithPos___redArg(v_inst_330_, v_inst_331_, v_inst_332_, v_f_333_, v_p_334_, v_e_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos___redArg(lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_visit_340_, lean_object* v_p_341_, lean_object* v_e_342_){
_start:
{
switch(lean_obj_tag(v_e_342_))
{
case 7:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Meta_traverseForallWithPos___redArg(v_inst_337_, v_inst_338_, v_inst_339_, v_visit_340_, v_p_341_, v_e_342_);
return v___x_343_;
}
case 6:
{
lean_object* v___x_344_; 
v___x_344_ = l_Lean_Meta_traverseLambdaWithPos___redArg(v_inst_337_, v_inst_338_, v_inst_339_, v_visit_340_, v_p_341_, v_e_342_);
return v___x_344_;
}
case 8:
{
lean_object* v___x_345_; 
v___x_345_ = l_Lean_Meta_traverseLetWithPos___redArg(v_inst_337_, v_inst_338_, v_inst_339_, v_visit_340_, v_p_341_, v_e_342_);
return v___x_345_;
}
case 5:
{
lean_object* v___x_346_; 
lean_dec_ref(v_inst_339_);
lean_dec(v_inst_338_);
v___x_346_ = l_Lean_Expr_traverseAppWithPos___redArg(v_inst_337_, v_visit_340_, v_p_341_, v_e_342_);
return v___x_346_;
}
case 10:
{
lean_object* v_toApplicative_347_; lean_object* v_toFunctor_348_; lean_object* v_expr_349_; lean_object* v_map_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_toApplicative_347_ = lean_ctor_get(v_inst_337_, 0);
lean_inc_ref(v_toApplicative_347_);
lean_dec_ref(v_inst_339_);
lean_dec(v_inst_338_);
lean_dec_ref(v_inst_337_);
v_toFunctor_348_ = lean_ctor_get(v_toApplicative_347_, 0);
lean_inc_ref(v_toFunctor_348_);
lean_dec_ref(v_toApplicative_347_);
v_expr_349_ = lean_ctor_get(v_e_342_, 1);
lean_inc_ref(v_expr_349_);
v_map_350_ = lean_ctor_get(v_toFunctor_348_, 0);
lean_inc(v_map_350_);
lean_dec_ref(v_toFunctor_348_);
v___x_351_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl), 2, 1);
lean_closure_set(v___x_351_, 0, v_e_342_);
v___x_352_ = lean_apply_2(v_visit_340_, v_p_341_, v_expr_349_);
v___x_353_ = lean_apply_4(v_map_350_, lean_box(0), lean_box(0), v___x_351_, v___x_352_);
return v___x_353_;
}
case 11:
{
lean_object* v_toApplicative_354_; lean_object* v_toFunctor_355_; lean_object* v_struct_356_; lean_object* v_map_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_toApplicative_354_ = lean_ctor_get(v_inst_337_, 0);
lean_inc_ref(v_toApplicative_354_);
lean_dec_ref(v_inst_339_);
lean_dec(v_inst_338_);
lean_dec_ref(v_inst_337_);
v_toFunctor_355_ = lean_ctor_get(v_toApplicative_354_, 0);
lean_inc_ref(v_toFunctor_355_);
lean_dec_ref(v_toApplicative_354_);
v_struct_356_ = lean_ctor_get(v_e_342_, 2);
lean_inc_ref(v_struct_356_);
v_map_357_ = lean_ctor_get(v_toFunctor_355_, 0);
lean_inc(v_map_357_);
lean_dec_ref(v_toFunctor_355_);
v___x_358_ = lean_alloc_closure((void*)(l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl), 2, 1);
lean_closure_set(v___x_358_, 0, v_e_342_);
v___x_359_ = l_Lean_SubExpr_Pos_pushProj(v_p_341_);
lean_dec(v_p_341_);
v___x_360_ = lean_apply_2(v_visit_340_, v___x_359_, v_struct_356_);
v___x_361_ = lean_apply_4(v_map_357_, lean_box(0), lean_box(0), v___x_358_, v___x_360_);
return v___x_361_;
}
default: 
{
lean_object* v_toApplicative_362_; lean_object* v_toPure_363_; lean_object* v___x_364_; 
v_toApplicative_362_ = lean_ctor_get(v_inst_337_, 0);
lean_inc_ref(v_toApplicative_362_);
lean_dec(v_p_341_);
lean_dec(v_visit_340_);
lean_dec_ref(v_inst_339_);
lean_dec(v_inst_338_);
lean_dec_ref(v_inst_337_);
v_toPure_363_ = lean_ctor_get(v_toApplicative_362_, 1);
lean_inc(v_toPure_363_);
lean_dec_ref(v_toApplicative_362_);
v___x_364_ = lean_apply_2(v_toPure_363_, lean_box(0), v_e_342_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildrenWithPos(lean_object* v_M_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_visit_369_, lean_object* v_p_370_, lean_object* v_e_371_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_traverseChildrenWithPos___redArg(v_inst_366_, v_inst_367_, v_inst_368_, v_visit_369_, v_p_370_, v_e_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda___redArg(lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_visit_376_, lean_object* v_e_377_){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseLambdaWithPos), 7, 4);
lean_closure_set(v___x_378_, 0, lean_box(0));
lean_closure_set(v___x_378_, 1, v_inst_373_);
lean_closure_set(v___x_378_, 2, v_inst_374_);
lean_closure_set(v___x_378_, 3, v_inst_375_);
v___x_379_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_378_, v_visit_376_, v_e_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLambda(lean_object* v_M_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_visit_384_, lean_object* v_e_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_traverseLambda___redArg(v_inst_381_, v_inst_382_, v_inst_383_, v_visit_384_, v_e_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall___redArg(lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_visit_390_, lean_object* v_e_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseForallWithPos), 7, 4);
lean_closure_set(v___x_392_, 0, lean_box(0));
lean_closure_set(v___x_392_, 1, v_inst_387_);
lean_closure_set(v___x_392_, 2, v_inst_388_);
lean_closure_set(v___x_392_, 3, v_inst_389_);
v___x_393_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_392_, v_visit_390_, v_e_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseForall(lean_object* v_M_394_, lean_object* v_inst_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_visit_398_, lean_object* v_e_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Meta_traverseForall___redArg(v_inst_395_, v_inst_396_, v_inst_397_, v_visit_398_, v_e_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet___redArg(lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_visit_404_, lean_object* v_e_405_){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseLetWithPos), 7, 4);
lean_closure_set(v___x_406_, 0, lean_box(0));
lean_closure_set(v___x_406_, 1, v_inst_401_);
lean_closure_set(v___x_406_, 2, v_inst_402_);
lean_closure_set(v___x_406_, 3, v_inst_403_);
v___x_407_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_406_, v_visit_404_, v_e_405_);
return v___x_407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseLet(lean_object* v_M_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_visit_412_, lean_object* v_e_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_traverseLet___redArg(v_inst_409_, v_inst_410_, v_inst_411_, v_visit_412_, v_e_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren___redArg(lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_visit_418_, lean_object* v_e_419_){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_alloc_closure((void*)(l_Lean_Meta_traverseChildrenWithPos), 7, 4);
lean_closure_set(v___x_420_, 0, lean_box(0));
lean_closure_set(v___x_420_, 1, v_inst_415_);
lean_closure_set(v___x_420_, 2, v_inst_416_);
lean_closure_set(v___x_420_, 3, v_inst_417_);
v___x_421_ = l___private_Lean_Meta_ExprTraverse_0__Lean_Meta_forgetPos___redArg(v___x_420_, v_visit_418_, v_e_419_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_traverseChildren(lean_object* v_M_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_visit_426_, lean_object* v_e_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Lean_Meta_traverseChildren___redArg(v_inst_423_, v_inst_424_, v_inst_425_, v_visit_426_, v_e_427_);
return v___x_428_;
}
}
lean_object* runtime_initialize_Lean_SubExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_ExprTraverse(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
