// Lean compiler output
// Module: Lean.Meta.MatchUtil
// Imports: public import Lean.Util.Recognizers public import Lean.Meta.CtorRecognizer
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
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_testHelper(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_testHelper___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_matchEq_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_matchEq_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_matchEq_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_matchEq_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_matchEq_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_matchEq_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_matchEq_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_matchHEq_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_matchHEq_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_matchHEq_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_matchHEq_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_matchHEq_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_matchHEq_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_matchHEq_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEqLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEqLHS_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_matchNot_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_matchNot_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_matchNot_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_matchNot_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_matchNot_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_matchNot_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_matchNot_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_matchNe_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Ne"};
static const lean_object* l_Lean_Meta_matchNe_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_matchNe_x3f___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_matchNe_x3f___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_matchNe_x3f___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(161, 247, 70, 70, 118, 145, 235, 92)}};
static const lean_object* l_Lean_Meta_matchNe_x3f___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_matchNe_x3f___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_matchConstructorApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_testHelper(lean_object* v_e_1_, lean_object* v_p_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_8_; 
lean_inc_ref(v_p_2_);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
lean_inc_ref(v_e_1_);
v___x_8_ = lean_apply_6(v_p_2_, v_e_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, lean_box(0));
if (lean_obj_tag(v___x_8_) == 0)
{
lean_object* v_a_9_; uint8_t v___x_10_; 
v_a_9_ = lean_ctor_get(v___x_8_, 0);
lean_inc(v_a_9_);
v___x_10_ = lean_unbox(v_a_9_);
lean_dec(v_a_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; 
lean_dec_ref_known(v___x_8_, 1);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_11_ = lean_whnf(v_e_1_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_12_ = lean_ctor_get(v___x_11_, 0);
lean_inc(v_a_12_);
lean_dec_ref_known(v___x_11_, 1);
lean_inc(v_a_6_);
lean_inc_ref(v_a_5_);
lean_inc(v_a_4_);
lean_inc_ref(v_a_3_);
v___x_13_ = lean_apply_6(v_p_2_, v_a_12_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, lean_box(0));
return v___x_13_;
}
else
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
lean_dec_ref(v_p_2_);
v_a_14_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_21_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_21_ == 0)
{
v___x_16_ = v___x_11_;
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_a_14_);
lean_dec(v___x_11_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_21_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_19_; 
if (v_isShared_17_ == 0)
{
v___x_19_ = v___x_16_;
goto v_reusejp_18_;
}
else
{
lean_object* v_reuseFailAlloc_20_; 
v_reuseFailAlloc_20_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_20_, 0, v_a_14_);
v___x_19_ = v_reuseFailAlloc_20_;
goto v_reusejp_18_;
}
v_reusejp_18_:
{
return v___x_19_;
}
}
}
}
else
{
lean_dec_ref(v_p_2_);
lean_dec_ref(v_e_1_);
return v___x_8_;
}
}
else
{
lean_dec_ref(v_p_2_);
lean_dec_ref(v_e_1_);
return v___x_8_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_testHelper_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v_p_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_res_22_;
v_res_22_ = l_Lean_Meta_testHelper(v_e_1_, v_p_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_testHelper___boxed(lean_object* v_e_23_, lean_object* v_p_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Meta_testHelper(v_e_23_, v_p_24_, v_a_25_, v_a_26_, v_a_27_, v_a_28_);
lean_dec(v_a_28_);
lean_dec_ref(v_a_27_);
lean_dec(v_a_26_);
lean_dec_ref(v_a_25_);
return v_res_30_;
}
}
lean_object* l_Lean_Meta_matchHelper_x3f___redArg(lean_object* v_e_31_, lean_object* v_p_x3f_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_){
_start:
{
lean_object* v___x_38_; 
lean_inc_ref(v_p_x3f_32_);
lean_inc(v_a_36_);
lean_inc_ref(v_a_35_);
lean_inc(v_a_34_);
lean_inc_ref(v_a_33_);
lean_inc_ref(v_e_31_);
v___x_38_ = lean_apply_6(v_p_x3f_32_, v_e_31_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, lean_box(0));
if (lean_obj_tag(v___x_38_) == 0)
{
lean_object* v_a_39_; 
v_a_39_ = lean_ctor_get(v___x_38_, 0);
lean_inc(v_a_39_);
if (lean_obj_tag(v_a_39_) == 0)
{
lean_object* v___x_40_; 
lean_dec_ref_known(v___x_38_, 1);
lean_inc(v_a_36_);
lean_inc_ref(v_a_35_);
lean_inc(v_a_34_);
lean_inc_ref(v_a_33_);
v___x_40_ = lean_whnf(v_e_31_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v___x_42_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_a_41_);
lean_dec_ref_known(v___x_40_, 1);
lean_inc(v_a_36_);
lean_inc_ref(v_a_35_);
lean_inc(v_a_34_);
lean_inc_ref(v_a_33_);
v___x_42_ = lean_apply_6(v_p_x3f_32_, v_a_41_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, lean_box(0));
return v___x_42_;
}
else
{
lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_50_; 
lean_dec_ref(v_p_x3f_32_);
v_a_43_ = lean_ctor_get(v___x_40_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_40_);
if (v_isSharedCheck_50_ == 0)
{
v___x_45_ = v___x_40_;
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_40_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_50_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_48_; 
if (v_isShared_46_ == 0)
{
v___x_48_ = v___x_45_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_a_43_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
else
{
lean_dec(v_a_39_);
lean_dec_ref(v_p_x3f_32_);
lean_dec_ref(v_e_31_);
return v___x_38_;
}
}
else
{
lean_dec_ref(v_p_x3f_32_);
lean_dec_ref(v_e_31_);
return v___x_38_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchHelper_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v_p_x3f_32_ = stack[1].m_obj;
lean_object* v_a_33_ = stack[2].m_obj;
lean_object* v_a_34_ = stack[3].m_obj;
lean_object* v_a_35_ = stack[4].m_obj;
lean_object* v_a_36_ = stack[5].m_obj;
lean_object* v_res_51_;
v_res_51_ = l_Lean_Meta_matchHelper_x3f___redArg(v_e_31_, v_p_x3f_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
stack->m_obj
 = v_res_51_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f___redArg___boxed(lean_object* v_e_52_, lean_object* v_p_x3f_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Meta_matchHelper_x3f___redArg(v_e_52_, v_p_x3f_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_);
lean_dec(v_a_57_);
lean_dec_ref(v_a_56_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
return v_res_59_;
}
}
lean_object* l_Lean_Meta_matchHelper_x3f(lean_object* v_00_u03b1_60_, lean_object* v_e_61_, lean_object* v_p_x3f_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; 
lean_inc_ref(v_p_x3f_62_);
lean_inc(v_a_66_);
lean_inc_ref(v_a_65_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
lean_inc_ref(v_e_61_);
v___x_68_ = lean_apply_6(v_p_x3f_62_, v_e_61_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, lean_box(0));
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
if (lean_obj_tag(v_a_69_) == 0)
{
lean_object* v___x_70_; 
lean_dec_ref_known(v___x_68_, 1);
lean_inc(v_a_66_);
lean_inc_ref(v_a_65_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
v___x_70_ = lean_whnf(v_e_61_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_72_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_70_, 1);
lean_inc(v_a_66_);
lean_inc_ref(v_a_65_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
v___x_72_ = lean_apply_6(v_p_x3f_62_, v_a_71_, v_a_63_, v_a_64_, v_a_65_, v_a_66_, lean_box(0));
return v___x_72_;
}
else
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_80_; 
lean_dec_ref(v_p_x3f_62_);
v_a_73_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_80_ == 0)
{
v___x_75_ = v___x_70_;
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_70_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_80_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_78_; 
if (v_isShared_76_ == 0)
{
v___x_78_ = v___x_75_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v_a_73_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
else
{
lean_dec(v_a_69_);
lean_dec_ref(v_p_x3f_62_);
lean_dec_ref(v_e_61_);
return v___x_68_;
}
}
else
{
lean_dec_ref(v_p_x3f_62_);
lean_dec_ref(v_e_61_);
return v___x_68_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchHelper_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_61_ = stack[1].m_obj;
lean_object* v_p_x3f_62_ = stack[2].m_obj;
lean_object* v_a_63_ = stack[3].m_obj;
lean_object* v_a_64_ = stack[4].m_obj;
lean_object* v_a_65_ = stack[5].m_obj;
lean_object* v_a_66_ = stack[6].m_obj;
lean_object* v_res_81_;
v_res_81_ = l_Lean_Meta_matchHelper_x3f(lean_box(0), v_e_61_, v_p_x3f_62_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f___boxed(lean_object* v_00_u03b1_82_, lean_object* v_e_83_, lean_object* v_p_x3f_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_matchHelper_x3f(v_00_u03b1_82_, v_e_83_, v_p_x3f_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_);
lean_dec(v_a_88_);
lean_dec_ref(v_a_87_);
lean_dec(v_a_86_);
lean_dec_ref(v_a_85_);
return v_res_90_;
}
}
lean_object* l_Lean_Meta_matchEq_x3f___lam__0(lean_object* v_e_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_100_ = ((lean_object*)(l_Lean_Meta_matchEq_x3f___lam__0___closed__1));
v___x_101_ = lean_unsigned_to_nat(3u);
v___x_102_ = l_Lean_Expr_isAppOfArity(v_e_94_, v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = lean_box(0);
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
else
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_105_ = l_Lean_Expr_appFn_x21(v_e_94_);
v___x_106_ = l_Lean_Expr_appFn_x21(v___x_105_);
v___x_107_ = l_Lean_Expr_appArg_x21(v___x_106_);
lean_dec_ref(v___x_106_);
v___x_108_ = l_Lean_Expr_appArg_x21(v___x_105_);
lean_dec_ref(v___x_105_);
v___x_109_ = l_Lean_Expr_appArg_x21(v_e_94_);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_108_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
v___x_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_107_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
v___x_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
return v___x_113_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchEq_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_94_ = stack[0].m_obj;
lean_object* v___y_95_ = stack[1].m_obj;
lean_object* v___y_96_ = stack[2].m_obj;
lean_object* v___y_97_ = stack[3].m_obj;
lean_object* v___y_98_ = stack[4].m_obj;
lean_object* v_res_114_;
v_res_114_ = l_Lean_Meta_matchEq_x3f___lam__0(v_e_94_, v___y_95_, v___y_96_, v___y_97_, v___y_98_);
stack->m_obj
 = v_res_114_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f___lam__0___boxed(lean_object* v_e_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Lean_Meta_matchEq_x3f___lam__0(v_e_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
lean_dec(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec_ref(v_e_115_);
return v_res_121_;
}
}
lean_object* l_Lean_Meta_matchEq_x3f(lean_object* v_e_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v___x_128_; lean_object* v_a_129_; 
v___x_128_ = l_Lean_Meta_matchEq_x3f___lam__0(v_e_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
v_a_129_ = lean_ctor_get(v___x_128_, 0);
if (lean_obj_tag(v_a_129_) == 0)
{
lean_object* v___x_130_; 
lean_dec_ref(v___x_128_);
lean_inc(v_a_126_);
lean_inc_ref(v_a_125_);
lean_inc(v_a_124_);
lean_inc_ref(v_a_123_);
v___x_130_ = lean_whnf(v_e_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
if (lean_obj_tag(v___x_130_) == 0)
{
lean_object* v_a_131_; lean_object* v___x_132_; 
v_a_131_ = lean_ctor_get(v___x_130_, 0);
lean_inc(v_a_131_);
lean_dec_ref_known(v___x_130_, 1);
v___x_132_ = l_Lean_Meta_matchEq_x3f___lam__0(v_a_131_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
lean_dec(v_a_131_);
return v___x_132_;
}
else
{
lean_object* v_a_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_140_; 
v_a_133_ = lean_ctor_get(v___x_130_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_130_);
if (v_isSharedCheck_140_ == 0)
{
v___x_135_ = v___x_130_;
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_a_133_);
lean_dec(v___x_130_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_140_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_138_; 
if (v_isShared_136_ == 0)
{
v___x_138_ = v___x_135_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_a_133_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
}
}
else
{
lean_dec_ref(v_e_122_);
return v___x_128_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchEq_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_122_ = stack[0].m_obj;
lean_object* v_a_123_ = stack[1].m_obj;
lean_object* v_a_124_ = stack[2].m_obj;
lean_object* v_a_125_ = stack[3].m_obj;
lean_object* v_a_126_ = stack[4].m_obj;
lean_object* v_res_141_;
v_res_141_ = l_Lean_Meta_matchEq_x3f(v_e_122_, v_a_123_, v_a_124_, v_a_125_, v_a_126_);
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f___boxed(lean_object* v_e_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Meta_matchEq_x3f(v_e_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
return v_res_148_;
}
}
lean_object* l_Lean_Meta_matchHEq_x3f___lam__0(lean_object* v_e_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_158_ = ((lean_object*)(l_Lean_Meta_matchHEq_x3f___lam__0___closed__1));
v___x_159_ = lean_unsigned_to_nat(4u);
v___x_160_ = l_Lean_Expr_isAppOfArity(v_e_152_, v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = lean_box(0);
v___x_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_163_ = l_Lean_Expr_appFn_x21(v_e_152_);
v___x_164_ = l_Lean_Expr_appFn_x21(v___x_163_);
v___x_165_ = l_Lean_Expr_appFn_x21(v___x_164_);
v___x_166_ = l_Lean_Expr_appArg_x21(v___x_165_);
lean_dec_ref(v___x_165_);
v___x_167_ = l_Lean_Expr_appArg_x21(v___x_164_);
lean_dec_ref(v___x_164_);
v___x_168_ = l_Lean_Expr_appArg_x21(v___x_163_);
lean_dec_ref(v___x_163_);
v___x_169_ = l_Lean_Expr_appArg_x21(v_e_152_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_167_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_166_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchHEq_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_152_ = stack[0].m_obj;
lean_object* v___y_153_ = stack[1].m_obj;
lean_object* v___y_154_ = stack[2].m_obj;
lean_object* v___y_155_ = stack[3].m_obj;
lean_object* v___y_156_ = stack[4].m_obj;
lean_object* v_res_175_;
v_res_175_ = l_Lean_Meta_matchHEq_x3f___lam__0(v_e_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_);
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f___lam__0___boxed(lean_object* v_e_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_matchHEq_x3f___lam__0(v_e_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec_ref(v_e_176_);
return v_res_182_;
}
}
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object* v_e_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; lean_object* v_a_190_; 
v___x_189_ = l_Lean_Meta_matchHEq_x3f___lam__0(v_e_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
v_a_190_ = lean_ctor_get(v___x_189_, 0);
if (lean_obj_tag(v_a_190_) == 0)
{
lean_object* v___x_191_; 
lean_dec_ref(v___x_189_);
lean_inc(v_a_187_);
lean_inc_ref(v_a_186_);
lean_inc(v_a_185_);
lean_inc_ref(v_a_184_);
v___x_191_ = lean_whnf(v_e_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_object* v_a_192_; lean_object* v___x_193_; 
v_a_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_a_192_);
lean_dec_ref_known(v___x_191_, 1);
v___x_193_ = l_Lean_Meta_matchHEq_x3f___lam__0(v_a_192_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
lean_dec(v_a_192_);
return v___x_193_;
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
v_a_194_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_191_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_191_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_dec_ref(v_e_183_);
return v___x_189_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchHEq_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_183_ = stack[0].m_obj;
lean_object* v_a_184_ = stack[1].m_obj;
lean_object* v_a_185_ = stack[2].m_obj;
lean_object* v_a_186_ = stack[3].m_obj;
lean_object* v_a_187_ = stack[4].m_obj;
lean_object* v_res_202_;
v_res_202_ = l_Lean_Meta_matchHEq_x3f(v_e_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f___boxed(lean_object* v_e_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_matchHEq_x3f(v_e_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_209_;
}
}
lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object* v_e_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_216_; 
lean_inc_ref(v_e_210_);
v___x_216_ = l_Lean_Meta_matchEq_x3f(v_e_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
if (lean_obj_tag(v_a_217_) == 1)
{
lean_dec_ref(v_e_210_);
return v___x_216_;
}
else
{
lean_object* v___x_218_; 
lean_dec_ref_known(v___x_216_, 1);
v___x_218_ = l_Lean_Meta_matchHEq_x3f(v_e_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_278_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_278_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_278_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_278_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
if (lean_obj_tag(v_a_219_) == 1)
{
lean_object* v_val_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_273_; 
lean_del_object(v___x_221_);
v_val_223_ = lean_ctor_get(v_a_219_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v_a_219_);
if (v_isSharedCheck_273_ == 0)
{
v___x_225_ = v_a_219_;
v_isShared_226_ = v_isSharedCheck_273_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_val_223_);
lean_dec(v_a_219_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_273_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_snd_227_; lean_object* v_snd_228_; lean_object* v_fst_229_; lean_object* v_fst_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_271_; 
v_snd_227_ = lean_ctor_get(v_val_223_, 1);
lean_inc(v_snd_227_);
v_snd_228_ = lean_ctor_get(v_snd_227_, 1);
lean_inc(v_snd_228_);
v_fst_229_ = lean_ctor_get(v_val_223_, 0);
lean_inc(v_fst_229_);
lean_dec(v_val_223_);
v_fst_230_ = lean_ctor_get(v_snd_227_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v_snd_227_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; 
v_unused_272_ = lean_ctor_get(v_snd_227_, 1);
lean_dec(v_unused_272_);
v___x_232_ = v_snd_227_;
v_isShared_233_ = v_isSharedCheck_271_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_fst_230_);
lean_dec(v_snd_227_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_271_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_fst_234_; lean_object* v_snd_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_270_; 
v_fst_234_ = lean_ctor_get(v_snd_228_, 0);
v_snd_235_ = lean_ctor_get(v_snd_228_, 1);
v_isSharedCheck_270_ = !lean_is_exclusive(v_snd_228_);
if (v_isSharedCheck_270_ == 0)
{
v___x_237_ = v_snd_228_;
v_isShared_238_ = v_isSharedCheck_270_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_snd_235_);
lean_inc(v_fst_234_);
lean_dec(v_snd_228_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_270_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; 
lean_inc(v_fst_229_);
v___x_239_ = l_Lean_Meta_isExprDefEq(v_fst_229_, v_fst_234_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_261_; 
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_261_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_261_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_261_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
uint8_t v___x_244_; 
v___x_244_ = lean_unbox(v_a_240_);
lean_dec(v_a_240_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_del_object(v___x_237_);
lean_dec(v_snd_235_);
lean_del_object(v___x_232_);
lean_dec(v_fst_230_);
lean_dec(v_fst_229_);
lean_del_object(v___x_225_);
v___x_245_ = lean_box(0);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_245_);
v___x_247_ = v___x_242_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
else
{
lean_object* v___x_250_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 0, v_fst_230_);
v___x_250_ = v___x_237_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_fst_230_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_snd_235_);
v___x_250_ = v_reuseFailAlloc_260_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v___x_250_);
lean_ctor_set(v___x_232_, 0, v_fst_229_);
v___x_252_ = v___x_232_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_fst_229_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_250_);
v___x_252_ = v_reuseFailAlloc_259_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 0, v___x_252_);
v___x_254_ = v___x_225_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_256_; 
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_254_);
v___x_256_ = v___x_242_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_254_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_del_object(v___x_237_);
lean_dec(v_snd_235_);
lean_del_object(v___x_232_);
lean_dec(v_fst_230_);
lean_dec(v_fst_229_);
lean_del_object(v___x_225_);
v_a_262_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_239_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_239_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_274_; lean_object* v___x_276_; 
lean_dec(v_a_219_);
v___x_274_ = lean_box(0);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_274_);
v___x_276_ = v___x_221_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
else
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_218_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_218_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
else
{
lean_dec_ref(v_e_210_);
return v___x_216_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchEqHEq_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_210_ = stack[0].m_obj;
lean_object* v_a_211_ = stack[1].m_obj;
lean_object* v_a_212_ = stack[2].m_obj;
lean_object* v_a_213_ = stack[3].m_obj;
lean_object* v_a_214_ = stack[4].m_obj;
lean_object* v_res_287_;
v_res_287_ = l_Lean_Meta_matchEqHEq_x3f(v_e_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEq_x3f___boxed(lean_object* v_e_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_matchEqHEq_x3f(v_e_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_);
lean_dec(v_a_292_);
lean_dec_ref(v_a_291_);
lean_dec(v_a_290_);
lean_dec_ref(v_a_289_);
return v_res_294_;
}
}
lean_object* l_Lean_Meta_matchEqHEqLHS_x3f(lean_object* v_e_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_301_; 
lean_inc_ref(v_e_295_);
v___x_301_ = l_Lean_Meta_matchEq_x3f(v_e_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_368_; 
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_368_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_368_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_368_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
if (lean_obj_tag(v_a_302_) == 1)
{
lean_object* v_val_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_327_; 
lean_dec_ref(v_e_295_);
v_val_306_ = lean_ctor_get(v_a_302_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_a_302_);
if (v_isSharedCheck_327_ == 0)
{
v___x_308_ = v_a_302_;
v_isShared_309_ = v_isSharedCheck_327_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_val_306_);
lean_dec(v_a_302_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_327_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_snd_310_; lean_object* v_fst_311_; lean_object* v_fst_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_325_; 
v_snd_310_ = lean_ctor_get(v_val_306_, 1);
lean_inc(v_snd_310_);
v_fst_311_ = lean_ctor_get(v_val_306_, 0);
lean_inc(v_fst_311_);
lean_dec(v_val_306_);
v_fst_312_ = lean_ctor_get(v_snd_310_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v_snd_310_);
if (v_isSharedCheck_325_ == 0)
{
lean_object* v_unused_326_; 
v_unused_326_ = lean_ctor_get(v_snd_310_, 1);
lean_dec(v_unused_326_);
v___x_314_ = v_snd_310_;
v_isShared_315_ = v_isSharedCheck_325_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_fst_312_);
lean_dec(v_snd_310_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_325_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_fst_312_);
lean_ctor_set(v___x_314_, 0, v_fst_311_);
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_fst_311_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_fst_312_);
v___x_317_ = v_reuseFailAlloc_324_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_319_; 
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_317_);
v___x_319_ = v___x_308_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v___x_317_);
v___x_319_ = v_reuseFailAlloc_323_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_321_; 
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_319_);
v___x_321_ = v___x_304_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v___x_319_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
}
else
{
lean_object* v___x_328_; 
lean_del_object(v___x_304_);
lean_dec(v_a_302_);
v___x_328_ = l_Lean_Meta_matchHEq_x3f(v_e_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_331_; uint8_t v_isShared_332_; uint8_t v_isSharedCheck_359_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_359_ == 0)
{
v___x_331_ = v___x_328_;
v_isShared_332_ = v_isSharedCheck_359_;
goto v_resetjp_330_;
}
else
{
lean_inc(v_a_329_);
lean_dec(v___x_328_);
v___x_331_ = lean_box(0);
v_isShared_332_ = v_isSharedCheck_359_;
goto v_resetjp_330_;
}
v_resetjp_330_:
{
if (lean_obj_tag(v_a_329_) == 1)
{
lean_object* v_val_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_354_; 
v_val_333_ = lean_ctor_get(v_a_329_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v_a_329_);
if (v_isSharedCheck_354_ == 0)
{
v___x_335_ = v_a_329_;
v_isShared_336_ = v_isSharedCheck_354_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_val_333_);
lean_dec(v_a_329_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_354_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v_snd_337_; lean_object* v_fst_338_; lean_object* v_fst_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_352_; 
v_snd_337_ = lean_ctor_get(v_val_333_, 1);
lean_inc(v_snd_337_);
v_fst_338_ = lean_ctor_get(v_val_333_, 0);
lean_inc(v_fst_338_);
lean_dec(v_val_333_);
v_fst_339_ = lean_ctor_get(v_snd_337_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v_snd_337_);
if (v_isSharedCheck_352_ == 0)
{
lean_object* v_unused_353_; 
v_unused_353_ = lean_ctor_get(v_snd_337_, 1);
lean_dec(v_unused_353_);
v___x_341_ = v_snd_337_;
v_isShared_342_ = v_isSharedCheck_352_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_fst_339_);
lean_dec(v_snd_337_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_352_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v___x_344_; 
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v_fst_339_);
lean_ctor_set(v___x_341_, 0, v_fst_338_);
v___x_344_ = v___x_341_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_fst_338_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_fst_339_);
v___x_344_ = v_reuseFailAlloc_351_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_336_ == 0)
{
lean_ctor_set(v___x_335_, 0, v___x_344_);
v___x_346_ = v___x_335_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_346_);
v___x_348_ = v___x_331_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
else
{
lean_object* v___x_355_; lean_object* v___x_357_; 
lean_dec(v_a_329_);
v___x_355_ = lean_box(0);
if (v_isShared_332_ == 0)
{
lean_ctor_set(v___x_331_, 0, v___x_355_);
v___x_357_ = v___x_331_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_367_; 
v_a_360_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_367_ == 0)
{
v___x_362_ = v___x_328_;
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_a_360_);
lean_dec(v___x_328_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_367_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v___x_365_; 
if (v_isShared_363_ == 0)
{
v___x_365_ = v___x_362_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_360_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref(v_e_295_);
v_a_369_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_301_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_301_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchEqHEqLHS_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_295_ = stack[0].m_obj;
lean_object* v_a_296_ = stack[1].m_obj;
lean_object* v_a_297_ = stack[2].m_obj;
lean_object* v_a_298_ = stack[3].m_obj;
lean_object* v_a_299_ = stack[4].m_obj;
lean_object* v_res_377_;
v_res_377_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_e_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_);
stack->m_obj
 = v_res_377_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEqLHS_x3f___boxed(lean_object* v_e_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_e_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
return v_res_384_;
}
}
lean_object* l_Lean_Meta_matchFalse___lam__0(lean_object* v_e_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_){
_start:
{
uint8_t v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_391_ = l_Lean_Expr_isFalse(v_e_385_);
v___x_392_ = lean_box(v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
return v___x_393_;
}
}
LEAN_EXPORT void l_Lean_Meta_matchFalse___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_385_ = stack[0].m_obj;
lean_object* v___y_386_ = stack[1].m_obj;
lean_object* v___y_387_ = stack[2].m_obj;
lean_object* v___y_388_ = stack[3].m_obj;
lean_object* v___y_389_ = stack[4].m_obj;
lean_object* v_res_394_;
v_res_394_ = l_Lean_Meta_matchFalse___lam__0(v_e_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
stack->m_obj
 = v_res_394_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse___lam__0___boxed(lean_object* v_e_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_matchFalse___lam__0(v_e_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_401_;
}
}
lean_object* l_Lean_Meta_matchFalse(lean_object* v_e_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
lean_object* v___x_408_; lean_object* v_a_409_; uint8_t v___x_410_; 
lean_inc_ref(v_e_402_);
v___x_408_ = l_Lean_Meta_matchFalse___lam__0(v_e_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v___x_410_ = lean_unbox(v_a_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec_ref(v___x_408_);
lean_inc(v_a_406_);
lean_inc_ref(v_a_405_);
lean_inc(v_a_404_);
lean_inc_ref(v_a_403_);
v___x_411_ = lean_whnf(v_e_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; lean_object* v___x_413_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = l_Lean_Meta_matchFalse___lam__0(v_a_412_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
return v___x_413_;
}
else
{
lean_object* v_a_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_421_; 
v_a_414_ = lean_ctor_get(v___x_411_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v___x_411_);
if (v_isSharedCheck_421_ == 0)
{
v___x_416_ = v___x_411_;
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_a_414_);
lean_dec(v___x_411_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_421_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_419_; 
if (v_isShared_417_ == 0)
{
v___x_419_ = v___x_416_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_a_414_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
}
else
{
lean_dec_ref(v_e_402_);
return v___x_408_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchFalse_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_402_ = stack[0].m_obj;
lean_object* v_a_403_ = stack[1].m_obj;
lean_object* v_a_404_ = stack[2].m_obj;
lean_object* v_a_405_ = stack[3].m_obj;
lean_object* v_a_406_ = stack[4].m_obj;
lean_object* v_res_422_;
v_res_422_ = l_Lean_Meta_matchFalse(v_e_402_, v_a_403_, v_a_404_, v_a_405_, v_a_406_);
stack->m_obj
 = v_res_422_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse___boxed(lean_object* v_e_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Meta_matchFalse(v_e_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
lean_dec(v_a_425_);
lean_dec_ref(v_a_424_);
return v_res_429_;
}
}
lean_object* l_Lean_Meta_matchNot_x3f___lam__0(lean_object* v_e_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_442_ = ((lean_object*)(l_Lean_Meta_matchNot_x3f___lam__0___closed__1));
v___x_443_ = lean_unsigned_to_nat(1u);
v___x_444_ = l_Lean_Expr_isAppOfArity(v_e_433_, v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
if (lean_obj_tag(v_e_433_) == 7)
{
lean_object* v_binderType_445_; lean_object* v_body_446_; uint8_t v___x_447_; 
v_binderType_445_ = lean_ctor_get(v_e_433_, 1);
lean_inc_ref(v_binderType_445_);
v_body_446_ = lean_ctor_get(v_e_433_, 2);
lean_inc_ref(v_body_446_);
lean_dec_ref_known(v_e_433_, 3);
v___x_447_ = l_Lean_Expr_hasLooseBVars(v_body_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_Meta_matchFalse(v_body_446_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
if (lean_obj_tag(v___x_448_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_462_; 
v_a_449_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_462_ == 0)
{
v___x_451_ = v___x_448_;
v_isShared_452_ = v_isSharedCheck_462_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_462_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
uint8_t v___x_453_; 
v___x_453_ = lean_unbox(v_a_449_);
lean_dec(v_a_449_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_456_; 
lean_dec_ref(v_binderType_445_);
v___x_454_ = lean_box(0);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_454_);
v___x_456_ = v___x_451_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_454_);
v___x_456_ = v_reuseFailAlloc_457_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
return v___x_456_;
}
}
else
{
lean_object* v___x_458_; lean_object* v___x_460_; 
v___x_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_458_, 0, v_binderType_445_);
if (v_isShared_452_ == 0)
{
lean_ctor_set(v___x_451_, 0, v___x_458_);
v___x_460_ = v___x_451_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
else
{
lean_object* v_a_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_470_; 
lean_dec_ref(v_binderType_445_);
v_a_463_ = lean_ctor_get(v___x_448_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_470_ == 0)
{
v___x_465_ = v___x_448_;
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_a_463_);
lean_dec(v___x_448_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_470_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_468_; 
if (v_isShared_466_ == 0)
{
v___x_468_ = v___x_465_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_463_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
else
{
lean_dec_ref(v_body_446_);
lean_dec_ref(v_binderType_445_);
goto v___jp_439_;
}
}
else
{
lean_dec_ref(v_e_433_);
goto v___jp_439_;
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = l_Lean_Expr_appArg_x21(v_e_433_);
lean_dec_ref(v_e_433_);
v___x_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
v___x_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
return v___x_473_;
}
v___jp_439_:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = lean_box(0);
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
return v___x_441_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchNot_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_433_ = stack[0].m_obj;
lean_object* v___y_434_ = stack[1].m_obj;
lean_object* v___y_435_ = stack[2].m_obj;
lean_object* v___y_436_ = stack[3].m_obj;
lean_object* v___y_437_ = stack[4].m_obj;
lean_object* v_res_474_;
v_res_474_ = l_Lean_Meta_matchNot_x3f___lam__0(v_e_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
stack->m_obj
 = v_res_474_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f___lam__0___boxed(lean_object* v_e_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Meta_matchNot_x3f___lam__0(v_e_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_481_;
}
}
lean_object* l_Lean_Meta_matchNot_x3f(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v___x_488_; 
lean_inc_ref(v_e_482_);
v___x_488_ = l_Lean_Meta_matchNot_x3f___lam__0(v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v_a_489_; 
v_a_489_ = lean_ctor_get(v___x_488_, 0);
if (lean_obj_tag(v_a_489_) == 0)
{
lean_object* v___x_490_; 
lean_dec_ref_known(v___x_488_, 1);
lean_inc(v_a_486_);
lean_inc_ref(v_a_485_);
lean_inc(v_a_484_);
lean_inc_ref(v_a_483_);
v___x_490_ = lean_whnf(v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___x_492_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = l_Lean_Meta_matchNot_x3f___lam__0(v_a_491_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
return v___x_492_;
}
else
{
lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_a_493_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___x_490_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_dec(v___x_490_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
}
else
{
lean_dec_ref(v_e_482_);
return v___x_488_;
}
}
else
{
lean_dec_ref(v_e_482_);
return v___x_488_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchNot_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_482_ = stack[0].m_obj;
lean_object* v_a_483_ = stack[1].m_obj;
lean_object* v_a_484_ = stack[2].m_obj;
lean_object* v_a_485_ = stack[3].m_obj;
lean_object* v_a_486_ = stack[4].m_obj;
lean_object* v_res_501_;
v_res_501_ = l_Lean_Meta_matchNot_x3f(v_e_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_);
stack->m_obj
 = v_res_501_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f___boxed(lean_object* v_e_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Meta_matchNot_x3f(v_e_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
lean_dec(v_a_506_);
lean_dec_ref(v_a_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_a_503_);
return v_res_508_;
}
}
lean_object* l_Lean_Meta_matchNe_x3f___lam__0(lean_object* v_e_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_518_ = ((lean_object*)(l_Lean_Meta_matchNe_x3f___lam__0___closed__1));
v___x_519_ = lean_unsigned_to_nat(3u);
v___x_520_ = l_Lean_Expr_isAppOfArity(v_e_512_, v___x_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Meta_matchNot_x3f(v_e_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_532_; 
v_a_522_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_532_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_532_ == 0)
{
v___x_524_ = v___x_521_;
v_isShared_525_ = v_isSharedCheck_532_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_521_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_532_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
if (lean_obj_tag(v_a_522_) == 1)
{
lean_object* v_val_526_; lean_object* v___x_527_; 
lean_del_object(v___x_524_);
v_val_526_ = lean_ctor_get(v_a_522_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v_a_522_, 1);
v___x_527_ = l_Lean_Meta_matchEq_x3f(v_val_526_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
return v___x_527_;
}
else
{
lean_object* v___x_528_; lean_object* v___x_530_; 
lean_dec(v_a_522_);
v___x_528_ = lean_box(0);
if (v_isShared_525_ == 0)
{
lean_ctor_set(v___x_524_, 0, v___x_528_);
v___x_530_ = v___x_524_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
v_a_533_ = lean_ctor_get(v___x_521_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_521_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_521_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_521_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_541_ = l_Lean_Expr_appFn_x21(v_e_512_);
v___x_542_ = l_Lean_Expr_appFn_x21(v___x_541_);
v___x_543_ = l_Lean_Expr_appArg_x21(v___x_542_);
lean_dec_ref(v___x_542_);
v___x_544_ = l_Lean_Expr_appArg_x21(v___x_541_);
lean_dec_ref(v___x_541_);
v___x_545_ = l_Lean_Expr_appArg_x21(v_e_512_);
lean_dec_ref(v_e_512_);
v___x_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_544_);
lean_ctor_set(v___x_546_, 1, v___x_545_);
v___x_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_543_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v___x_548_);
return v___x_549_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchNe_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_512_ = stack[0].m_obj;
lean_object* v___y_513_ = stack[1].m_obj;
lean_object* v___y_514_ = stack[2].m_obj;
lean_object* v___y_515_ = stack[3].m_obj;
lean_object* v___y_516_ = stack[4].m_obj;
lean_object* v_res_550_;
v_res_550_ = l_Lean_Meta_matchNe_x3f___lam__0(v_e_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
stack->m_obj
 = v_res_550_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f___lam__0___boxed(lean_object* v_e_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean_Meta_matchNe_x3f___lam__0(v_e_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
return v_res_557_;
}
}
lean_object* l_Lean_Meta_matchNe_x3f(lean_object* v_e_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v___x_564_; 
lean_inc_ref(v_e_558_);
v___x_564_ = l_Lean_Meta_matchNe_x3f___lam__0(v_e_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
if (lean_obj_tag(v_a_565_) == 0)
{
lean_object* v___x_566_; 
lean_dec_ref_known(v___x_564_, 1);
lean_inc(v_a_562_);
lean_inc_ref(v_a_561_);
lean_inc(v_a_560_);
lean_inc_ref(v_a_559_);
v___x_566_ = lean_whnf(v_e_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_568_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v___x_566_, 1);
v___x_568_ = l_Lean_Meta_matchNe_x3f___lam__0(v_a_567_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
return v___x_568_;
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
v_a_569_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_566_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_566_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_dec_ref(v_e_558_);
return v___x_564_;
}
}
else
{
lean_dec_ref(v_e_558_);
return v___x_564_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchNe_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_558_ = stack[0].m_obj;
lean_object* v_a_559_ = stack[1].m_obj;
lean_object* v_a_560_ = stack[2].m_obj;
lean_object* v_a_561_ = stack[3].m_obj;
lean_object* v_a_562_ = stack[4].m_obj;
lean_object* v_res_577_;
v_res_577_ = l_Lean_Meta_matchNe_x3f(v_e_558_, v_a_559_, v_a_560_, v_a_561_, v_a_562_);
stack->m_obj
 = v_res_577_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f___boxed(lean_object* v_e_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_Meta_matchNe_x3f(v_e_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
return v_res_584_;
}
}
lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object* v_e_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; 
lean_inc_ref(v_e_585_);
v___x_591_ = l_Lean_Meta_isConstructorApp_x3f(v_e_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_591_) == 0)
{
lean_object* v_a_592_; 
v_a_592_ = lean_ctor_get(v___x_591_, 0);
if (lean_obj_tag(v_a_592_) == 0)
{
lean_object* v___x_593_; 
lean_dec_ref_known(v___x_591_, 1);
lean_inc(v_a_589_);
lean_inc_ref(v_a_588_);
lean_inc(v_a_587_);
lean_inc_ref(v_a_586_);
v___x_593_ = lean_whnf(v_e_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = l_Lean_Meta_isConstructorApp_x3f(v_a_594_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
return v___x_595_;
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
v_a_596_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_593_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_593_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
else
{
lean_dec_ref(v_e_585_);
return v___x_591_;
}
}
else
{
lean_dec_ref(v_e_585_);
return v___x_591_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_matchConstructorApp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_585_ = stack[0].m_obj;
lean_object* v_a_586_ = stack[1].m_obj;
lean_object* v_a_587_ = stack[2].m_obj;
lean_object* v_a_588_ = stack[3].m_obj;
lean_object* v_a_589_ = stack[4].m_obj;
lean_object* v_res_604_;
v_res_604_ = l_Lean_Meta_matchConstructorApp_x3f(v_e_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_);
stack->m_obj
 = v_res_604_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchConstructorApp_x3f___boxed(lean_object* v_e_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_, lean_object* v_a_609_, lean_object* v_a_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_Meta_matchConstructorApp_x3f(v_e_605_, v_a_606_, v_a_607_, v_a_608_, v_a_609_);
lean_dec(v_a_609_);
lean_dec_ref(v_a_608_);
lean_dec(v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_611_;
}
}
lean_object* runtime_initialize_Lean_Util_Recognizers(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_MatchUtil(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_MatchUtil(builtin);
}
#ifdef __cplusplus
}
#endif
