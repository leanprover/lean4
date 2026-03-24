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
LEAN_EXPORT lean_object* l_Lean_Meta_testHelper(lean_object* v_e_1_, lean_object* v_p_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_){
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
lean_dec_ref(v___x_8_);
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
lean_dec_ref(v___x_11_);
v___x_13_ = lean_apply_6(v_p_2_, v_a_12_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, lean_box(0));
return v___x_13_;
}
else
{
lean_object* v_a_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_21_; 
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_a_4_);
lean_dec_ref(v_a_3_);
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
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_a_4_);
lean_dec_ref(v_a_3_);
lean_dec_ref(v_p_2_);
lean_dec_ref(v_e_1_);
return v___x_8_;
}
}
else
{
lean_dec(v_a_6_);
lean_dec_ref(v_a_5_);
lean_dec(v_a_4_);
lean_dec_ref(v_a_3_);
lean_dec_ref(v_p_2_);
lean_dec_ref(v_e_1_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_testHelper___boxed(lean_object* v_e_22_, lean_object* v_p_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Meta_testHelper(v_e_22_, v_p_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f___redArg(lean_object* v_e_30_, lean_object* v_p_x3f_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v___x_37_; 
lean_inc_ref(v_p_x3f_31_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc_ref(v_a_32_);
lean_inc_ref(v_e_30_);
v___x_37_ = lean_apply_6(v_p_x3f_31_, v_e_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, lean_box(0));
if (lean_obj_tag(v___x_37_) == 0)
{
lean_object* v_a_38_; 
v_a_38_ = lean_ctor_get(v___x_37_, 0);
lean_inc(v_a_38_);
if (lean_obj_tag(v_a_38_) == 0)
{
lean_object* v___x_39_; 
lean_dec_ref(v___x_37_);
lean_inc(v_a_35_);
lean_inc_ref(v_a_34_);
lean_inc(v_a_33_);
lean_inc_ref(v_a_32_);
v___x_39_ = lean_whnf(v_e_30_, v_a_32_, v_a_33_, v_a_34_, v_a_35_);
if (lean_obj_tag(v___x_39_) == 0)
{
lean_object* v_a_40_; lean_object* v___x_41_; 
v_a_40_ = lean_ctor_get(v___x_39_, 0);
lean_inc(v_a_40_);
lean_dec_ref(v___x_39_);
v___x_41_ = lean_apply_6(v_p_x3f_31_, v_a_40_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, lean_box(0));
return v___x_41_;
}
else
{
lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec_ref(v_p_x3f_31_);
v_a_42_ = lean_ctor_get(v___x_39_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_39_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v___x_39_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_39_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_a_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
else
{
lean_dec(v_a_38_);
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec_ref(v_p_x3f_31_);
lean_dec_ref(v_e_30_);
return v___x_37_;
}
}
else
{
lean_dec(v_a_35_);
lean_dec_ref(v_a_34_);
lean_dec(v_a_33_);
lean_dec_ref(v_a_32_);
lean_dec_ref(v_p_x3f_31_);
lean_dec_ref(v_e_30_);
return v___x_37_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f___redArg___boxed(lean_object* v_e_50_, lean_object* v_p_x3f_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Meta_matchHelper_x3f___redArg(v_e_50_, v_p_x3f_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f(lean_object* v_00_u03b1_58_, lean_object* v_e_59_, lean_object* v_p_x3f_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_66_; 
lean_inc_ref(v_p_x3f_60_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
lean_inc(v_a_62_);
lean_inc_ref(v_a_61_);
lean_inc_ref(v_e_59_);
v___x_66_ = lean_apply_6(v_p_x3f_60_, v_e_59_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, lean_box(0));
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
if (lean_obj_tag(v_a_67_) == 0)
{
lean_object* v___x_68_; 
lean_dec_ref(v___x_66_);
lean_inc(v_a_64_);
lean_inc_ref(v_a_63_);
lean_inc(v_a_62_);
lean_inc_ref(v_a_61_);
v___x_68_ = lean_whnf(v_e_59_, v_a_61_, v_a_62_, v_a_63_, v_a_64_);
if (lean_obj_tag(v___x_68_) == 0)
{
lean_object* v_a_69_; lean_object* v___x_70_; 
v_a_69_ = lean_ctor_get(v___x_68_, 0);
lean_inc(v_a_69_);
lean_dec_ref(v___x_68_);
v___x_70_ = lean_apply_6(v_p_x3f_60_, v_a_69_, v_a_61_, v_a_62_, v_a_63_, v_a_64_, lean_box(0));
return v___x_70_;
}
else
{
lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_78_; 
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec_ref(v_p_x3f_60_);
v_a_71_ = lean_ctor_get(v___x_68_, 0);
v_isSharedCheck_78_ = !lean_is_exclusive(v___x_68_);
if (v_isSharedCheck_78_ == 0)
{
v___x_73_ = v___x_68_;
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_68_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_78_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_76_; 
if (v_isShared_74_ == 0)
{
v___x_76_ = v___x_73_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_a_71_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
else
{
lean_dec(v_a_67_);
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec_ref(v_p_x3f_60_);
lean_dec_ref(v_e_59_);
return v___x_66_;
}
}
else
{
lean_dec(v_a_64_);
lean_dec_ref(v_a_63_);
lean_dec(v_a_62_);
lean_dec_ref(v_a_61_);
lean_dec_ref(v_p_x3f_60_);
lean_dec_ref(v_e_59_);
return v___x_66_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHelper_x3f___boxed(lean_object* v_00_u03b1_79_, lean_object* v_e_80_, lean_object* v_p_x3f_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Meta_matchHelper_x3f(v_00_u03b1_79_, v_e_80_, v_p_x3f_81_, v_a_82_, v_a_83_, v_a_84_, v_a_85_);
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f___lam__0(lean_object* v_e_91_, lean_object* v___y_92_, lean_object* v___y_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_97_ = ((lean_object*)(l_Lean_Meta_matchEq_x3f___lam__0___closed__1));
v___x_98_ = lean_unsigned_to_nat(3u);
v___x_99_ = l_Lean_Expr_isAppOfArity(v_e_91_, v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_box(0);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_102_ = l_Lean_Expr_appFn_x21(v_e_91_);
v___x_103_ = l_Lean_Expr_appFn_x21(v___x_102_);
v___x_104_ = l_Lean_Expr_appArg_x21(v___x_103_);
lean_dec_ref(v___x_103_);
v___x_105_ = l_Lean_Expr_appArg_x21(v___x_102_);
lean_dec_ref(v___x_102_);
v___x_106_ = l_Lean_Expr_appArg_x21(v_e_91_);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_104_);
lean_ctor_set(v___x_108_, 1, v___x_107_);
v___x_109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
v___x_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f___lam__0___boxed(lean_object* v_e_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Meta_matchEq_x3f___lam__0(v_e_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
lean_dec_ref(v_e_111_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f(lean_object* v_e_118_, lean_object* v_a_119_, lean_object* v_a_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v___x_124_; lean_object* v_a_125_; 
v___x_124_ = l_Lean_Meta_matchEq_x3f___lam__0(v_e_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
if (lean_obj_tag(v_a_125_) == 0)
{
lean_object* v___x_126_; 
lean_dec_ref(v___x_124_);
lean_inc(v_a_122_);
lean_inc_ref(v_a_121_);
lean_inc(v_a_120_);
lean_inc_ref(v_a_119_);
v___x_126_ = lean_whnf(v_e_118_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
if (lean_obj_tag(v___x_126_) == 0)
{
lean_object* v_a_127_; lean_object* v___x_128_; 
v_a_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc(v_a_127_);
lean_dec_ref(v___x_126_);
v___x_128_ = l_Lean_Meta_matchEq_x3f___lam__0(v_a_127_, v_a_119_, v_a_120_, v_a_121_, v_a_122_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec(v_a_127_);
return v___x_128_;
}
else
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
v_a_129_ = lean_ctor_get(v___x_126_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_126_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v___x_126_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_126_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_a_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
lean_dec(v_a_125_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
lean_dec(v_a_120_);
lean_dec_ref(v_a_119_);
lean_dec_ref(v_e_118_);
return v___x_124_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEq_x3f___boxed(lean_object* v_e_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_Lean_Meta_matchEq_x3f(v_e_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f___lam__0(lean_object* v_e_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_153_ = ((lean_object*)(l_Lean_Meta_matchHEq_x3f___lam__0___closed__1));
v___x_154_ = lean_unsigned_to_nat(4u);
v___x_155_ = l_Lean_Expr_isAppOfArity(v_e_147_, v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_158_ = l_Lean_Expr_appFn_x21(v_e_147_);
v___x_159_ = l_Lean_Expr_appFn_x21(v___x_158_);
v___x_160_ = l_Lean_Expr_appFn_x21(v___x_159_);
v___x_161_ = l_Lean_Expr_appArg_x21(v___x_160_);
lean_dec_ref(v___x_160_);
v___x_162_ = l_Lean_Expr_appArg_x21(v___x_159_);
lean_dec_ref(v___x_159_);
v___x_163_ = l_Lean_Expr_appArg_x21(v___x_158_);
lean_dec_ref(v___x_158_);
v___x_164_ = l_Lean_Expr_appArg_x21(v_e_147_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_162_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_161_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
v___x_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
v___x_169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
return v___x_169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f___lam__0___boxed(lean_object* v_e_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lean_Meta_matchHEq_x3f___lam__0(v_e_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec_ref(v_e_170_);
return v_res_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f(lean_object* v_e_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_183_; lean_object* v_a_184_; 
v___x_183_ = l_Lean_Meta_matchHEq_x3f___lam__0(v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
if (lean_obj_tag(v_a_184_) == 0)
{
lean_object* v___x_185_; 
lean_dec_ref(v___x_183_);
lean_inc(v_a_181_);
lean_inc_ref(v_a_180_);
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
v___x_185_ = lean_whnf(v_e_177_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref(v___x_185_);
v___x_187_ = l_Lean_Meta_matchHEq_x3f___lam__0(v_a_186_, v_a_178_, v_a_179_, v_a_180_, v_a_181_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_186_);
return v___x_187_;
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
v_a_188_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_185_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_185_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_dec(v_a_184_);
lean_dec(v_a_181_);
lean_dec_ref(v_a_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec_ref(v_e_177_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchHEq_x3f___boxed(lean_object* v_e_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_Meta_matchHEq_x3f(v_e_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object* v_e_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; 
lean_inc(v_a_207_);
lean_inc_ref(v_a_206_);
lean_inc(v_a_205_);
lean_inc_ref(v_a_204_);
lean_inc_ref(v_e_203_);
v___x_209_ = l_Lean_Meta_matchEq_x3f(v_e_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
if (lean_obj_tag(v_a_210_) == 1)
{
lean_dec_ref(v_a_210_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec_ref(v_e_203_);
return v___x_209_;
}
else
{
lean_object* v___x_211_; 
lean_dec(v_a_210_);
lean_dec_ref(v___x_209_);
lean_inc(v_a_207_);
lean_inc_ref(v_a_206_);
lean_inc(v_a_205_);
lean_inc_ref(v_a_204_);
v___x_211_ = l_Lean_Meta_matchHEq_x3f(v_e_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_271_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_271_ == 0)
{
v___x_214_ = v___x_211_;
v_isShared_215_ = v_isSharedCheck_271_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_211_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_271_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
if (lean_obj_tag(v_a_212_) == 1)
{
lean_object* v_val_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_266_; 
lean_del_object(v___x_214_);
v_val_216_ = lean_ctor_get(v_a_212_, 0);
v_isSharedCheck_266_ = !lean_is_exclusive(v_a_212_);
if (v_isSharedCheck_266_ == 0)
{
v___x_218_ = v_a_212_;
v_isShared_219_ = v_isSharedCheck_266_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_val_216_);
lean_dec(v_a_212_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_266_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v_snd_220_; lean_object* v_snd_221_; lean_object* v_fst_222_; lean_object* v_fst_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_264_; 
v_snd_220_ = lean_ctor_get(v_val_216_, 1);
lean_inc(v_snd_220_);
v_snd_221_ = lean_ctor_get(v_snd_220_, 1);
lean_inc(v_snd_221_);
v_fst_222_ = lean_ctor_get(v_val_216_, 0);
lean_inc(v_fst_222_);
lean_dec(v_val_216_);
v_fst_223_ = lean_ctor_get(v_snd_220_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v_snd_220_);
if (v_isSharedCheck_264_ == 0)
{
lean_object* v_unused_265_; 
v_unused_265_ = lean_ctor_get(v_snd_220_, 1);
lean_dec(v_unused_265_);
v___x_225_ = v_snd_220_;
v_isShared_226_ = v_isSharedCheck_264_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_fst_223_);
lean_dec(v_snd_220_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_264_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v_fst_227_; lean_object* v_snd_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_263_; 
v_fst_227_ = lean_ctor_get(v_snd_221_, 0);
v_snd_228_ = lean_ctor_get(v_snd_221_, 1);
v_isSharedCheck_263_ = !lean_is_exclusive(v_snd_221_);
if (v_isSharedCheck_263_ == 0)
{
v___x_230_ = v_snd_221_;
v_isShared_231_ = v_isSharedCheck_263_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_snd_228_);
lean_inc(v_fst_227_);
lean_dec(v_snd_221_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_263_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_232_; 
lean_inc(v_fst_222_);
v___x_232_ = l_Lean_Meta_isExprDefEq(v_fst_222_, v_fst_227_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_254_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_254_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_254_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_254_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
uint8_t v___x_237_; 
v___x_237_ = lean_unbox(v_a_233_);
lean_dec(v_a_233_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; lean_object* v___x_240_; 
lean_del_object(v___x_230_);
lean_dec(v_snd_228_);
lean_del_object(v___x_225_);
lean_dec(v_fst_223_);
lean_dec(v_fst_222_);
lean_del_object(v___x_218_);
v___x_238_ = lean_box(0);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_238_);
v___x_240_ = v___x_235_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v___x_238_);
v___x_240_ = v_reuseFailAlloc_241_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
return v___x_240_;
}
}
else
{
lean_object* v___x_243_; 
if (v_isShared_231_ == 0)
{
lean_ctor_set(v___x_230_, 0, v_fst_223_);
v___x_243_ = v___x_230_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_fst_223_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_snd_228_);
v___x_243_ = v_reuseFailAlloc_253_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_245_; 
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_243_);
lean_ctor_set(v___x_225_, 0, v_fst_222_);
v___x_245_ = v___x_225_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_fst_222_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_252_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_245_);
v___x_247_ = v___x_218_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_251_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
lean_object* v___x_249_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_247_);
v___x_249_ = v___x_235_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_del_object(v___x_230_);
lean_dec(v_snd_228_);
lean_del_object(v___x_225_);
lean_dec(v_fst_223_);
lean_dec(v_fst_222_);
lean_del_object(v___x_218_);
v_a_255_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_232_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_232_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_267_; lean_object* v___x_269_; 
lean_dec(v_a_212_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
v___x_267_ = lean_box(0);
if (v_isShared_215_ == 0)
{
lean_ctor_set(v___x_214_, 0, v___x_267_);
v___x_269_ = v___x_214_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v___x_267_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
else
{
lean_object* v_a_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_279_; 
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
v_a_272_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_279_ == 0)
{
v___x_274_ = v___x_211_;
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_a_272_);
lean_dec(v___x_211_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_279_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_277_; 
if (v_isShared_275_ == 0)
{
v___x_277_ = v___x_274_;
goto v_reusejp_276_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v_a_272_);
v___x_277_ = v_reuseFailAlloc_278_;
goto v_reusejp_276_;
}
v_reusejp_276_:
{
return v___x_277_;
}
}
}
}
}
else
{
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
lean_dec_ref(v_e_203_);
return v___x_209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEq_x3f___boxed(lean_object* v_e_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Meta_matchEqHEq_x3f(v_e_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEqLHS_x3f(lean_object* v_e_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
lean_object* v___x_293_; 
lean_inc(v_a_291_);
lean_inc_ref(v_a_290_);
lean_inc(v_a_289_);
lean_inc_ref(v_a_288_);
lean_inc_ref(v_e_287_);
v___x_293_ = l_Lean_Meta_matchEq_x3f(v_e_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_293_) == 0)
{
lean_object* v_a_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_360_; 
v_a_294_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_360_ == 0)
{
v___x_296_ = v___x_293_;
v_isShared_297_ = v_isSharedCheck_360_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_a_294_);
lean_dec(v___x_293_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_360_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
if (lean_obj_tag(v_a_294_) == 1)
{
lean_object* v_val_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_319_; 
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec_ref(v_e_287_);
v_val_298_ = lean_ctor_get(v_a_294_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v_a_294_);
if (v_isSharedCheck_319_ == 0)
{
v___x_300_ = v_a_294_;
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_val_298_);
lean_dec(v_a_294_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_snd_302_; lean_object* v_fst_303_; lean_object* v_fst_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_317_; 
v_snd_302_ = lean_ctor_get(v_val_298_, 1);
lean_inc(v_snd_302_);
v_fst_303_ = lean_ctor_get(v_val_298_, 0);
lean_inc(v_fst_303_);
lean_dec(v_val_298_);
v_fst_304_ = lean_ctor_get(v_snd_302_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v_snd_302_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v_snd_302_, 1);
lean_dec(v_unused_318_);
v___x_306_ = v_snd_302_;
v_isShared_307_ = v_isSharedCheck_317_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_fst_304_);
lean_dec(v_snd_302_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_317_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_fst_304_);
lean_ctor_set(v___x_306_, 0, v_fst_303_);
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_fst_303_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_fst_304_);
v___x_309_ = v_reuseFailAlloc_316_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
lean_object* v___x_311_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_309_);
v___x_311_ = v___x_300_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_309_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_313_; 
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_311_);
v___x_313_ = v___x_296_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
}
else
{
lean_object* v___x_320_; 
lean_del_object(v___x_296_);
lean_dec(v_a_294_);
v___x_320_ = l_Lean_Meta_matchHEq_x3f(v_e_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_351_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_351_ == 0)
{
v___x_323_ = v___x_320_;
v_isShared_324_ = v_isSharedCheck_351_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_a_321_);
lean_dec(v___x_320_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_351_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
if (lean_obj_tag(v_a_321_) == 1)
{
lean_object* v_val_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_346_; 
v_val_325_ = lean_ctor_get(v_a_321_, 0);
v_isSharedCheck_346_ = !lean_is_exclusive(v_a_321_);
if (v_isSharedCheck_346_ == 0)
{
v___x_327_ = v_a_321_;
v_isShared_328_ = v_isSharedCheck_346_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_val_325_);
lean_dec(v_a_321_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_346_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v_snd_329_; lean_object* v_fst_330_; lean_object* v_fst_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_344_; 
v_snd_329_ = lean_ctor_get(v_val_325_, 1);
lean_inc(v_snd_329_);
v_fst_330_ = lean_ctor_get(v_val_325_, 0);
lean_inc(v_fst_330_);
lean_dec(v_val_325_);
v_fst_331_ = lean_ctor_get(v_snd_329_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v_snd_329_);
if (v_isSharedCheck_344_ == 0)
{
lean_object* v_unused_345_; 
v_unused_345_ = lean_ctor_get(v_snd_329_, 1);
lean_dec(v_unused_345_);
v___x_333_ = v_snd_329_;
v_isShared_334_ = v_isSharedCheck_344_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_fst_331_);
lean_dec(v_snd_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_344_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_336_; 
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_fst_331_);
lean_ctor_set(v___x_333_, 0, v_fst_330_);
v___x_336_ = v___x_333_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_fst_330_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v_fst_331_);
v___x_336_ = v_reuseFailAlloc_343_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_338_; 
if (v_isShared_328_ == 0)
{
lean_ctor_set(v___x_327_, 0, v___x_336_);
v___x_338_ = v___x_327_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_336_);
v___x_338_ = v_reuseFailAlloc_342_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_340_; 
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_338_);
v___x_340_ = v___x_323_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
}
else
{
lean_object* v___x_347_; lean_object* v___x_349_; 
lean_dec(v_a_321_);
v___x_347_ = lean_box(0);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 0, v___x_347_);
v___x_349_ = v___x_323_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
v_a_352_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_320_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_320_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
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
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec(v_a_291_);
lean_dec_ref(v_a_290_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec_ref(v_e_287_);
v_a_361_ = lean_ctor_get(v___x_293_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_293_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_293_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_293_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchEqHEqLHS_x3f___boxed(lean_object* v_e_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_e_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
return v_res_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse___lam__0(lean_object* v_e_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = l_Lean_Expr_isFalse(v_e_376_);
v___x_383_ = lean_box(v___x_382_);
v___x_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse___lam__0___boxed(lean_object* v_e_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Meta_matchFalse___lam__0(v_e_385_, v___y_386_, v___y_387_, v___y_388_, v___y_389_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
lean_dec(v___y_387_);
lean_dec_ref(v___y_386_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse(lean_object* v_e_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_398_; lean_object* v_a_399_; uint8_t v___x_400_; 
lean_inc_ref(v_e_392_);
v___x_398_ = l_Lean_Meta_matchFalse___lam__0(v_e_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
v_a_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_a_399_);
v___x_400_ = lean_unbox(v_a_399_);
lean_dec(v_a_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; 
lean_dec_ref(v___x_398_);
lean_inc(v_a_396_);
lean_inc_ref(v_a_395_);
lean_inc(v_a_394_);
lean_inc_ref(v_a_393_);
v___x_401_ = lean_whnf(v_e_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
if (lean_obj_tag(v___x_401_) == 0)
{
lean_object* v_a_402_; lean_object* v___x_403_; 
v_a_402_ = lean_ctor_get(v___x_401_, 0);
lean_inc(v_a_402_);
lean_dec_ref(v___x_401_);
v___x_403_ = l_Lean_Meta_matchFalse___lam__0(v_a_402_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
return v___x_403_;
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_411_; 
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
v_a_404_ = lean_ctor_get(v___x_401_, 0);
v_isSharedCheck_411_ = !lean_is_exclusive(v___x_401_);
if (v_isSharedCheck_411_ == 0)
{
v___x_406_ = v___x_401_;
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_401_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_411_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_409_; 
if (v_isShared_407_ == 0)
{
v___x_409_ = v___x_406_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_a_404_);
v___x_409_ = v_reuseFailAlloc_410_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
return v___x_409_;
}
}
}
}
else
{
lean_dec(v_a_396_);
lean_dec_ref(v_a_395_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec_ref(v_e_392_);
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchFalse___boxed(lean_object* v_e_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Meta_matchFalse(v_e_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f___lam__0(lean_object* v_e_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_431_ = ((lean_object*)(l_Lean_Meta_matchNot_x3f___lam__0___closed__1));
v___x_432_ = lean_unsigned_to_nat(1u);
v___x_433_ = l_Lean_Expr_isAppOfArity(v_e_422_, v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
if (lean_obj_tag(v_e_422_) == 7)
{
lean_object* v_binderType_434_; lean_object* v_body_435_; uint8_t v___x_436_; 
v_binderType_434_ = lean_ctor_get(v_e_422_, 1);
lean_inc_ref(v_binderType_434_);
v_body_435_ = lean_ctor_get(v_e_422_, 2);
lean_inc_ref(v_body_435_);
lean_dec_ref(v_e_422_);
v___x_436_ = l_Lean_Expr_hasLooseBVars(v_body_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; 
v___x_437_ = l_Lean_Meta_matchFalse(v_body_435_, v___y_423_, v___y_424_, v___y_425_, v___y_426_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_451_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_451_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_451_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
uint8_t v___x_442_; 
v___x_442_ = lean_unbox(v_a_438_);
lean_dec(v_a_438_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; lean_object* v___x_445_; 
lean_dec_ref(v_binderType_434_);
v___x_443_ = lean_box(0);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_443_);
v___x_445_ = v___x_440_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_447_, 0, v_binderType_434_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_447_);
v___x_449_ = v___x_440_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
lean_dec_ref(v_binderType_434_);
v_a_452_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_437_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_437_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_dec_ref(v_body_435_);
lean_dec_ref(v_binderType_434_);
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
goto v___jp_428_;
}
}
else
{
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec_ref(v_e_422_);
goto v___jp_428_;
}
}
else
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
lean_dec(v___y_426_);
lean_dec_ref(v___y_425_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
v___x_460_ = l_Lean_Expr_appArg_x21(v_e_422_);
lean_dec_ref(v_e_422_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
v___jp_428_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(0);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f___lam__0___boxed(lean_object* v_e_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Lean_Meta_matchNot_x3f___lam__0(v_e_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f(lean_object* v_e_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v___x_476_; 
lean_inc(v_a_474_);
lean_inc_ref(v_a_473_);
lean_inc(v_a_472_);
lean_inc_ref(v_a_471_);
lean_inc_ref(v_e_470_);
v___x_476_ = l_Lean_Meta_matchNot_x3f___lam__0(v_e_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_476_) == 0)
{
lean_object* v_a_477_; 
v_a_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_a_477_);
if (lean_obj_tag(v_a_477_) == 0)
{
lean_object* v___x_478_; 
lean_dec_ref(v___x_476_);
lean_inc(v_a_474_);
lean_inc_ref(v_a_473_);
lean_inc(v_a_472_);
lean_inc_ref(v_a_471_);
v___x_478_ = lean_whnf(v_e_470_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref(v___x_478_);
v___x_480_ = l_Lean_Meta_matchNot_x3f___lam__0(v_a_479_, v_a_471_, v_a_472_, v_a_473_, v_a_474_);
return v___x_480_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_488_; 
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
v_a_481_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_488_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_488_ == 0)
{
v___x_483_ = v___x_478_;
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_a_481_);
lean_dec(v___x_478_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_488_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_486_; 
if (v_isShared_484_ == 0)
{
v___x_486_ = v___x_483_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_a_481_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
}
else
{
lean_dec(v_a_477_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec_ref(v_e_470_);
return v___x_476_;
}
}
else
{
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_a_471_);
lean_dec_ref(v_e_470_);
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNot_x3f___boxed(lean_object* v_e_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_Meta_matchNot_x3f(v_e_489_, v_a_490_, v_a_491_, v_a_492_, v_a_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f___lam__0(lean_object* v_e_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_505_ = ((lean_object*)(l_Lean_Meta_matchNe_x3f___lam__0___closed__1));
v___x_506_ = lean_unsigned_to_nat(3u);
v___x_507_ = l_Lean_Expr_isAppOfArity(v_e_499_, v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; 
lean_inc(v___y_503_);
lean_inc_ref(v___y_502_);
lean_inc(v___y_501_);
lean_inc_ref(v___y_500_);
v___x_508_ = l_Lean_Meta_matchNot_x3f(v_e_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_519_; 
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_519_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_519_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_519_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
if (lean_obj_tag(v_a_509_) == 1)
{
lean_object* v_val_513_; lean_object* v___x_514_; 
lean_del_object(v___x_511_);
v_val_513_ = lean_ctor_get(v_a_509_, 0);
lean_inc(v_val_513_);
lean_dec_ref(v_a_509_);
v___x_514_ = l_Lean_Meta_matchEq_x3f(v_val_513_, v___y_500_, v___y_501_, v___y_502_, v___y_503_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_517_; 
lean_dec(v_a_509_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
v___x_515_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_515_);
v___x_517_ = v___x_511_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
}
}
}
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
v_a_520_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_508_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_508_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
else
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
v___x_528_ = l_Lean_Expr_appFn_x21(v_e_499_);
v___x_529_ = l_Lean_Expr_appFn_x21(v___x_528_);
v___x_530_ = l_Lean_Expr_appArg_x21(v___x_529_);
lean_dec_ref(v___x_529_);
v___x_531_ = l_Lean_Expr_appArg_x21(v___x_528_);
lean_dec_ref(v___x_528_);
v___x_532_ = l_Lean_Expr_appArg_x21(v_e_499_);
lean_dec_ref(v_e_499_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_531_);
lean_ctor_set(v___x_533_, 1, v___x_532_);
v___x_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_530_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
v___x_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_536_, 0, v___x_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f___lam__0___boxed(lean_object* v_e_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lean_Meta_matchNe_x3f___lam__0(v_e_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f(lean_object* v_e_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_550_; 
lean_inc(v_a_548_);
lean_inc_ref(v_a_547_);
lean_inc(v_a_546_);
lean_inc_ref(v_a_545_);
lean_inc_ref(v_e_544_);
v___x_550_ = l_Lean_Meta_matchNe_x3f___lam__0(v_e_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
if (lean_obj_tag(v_a_551_) == 0)
{
lean_object* v___x_552_; 
lean_dec_ref(v___x_550_);
lean_inc(v_a_548_);
lean_inc_ref(v_a_547_);
lean_inc(v_a_546_);
lean_inc_ref(v_a_545_);
v___x_552_ = lean_whnf(v_e_544_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_554_; 
v_a_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_a_553_);
lean_dec_ref(v___x_552_);
v___x_554_ = l_Lean_Meta_matchNe_x3f___lam__0(v_a_553_, v_a_545_, v_a_546_, v_a_547_, v_a_548_);
return v___x_554_;
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
v_a_555_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v___x_552_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v___x_552_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
else
{
lean_dec(v_a_551_);
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec_ref(v_e_544_);
return v___x_550_;
}
}
else
{
lean_dec(v_a_548_);
lean_dec_ref(v_a_547_);
lean_dec(v_a_546_);
lean_dec_ref(v_a_545_);
lean_dec_ref(v_e_544_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchNe_x3f___boxed(lean_object* v_e_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Lean_Meta_matchNe_x3f(v_e_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object* v_e_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_576_; 
lean_inc(v_a_574_);
lean_inc_ref(v_a_573_);
lean_inc(v_a_572_);
lean_inc_ref(v_a_571_);
lean_inc_ref(v_e_570_);
v___x_576_ = l_Lean_Meta_isConstructorApp_x3f(v_e_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v_a_577_; 
v_a_577_ = lean_ctor_get(v___x_576_, 0);
lean_inc(v_a_577_);
if (lean_obj_tag(v_a_577_) == 0)
{
lean_object* v___x_578_; 
lean_dec_ref(v___x_576_);
lean_inc(v_a_574_);
lean_inc_ref(v_a_573_);
lean_inc(v_a_572_);
lean_inc_ref(v_a_571_);
v___x_578_ = lean_whnf(v_e_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_object* v_a_579_; lean_object* v___x_580_; 
v_a_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_a_579_);
lean_dec_ref(v___x_578_);
v___x_580_ = l_Lean_Meta_isConstructorApp_x3f(v_a_579_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
return v___x_580_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
v_a_581_ = lean_ctor_get(v___x_578_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_578_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_578_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_578_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_dec(v_a_577_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec_ref(v_e_570_);
return v___x_576_;
}
}
else
{
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec_ref(v_e_570_);
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_matchConstructorApp_x3f___boxed(lean_object* v_e_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Meta_matchConstructorApp_x3f(v_e_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
return v_res_595_;
}
}
lean_object* runtime_initialize_Lean_Util_Recognizers(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
