// Lean compiler output
// Module: Lean.Meta.Tactic.BVDecide.Normalize.Reduction
// Imports: public import Lean.Meta.Tactic.BVDecide.Normalize.Basic import Lean.Meta.Sym.Simp.Theorems import Lean.Meta.Sym.DSimp
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
lean_object* l_Lean_Meta_Sym_DSimp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_beta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_DSimp_zeta___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed, .m_arity = 12, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed, .m_arity = 13, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__0_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2_value;
static const lean_closure_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__4___boxed, .m_arity = 11, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__1_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__2_value)} };
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3_value;
static const lean_string_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "reductionPass"};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__4_value),LEAN_SCALAR_PTR_LITERAL(99, 173, 196, 173, 194, 157, 239, 250)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__5_value),((lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__3_value)}};
static const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__6 = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass = (const lean_object*)&l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___lam__0(lean_object* v_x_1_, lean_object* v___y_2_, lean_object* v___y_3_, lean_object* v___y_4_, lean_object* v___y_5_, lean_object* v___y_6_, lean_object* v___y_7_, lean_object* v___y_8_, lean_object* v___y_9_){
_start:
{
lean_object* v___x_11_; 
lean_inc(v___y_5_);
lean_inc_ref(v___y_4_);
lean_inc(v___y_3_);
lean_inc_ref(v___y_2_);
v___x_11_ = lean_apply_9(v_x_1_, v___y_2_, v___y_3_, v___y_4_, v___y_5_, v___y_6_, v___y_7_, v___y_8_, v___y_9_, lean_box(0));
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___lam__0___boxed(lean_object* v_x_12_, lean_object* v___y_13_, lean_object* v___y_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_, lean_object* v___y_20_, lean_object* v___y_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___lam__0(v_x_12_, v___y_13_, v___y_14_, v___y_15_, v___y_16_, v___y_17_, v___y_18_, v___y_19_, v___y_20_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
lean_dec(v___y_14_);
lean_dec_ref(v___y_13_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(lean_object* v_mvarId_23_, lean_object* v_x_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v___f_34_; lean_object* v___x_35_; 
lean_inc(v___y_28_);
lean_inc_ref(v___y_27_);
lean_inc(v___y_26_);
lean_inc_ref(v___y_25_);
v___f_34_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___lam__0___boxed), 10, 5);
lean_closure_set(v___f_34_, 0, v_x_24_);
lean_closure_set(v___f_34_, 1, v___y_25_);
lean_closure_set(v___f_34_, 2, v___y_26_);
lean_closure_set(v___f_34_, 3, v___y_27_);
lean_closure_set(v___f_34_, 4, v___y_28_);
v___x_35_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_23_, v___f_34_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
if (lean_obj_tag(v___x_35_) == 0)
{
return v___x_35_;
}
else
{
lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_43_; 
v_a_36_ = lean_ctor_get(v___x_35_, 0);
v_isSharedCheck_43_ = !lean_is_exclusive(v___x_35_);
if (v_isSharedCheck_43_ == 0)
{
v___x_38_ = v___x_35_;
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_dec(v___x_35_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_43_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_41_; 
if (v_isShared_39_ == 0)
{
v___x_41_ = v___x_38_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_42_; 
v_reuseFailAlloc_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_42_, 0, v_a_36_);
v___x_41_ = v_reuseFailAlloc_42_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
return v___x_41_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg___boxed(lean_object* v_mvarId_44_, lean_object* v_x_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_mvarId_44_, v_x_45_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_, v___y_53_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
lean_dec(v___y_51_);
lean_dec_ref(v___y_50_);
lean_dec(v___y_49_);
lean_dec_ref(v___y_48_);
lean_dec(v___y_47_);
lean_dec_ref(v___y_46_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(lean_object* v_00_u03b1_56_, lean_object* v_mvarId_57_, lean_object* v_x_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_mvarId_57_, v_x_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_, v___y_63_, v___y_64_, v___y_65_, v___y_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___boxed(lean_object* v_00_u03b1_69_, lean_object* v_mvarId_70_, lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0(v_00_u03b1_69_, v_mvarId_70_, v_x_71_, v___y_72_, v___y_73_, v___y_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_);
lean_dec(v___y_79_);
lean_dec_ref(v___y_78_);
lean_dec(v___y_77_);
lean_dec_ref(v___y_76_);
lean_dec(v___y_75_);
lean_dec_ref(v___y_74_);
lean_dec(v___y_73_);
lean_dec_ref(v___y_72_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(lean_object* v_x_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_, lean_object* v___y_86_, lean_object* v___y_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; 
lean_inc_ref(v___y_83_);
v___x_94_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v___y_83_, v___y_89_, v___y_91_, v___y_92_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
if (lean_obj_tag(v_a_95_) == 0)
{
uint8_t v_done_96_; 
v_done_96_ = lean_ctor_get_uint8(v_a_95_, 0);
lean_dec_ref_known(v_a_95_, 0);
if (v_done_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref_known(v___x_94_, 1);
v___x_97_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v___y_83_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
return v___x_97_;
}
else
{
lean_dec_ref(v___y_83_);
return v___x_94_;
}
}
else
{
uint8_t v_done_98_; 
lean_dec_ref(v___y_83_);
v_done_98_ = lean_ctor_get_uint8(v_a_95_, sizeof(void*)*1);
if (v_done_98_ == 0)
{
lean_object* v_e_x27_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_117_; 
lean_dec_ref_known(v___x_94_, 1);
v_e_x27_99_ = lean_ctor_get(v_a_95_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v_a_95_);
if (v_isSharedCheck_117_ == 0)
{
v___x_101_ = v_a_95_;
v_isShared_102_ = v_isSharedCheck_117_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_e_x27_99_);
lean_dec(v_a_95_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_117_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; 
lean_inc_ref(v_e_x27_99_);
v___x_103_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_x27_99_, v___y_87_, v___y_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
if (lean_obj_tag(v_a_104_) == 0)
{
lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_115_; 
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; 
v_unused_116_ = lean_ctor_get(v___x_103_, 0);
lean_dec(v_unused_116_);
v___x_106_ = v___x_103_;
v_isShared_107_ = v_isSharedCheck_115_;
goto v_resetjp_105_;
}
else
{
lean_dec(v___x_103_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_115_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
uint8_t v_done_108_; lean_object* v___x_110_; 
v_done_108_ = lean_ctor_get_uint8(v_a_104_, 0);
lean_dec_ref_known(v_a_104_, 0);
if (v_isShared_102_ == 0)
{
v___x_110_ = v___x_101_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_e_x27_99_);
v___x_110_ = v_reuseFailAlloc_114_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; 
lean_ctor_set_uint8(v___x_110_, sizeof(void*)*1, v_done_108_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 0, v___x_110_);
v___x_112_ = v___x_106_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_104_, 1);
lean_del_object(v___x_101_);
lean_dec_ref(v_e_x27_99_);
return v___x_103_;
}
}
else
{
lean_del_object(v___x_101_);
lean_dec_ref(v_e_x27_99_);
return v___x_103_;
}
}
}
else
{
lean_dec_ref_known(v_a_95_, 1);
return v___x_94_;
}
}
}
else
{
lean_dec_ref(v___y_83_);
return v___x_94_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0___boxed(lean_object* v_x_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__0(v_x_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(lean_object* v___f_131_, lean_object* v_x_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_144_; 
lean_inc_ref(v___y_133_);
v___x_144_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(v___y_133_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_146_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_a_145_);
v___x_146_ = lean_box(0);
if (lean_obj_tag(v_a_145_) == 0)
{
uint8_t v_done_147_; 
v_done_147_ = lean_ctor_get_uint8(v_a_145_, 0);
lean_dec_ref_known(v_a_145_, 0);
if (v_done_147_ == 0)
{
lean_object* v___x_148_; 
lean_dec_ref_known(v___x_144_, 1);
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
lean_inc(v___y_140_);
lean_inc_ref(v___y_139_);
lean_inc(v___y_138_);
lean_inc_ref(v___y_137_);
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
lean_inc(v___y_134_);
v___x_148_ = lean_apply_12(v___f_131_, v___x_146_, v___y_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, lean_box(0));
return v___x_148_;
}
else
{
lean_dec_ref(v___y_133_);
lean_dec_ref(v___f_131_);
return v___x_144_;
}
}
else
{
uint8_t v_done_149_; 
lean_dec_ref(v___y_133_);
v_done_149_ = lean_ctor_get_uint8(v_a_145_, sizeof(void*)*1);
if (v_done_149_ == 0)
{
lean_object* v_e_x27_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_168_; 
lean_dec_ref_known(v___x_144_, 1);
v_e_x27_150_ = lean_ctor_get(v_a_145_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v_a_145_);
if (v_isSharedCheck_168_ == 0)
{
v___x_152_ = v_a_145_;
v_isShared_153_ = v_isSharedCheck_168_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_e_x27_150_);
lean_dec(v_a_145_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_168_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; 
lean_inc(v___y_142_);
lean_inc_ref(v___y_141_);
lean_inc(v___y_140_);
lean_inc_ref(v___y_139_);
lean_inc(v___y_138_);
lean_inc_ref(v___y_137_);
lean_inc(v___y_136_);
lean_inc_ref(v___y_135_);
lean_inc(v___y_134_);
lean_inc_ref(v_e_x27_150_);
v___x_154_ = lean_apply_12(v___f_131_, v___x_146_, v_e_x27_150_, v___y_134_, v___y_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_, v___y_141_, v___y_142_, lean_box(0));
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
if (lean_obj_tag(v_a_155_) == 0)
{
lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_166_; 
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_166_ == 0)
{
lean_object* v_unused_167_; 
v_unused_167_ = lean_ctor_get(v___x_154_, 0);
lean_dec(v_unused_167_);
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
else
{
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_166_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
uint8_t v_done_159_; lean_object* v___x_161_; 
v_done_159_ = lean_ctor_get_uint8(v_a_155_, 0);
lean_dec_ref_known(v_a_155_, 0);
if (v_isShared_153_ == 0)
{
v___x_161_ = v___x_152_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_e_x27_150_);
v___x_161_ = v_reuseFailAlloc_165_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_163_; 
lean_ctor_set_uint8(v___x_161_, sizeof(void*)*1, v_done_159_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 0, v___x_161_);
v___x_163_ = v___x_157_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_155_, 1);
lean_del_object(v___x_152_);
lean_dec_ref(v_e_x27_150_);
return v___x_154_;
}
}
else
{
lean_del_object(v___x_152_);
lean_dec_ref(v_e_x27_150_);
return v___x_154_;
}
}
}
else
{
lean_dec_ref_known(v_a_145_, 1);
lean_dec_ref(v___f_131_);
return v___x_144_;
}
}
}
else
{
lean_dec_ref(v___y_133_);
lean_dec_ref(v___f_131_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1___boxed(lean_object* v___f_169_, lean_object* v_x_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__1(v___f_169_, v_x_170_, v___y_171_, v___y_172_, v___y_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
lean_dec(v___y_180_);
lean_dec_ref(v___y_179_);
lean_dec(v___y_178_);
lean_dec_ref(v___y_177_);
lean_dec(v___y_176_);
lean_dec_ref(v___y_175_);
lean_dec(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_172_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2(lean_object* v_x_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_196_ = ((lean_object*)(l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2___closed__0));
v___x_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_197_, 0, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2___boxed(lean_object* v_x_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__2(v_x_198_, v___y_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
lean_dec(v___y_203_);
lean_dec_ref(v___y_202_);
lean_dec(v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec_ref(v_x_198_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__3(lean_object* v___x_210_, lean_object* v___f_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
lean_inc_ref(v___y_212_);
v___x_223_ = l_Lean_Meta_Sym_DSimp_evalGround___redArg(v___x_210_, v___y_212_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
v___x_225_ = lean_box(0);
if (lean_obj_tag(v_a_224_) == 0)
{
uint8_t v_done_226_; 
v_done_226_ = lean_ctor_get_uint8(v_a_224_, 0);
lean_dec_ref_known(v_a_224_, 0);
if (v_done_226_ == 0)
{
lean_object* v___x_227_; 
lean_dec_ref_known(v___x_223_, 1);
v___x_227_ = lean_apply_12(v___f_211_, v___x_225_, v___y_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, lean_box(0));
return v___x_227_;
}
else
{
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec_ref(v___f_211_);
return v___x_223_;
}
}
else
{
uint8_t v_done_228_; 
lean_dec_ref(v___y_212_);
v_done_228_ = lean_ctor_get_uint8(v_a_224_, sizeof(void*)*1);
if (v_done_228_ == 0)
{
lean_object* v_e_x27_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref_known(v___x_223_, 1);
v_e_x27_229_ = lean_ctor_get(v_a_224_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v_a_224_);
if (v_isSharedCheck_247_ == 0)
{
v___x_231_ = v_a_224_;
v_isShared_232_ = v_isSharedCheck_247_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_e_x27_229_);
lean_dec(v_a_224_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_247_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; 
lean_inc_ref(v_e_x27_229_);
v___x_233_ = lean_apply_12(v___f_211_, v___x_225_, v_e_x27_229_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, lean_box(0));
if (lean_obj_tag(v___x_233_) == 0)
{
lean_object* v_a_234_; 
v_a_234_ = lean_ctor_get(v___x_233_, 0);
lean_inc(v_a_234_);
if (lean_obj_tag(v_a_234_) == 0)
{
lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_245_; 
v_isSharedCheck_245_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_245_ == 0)
{
lean_object* v_unused_246_; 
v_unused_246_ = lean_ctor_get(v___x_233_, 0);
lean_dec(v_unused_246_);
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_245_;
goto v_resetjp_235_;
}
else
{
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_245_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v_done_238_; lean_object* v___x_240_; 
v_done_238_ = lean_ctor_get_uint8(v_a_234_, 0);
lean_dec_ref_known(v_a_234_, 0);
if (v_isShared_232_ == 0)
{
v___x_240_ = v___x_231_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_e_x27_229_);
v___x_240_ = v_reuseFailAlloc_244_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v___x_242_; 
lean_ctor_set_uint8(v___x_240_, sizeof(void*)*1, v_done_238_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_240_);
v___x_242_ = v___x_236_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_234_, 1);
lean_del_object(v___x_231_);
lean_dec_ref(v_e_x27_229_);
return v___x_233_;
}
}
else
{
lean_del_object(v___x_231_);
lean_dec_ref(v_e_x27_229_);
return v___x_233_;
}
}
}
else
{
lean_dec_ref_known(v_a_224_, 1);
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___f_211_);
return v___x_223_;
}
}
}
else
{
lean_dec(v___y_221_);
lean_dec_ref(v___y_220_);
lean_dec(v___y_219_);
lean_dec_ref(v___y_218_);
lean_dec(v___y_217_);
lean_dec_ref(v___y_216_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec_ref(v___f_211_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__3___boxed(lean_object* v___x_248_, lean_object* v___f_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__3(v___x_248_, v___f_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___x_248_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__4(lean_object* v___f_262_, lean_object* v___f_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_){
_start:
{
lean_object* v___x_273_; lean_object* v_maxSteps_274_; lean_object* v_goal_275_; uint8_t v___x_276_; lean_object* v_config_277_; lean_object* v___x_278_; lean_object* v___f_279_; lean_object* v_methods_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_273_ = lean_st_ref_get(v___y_265_);
v_maxSteps_274_ = lean_ctor_get(v___y_264_, 1);
v_goal_275_ = lean_ctor_get(v___x_273_, 4);
lean_inc(v_goal_275_);
lean_dec(v___x_273_);
v___x_276_ = 1;
lean_inc(v_maxSteps_274_);
v_config_277_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_config_277_, 0, v_maxSteps_274_);
lean_ctor_set_uint8(v_config_277_, sizeof(void*)*1, v___x_276_);
v___x_278_ = lean_unsigned_to_nat(255u);
v___f_279_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__3___boxed), 13, 2);
lean_closure_set(v___f_279_, 0, v___x_278_);
lean_closure_set(v___f_279_, 1, v___f_262_);
v_methods_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_methods_280_, 0, v___f_279_);
lean_ctor_set(v_methods_280_, 1, v___f_263_);
v___x_281_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_BVDecide_Normalize_PreProcessM_mapDSimpHyps___boxed), 11, 2);
lean_closure_set(v___x_281_, 0, v_methods_280_);
lean_closure_set(v___x_281_, 1, v_config_277_);
v___x_282_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_BVDecide_Normalize_reductionPass_spec__0___redArg(v_goal_275_, v___x_281_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__4___boxed(lean_object* v___f_283_, lean_object* v___f_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_Meta_Tactic_BVDecide_Normalize_reductionPass___lam__4(v___f_283_, v___f_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_294_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_Theorems(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_DSimp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_BVDecide_Normalize_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_DSimp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_BVDecide_Normalize_Reduction(builtin);
}
#ifdef __cplusplus
}
#endif
