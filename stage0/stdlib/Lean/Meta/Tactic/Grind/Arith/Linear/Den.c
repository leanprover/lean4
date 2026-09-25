// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Den
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Linear.LinearM import Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
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
lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__1, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(lean_object* v_getPoly_3_, lean_object* v_updateCnstr_4_, lean_object* v_c_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_){
_start:
{
lean_object* v_p_13_; lean_object* v___x_14_; 
lean_inc_ref(v_getPoly_3_);
lean_inc(v_c_5_);
v_p_13_ = lean_apply_1(v_getPoly_3_, v_c_5_);
lean_inc_ref(v_p_13_);
v___x_14_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f___redArg(v_p_13_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_);
if (lean_obj_tag(v___x_14_) == 0)
{
lean_object* v_a_15_; lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_32_; 
v_a_15_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_32_ == 0)
{
v___x_17_ = v___x_14_;
v_isShared_18_ = v_isSharedCheck_32_;
goto v_resetjp_16_;
}
else
{
lean_inc(v_a_15_);
lean_dec(v___x_14_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_32_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
if (lean_obj_tag(v_a_15_) == 1)
{
lean_object* v_val_19_; lean_object* v_fst_20_; lean_object* v_snd_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
lean_del_object(v___x_17_);
v_val_19_ = lean_ctor_get(v_a_15_, 0);
lean_inc(v_val_19_);
lean_dec_ref_known(v_a_15_, 1);
v_fst_20_ = lean_ctor_get(v_val_19_, 0);
lean_inc(v_fst_20_);
v_snd_21_ = lean_ctor_get(v_val_19_, 1);
lean_inc(v_snd_21_);
lean_dec(v_val_19_);
v___x_22_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_13_, v_snd_21_);
v___x_23_ = lean_nat_to_int(v_fst_20_);
v___x_24_ = l_Int_pow(v___x_23_, v___x_22_);
v___x_25_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_24_, v_p_13_);
lean_dec(v___x_24_);
v___x_26_ = l_Lean_Grind_CommRing_Poly_cancelVar(v___x_23_, v_snd_21_, v___x_25_);
lean_inc(v_updateCnstr_4_);
v___x_27_ = lean_apply_5(v_updateCnstr_4_, v_c_5_, v___x_26_, v___x_23_, v_snd_21_, v___x_22_);
v_c_5_ = v___x_27_;
goto _start;
}
else
{
lean_object* v___x_30_; 
lean_dec(v_a_15_);
lean_dec_ref(v_p_13_);
lean_dec(v_updateCnstr_4_);
lean_dec_ref(v_getPoly_3_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v_c_5_);
v___x_30_ = v___x_17_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_c_5_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
else
{
lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_40_; 
lean_dec_ref(v_p_13_);
lean_dec(v_c_5_);
lean_dec(v_updateCnstr_4_);
lean_dec_ref(v_getPoly_3_);
v_a_33_ = lean_ctor_get(v___x_14_, 0);
v_isSharedCheck_40_ = !lean_is_exclusive(v___x_14_);
if (v_isSharedCheck_40_ == 0)
{
v___x_35_ = v___x_14_;
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_dec(v___x_14_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_40_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_38_; 
if (v_isShared_36_ == 0)
{
v___x_38_ = v___x_35_;
goto v_reusejp_37_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_a_33_);
v___x_38_ = v_reuseFailAlloc_39_;
goto v_reusejp_37_;
}
v_reusejp_37_:
{
return v___x_38_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg___boxed(lean_object* v_getPoly_41_, lean_object* v_updateCnstr_42_, lean_object* v_c_43_, lean_object* v_a_44_, lean_object* v_a_45_, lean_object* v_a_46_, lean_object* v_a_47_, lean_object* v_a_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_41_, v_updateCnstr_42_, v_c_43_, v_a_44_, v_a_45_, v_a_46_, v_a_47_, v_a_48_, v_a_49_);
lean_dec(v_a_49_);
lean_dec_ref(v_a_48_);
lean_dec(v_a_47_);
lean_dec_ref(v_a_46_);
lean_dec(v_a_45_);
lean_dec_ref(v_a_44_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(lean_object* v_00_u03b1_52_, lean_object* v_getPoly_53_, lean_object* v_updateCnstr_54_, lean_object* v_c_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_, lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_53_, v_updateCnstr_54_, v_c_55_, v_a_56_, v_a_57_, v_a_63_, v_a_64_, v_a_65_, v_a_66_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed(lean_object* v_00_u03b1_69_, lean_object* v_getPoly_70_, lean_object* v_updateCnstr_71_, lean_object* v_c_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_, lean_object* v_a_77_, lean_object* v_a_78_, lean_object* v_a_79_, lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(v_00_u03b1_69_, v_getPoly_70_, v_updateCnstr_71_, v_c_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_, v_a_77_, v_a_78_, v_a_79_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
lean_dec(v_a_83_);
lean_dec_ref(v_a_82_);
lean_dec(v_a_81_);
lean_dec_ref(v_a_80_);
lean_dec(v_a_79_);
lean_dec_ref(v_a_78_);
lean_dec(v_a_77_);
lean_dec_ref(v_a_76_);
lean_dec(v_a_75_);
lean_dec(v_a_74_);
lean_dec_ref(v_a_73_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(lean_object* v_c_86_, lean_object* v_getPoly_87_, lean_object* v_updateCnstr_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_, lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_123_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_123_ == 0)
{
v___x_104_ = v___x_101_;
v_isShared_105_ = v_isSharedCheck_123_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_101_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_123_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v_fieldInst_x3f_106_; 
v_fieldInst_x3f_106_ = lean_ctor_get(v_a_102_, 15);
if (lean_obj_tag(v_fieldInst_x3f_106_) == 0)
{
lean_object* v___x_108_; 
lean_dec(v_a_102_);
lean_dec(v_updateCnstr_88_);
lean_dec_ref(v_getPoly_87_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_c_86_);
v___x_108_ = v___x_104_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_109_; 
v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_109_, 0, v_c_86_);
v___x_108_ = v_reuseFailAlloc_109_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
return v___x_108_;
}
}
else
{
lean_object* v_charInst_x3f_110_; 
v_charInst_x3f_110_ = lean_ctor_get(v_a_102_, 16);
lean_inc(v_charInst_x3f_110_);
lean_dec(v_a_102_);
if (lean_obj_tag(v_charInst_x3f_110_) == 1)
{
lean_object* v_val_111_; lean_object* v_snd_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_val_111_ = lean_ctor_get(v_charInst_x3f_110_, 0);
lean_inc(v_val_111_);
lean_dec_ref_known(v_charInst_x3f_110_, 1);
v_snd_112_ = lean_ctor_get(v_val_111_, 1);
lean_inc(v_snd_112_);
lean_dec(v_val_111_);
v___x_113_ = lean_unsigned_to_nat(0u);
v___x_114_ = lean_nat_dec_eq(v_snd_112_, v___x_113_);
lean_dec(v_snd_112_);
if (v___x_114_ == 0)
{
lean_object* v___x_116_; 
lean_dec(v_updateCnstr_88_);
lean_dec_ref(v_getPoly_87_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_c_86_);
v___x_116_ = v___x_104_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_c_86_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_del_object(v___x_104_);
v___x_118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed), 16, 4);
lean_closure_set(v___x_118_, 0, lean_box(0));
lean_closure_set(v___x_118_, 1, v_getPoly_87_);
lean_closure_set(v___x_118_, 2, v_updateCnstr_88_);
lean_closure_set(v___x_118_, 3, v_c_86_);
v___x_119_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_118_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_, v_a_94_, v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
return v___x_119_;
}
}
else
{
lean_object* v___x_121_; 
lean_dec(v_charInst_x3f_110_);
lean_dec(v_updateCnstr_88_);
lean_dec_ref(v_getPoly_87_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v_c_86_);
v___x_121_ = v___x_104_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v_c_86_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_updateCnstr_88_);
lean_dec_ref(v_getPoly_87_);
lean_dec(v_c_86_);
v_a_124_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_101_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_101_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg___boxed(lean_object* v_c_132_, lean_object* v_getPoly_133_, lean_object* v_updateCnstr_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_132_, v_getPoly_133_, v_updateCnstr_134_, v_a_135_, v_a_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_a_144_);
lean_dec(v_a_143_);
lean_dec_ref(v_a_142_);
lean_dec(v_a_141_);
lean_dec_ref(v_a_140_);
lean_dec(v_a_139_);
lean_dec_ref(v_a_138_);
lean_dec(v_a_137_);
lean_dec(v_a_136_);
lean_dec(v_a_135_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(lean_object* v_00_u03b1_148_, lean_object* v_c_149_, lean_object* v_getPoly_150_, lean_object* v_updateCnstr_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v___x_164_; 
v___x_164_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_149_, v_getPoly_150_, v_updateCnstr_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___boxed(lean_object* v_00_u03b1_165_, lean_object* v_c_166_, lean_object* v_getPoly_167_, lean_object* v_updateCnstr_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(v_00_u03b1_165_, v_c_166_, v_getPoly_167_, v_updateCnstr_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
lean_dec(v_a_179_);
lean_dec_ref(v_a_178_);
lean_dec(v_a_177_);
lean_dec_ref(v_a_176_);
lean_dec(v_a_175_);
lean_dec_ref(v_a_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_a_172_);
lean_dec(v_a_171_);
lean_dec(v_a_170_);
lean_dec(v_a_169_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(lean_object* v_x_182_){
_start:
{
lean_object* v_p_183_; 
v_p_183_ = lean_ctor_get(v_x_182_, 0);
lean_inc_ref(v_p_183_);
return v_p_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0___boxed(lean_object* v_x_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(v_x_184_);
lean_dec_ref(v_x_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__1(lean_object* v_c_186_, lean_object* v_p_187_, lean_object* v_val_188_, lean_object* v_x_189_, lean_object* v_n_190_){
_start:
{
uint8_t v_strict_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_strict_191_ = lean_ctor_get_uint8(v_c_186_, sizeof(void*)*2);
v___x_192_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_192_, 0, v_c_186_);
lean_ctor_set(v___x_192_, 1, v_val_188_);
lean_ctor_set(v___x_192_, 2, v_x_189_);
lean_ctor_set(v___x_192_, 3, v_n_190_);
v___x_193_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_193_, 0, v_p_187_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*2, v_strict_191_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(lean_object* v_c_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___f_209_; lean_object* v___f_210_; lean_object* v___x_211_; 
v___f_209_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0));
v___f_210_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1));
v___x_211_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_196_, v___f_209_, v___f_210_, v_a_197_, v_a_198_, v_a_199_, v_a_200_, v_a_201_, v_a_202_, v_a_203_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___boxed(lean_object* v_c_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v_c_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
lean_dec_ref(v_a_216_);
lean_dec(v_a_215_);
lean_dec(v_a_214_);
lean_dec(v_a_213_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(lean_object* v_x_226_){
_start:
{
lean_object* v_p_227_; 
v_p_227_ = lean_ctor_get(v_x_226_, 0);
lean_inc_ref(v_p_227_);
return v_p_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0___boxed(lean_object* v_x_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(v_x_228_);
lean_dec_ref(v_x_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__1(lean_object* v_c_230_, lean_object* v_p_231_, lean_object* v_val_232_, lean_object* v_x_233_, lean_object* v_n_234_){
_start:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
v___x_235_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_235_, 0, v_c_230_);
lean_ctor_set(v___x_235_, 1, v_val_232_);
lean_ctor_set(v___x_235_, 2, v_x_233_);
lean_ctor_set(v___x_235_, 3, v_n_234_);
v___x_236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_236_, 0, v_p_231_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(lean_object* v_c_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_, lean_object* v_a_249_, lean_object* v_a_250_){
_start:
{
lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___x_254_; 
v___f_252_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0));
v___f_253_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1));
v___x_254_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_239_, v___f_252_, v___f_253_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_, v_a_248_, v_a_249_, v_a_250_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___boxed(lean_object* v_c_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_, lean_object* v_a_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v_c_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_, v_a_265_, v_a_266_);
lean_dec(v_a_266_);
lean_dec_ref(v_a_265_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec(v_a_257_);
lean_dec(v_a_256_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(lean_object* v_x_269_){
_start:
{
lean_object* v_p_270_; 
v_p_270_ = lean_ctor_get(v_x_269_, 0);
lean_inc_ref(v_p_270_);
return v_p_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0___boxed(lean_object* v_x_271_){
_start:
{
lean_object* v_res_272_; 
v_res_272_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(v_x_271_);
lean_dec_ref(v_x_271_);
return v_res_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__1(lean_object* v_c_273_, lean_object* v_p_274_, lean_object* v_val_275_, lean_object* v_x_276_, lean_object* v_n_277_){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_278_, 0, v_c_273_);
lean_ctor_set(v___x_278_, 1, v_val_275_);
lean_ctor_set(v___x_278_, 2, v_x_276_);
lean_ctor_set(v___x_278_, 3, v_n_277_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_p_274_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(lean_object* v_c_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_){
_start:
{
lean_object* v___f_295_; lean_object* v___f_296_; lean_object* v___x_297_; 
v___f_295_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0));
v___f_296_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1));
v___x_297_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_307_; 
v_a_298_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_307_ == 0)
{
v___x_300_ = v___x_297_;
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_297_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_noNatDivInst_x3f_302_; 
v_noNatDivInst_x3f_302_ = lean_ctor_get(v_a_298_, 11);
lean_inc(v_noNatDivInst_x3f_302_);
lean_dec(v_a_298_);
if (lean_obj_tag(v_noNatDivInst_x3f_302_) == 0)
{
lean_object* v___x_304_; 
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v_c_282_);
v___x_304_ = v___x_300_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_c_282_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
else
{
lean_object* v___x_306_; 
lean_dec_ref_known(v_noNatDivInst_x3f_302_, 1);
lean_del_object(v___x_300_);
v___x_306_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_282_, v___f_295_, v___f_296_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_);
return v___x_306_;
}
}
}
else
{
lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
lean_dec_ref(v_c_282_);
v_a_308_ = lean_ctor_get(v___x_297_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___x_297_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___x_297_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_dec(v___x_297_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_a_308_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___boxed(lean_object* v_c_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v_c_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
lean_dec(v_a_327_);
lean_dec_ref(v_a_326_);
lean_dec(v_a_325_);
lean_dec_ref(v_a_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec(v_a_318_);
lean_dec(v_a_317_);
return v_res_329_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(builtin);
}
#ifdef __cplusplus
}
#endif
