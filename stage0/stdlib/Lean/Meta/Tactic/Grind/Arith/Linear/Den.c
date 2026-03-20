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
lean_object* l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_maxDegreeOf(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_mulConst(lean_object*, lean_object*);
lean_object* l_Lean_Grind_CommRing_Poly_cancelVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(lean_object* v_getPoly_3_, lean_object* v_updateCnstr_4_, lean_object* v_c_5_, lean_object* v_a_6_, lean_object* v_a_7_, lean_object* v_a_8_, lean_object* v_a_9_, lean_object* v_a_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_p_18_; lean_object* v___x_19_; 
lean_inc_ref(v_getPoly_3_);
lean_inc(v_c_5_);
v_p_18_ = lean_apply_1(v_getPoly_3_, v_c_5_);
lean_inc(v_a_16_);
lean_inc_ref(v_a_15_);
lean_inc(v_a_14_);
lean_inc_ref(v_a_13_);
lean_inc_ref(v_p_18_);
v___x_19_ = l_Lean_Grind_CommRing_Poly_findInvNumeralVar_x3f(v_p_18_, v_a_6_, v_a_7_, v_a_8_, v_a_9_, v_a_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_);
if (lean_obj_tag(v___x_19_) == 0)
{
lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_37_; 
v_a_20_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_37_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_37_ == 0)
{
v___x_22_ = v___x_19_;
v_isShared_23_ = v_isSharedCheck_37_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_37_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
if (lean_obj_tag(v_a_20_) == 1)
{
lean_object* v_val_24_; lean_object* v_fst_25_; lean_object* v_snd_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
lean_del_object(v___x_22_);
v_val_24_ = lean_ctor_get(v_a_20_, 0);
lean_inc(v_val_24_);
lean_dec_ref(v_a_20_);
v_fst_25_ = lean_ctor_get(v_val_24_, 0);
lean_inc(v_fst_25_);
v_snd_26_ = lean_ctor_get(v_val_24_, 1);
lean_inc(v_snd_26_);
lean_dec(v_val_24_);
v___x_27_ = l_Lean_Grind_CommRing_Poly_maxDegreeOf(v_p_18_, v_snd_26_);
v___x_28_ = lean_nat_to_int(v_fst_25_);
v___x_29_ = l_Int_pow(v___x_28_, v___x_27_);
v___x_30_ = l_Lean_Grind_CommRing_Poly_mulConst(v___x_29_, v_p_18_);
lean_dec(v___x_29_);
v___x_31_ = l_Lean_Grind_CommRing_Poly_cancelVar(v___x_28_, v_snd_26_, v___x_30_);
lean_inc(v_updateCnstr_4_);
v___x_32_ = lean_apply_5(v_updateCnstr_4_, v_c_5_, v___x_31_, v___x_28_, v_snd_26_, v___x_27_);
v_c_5_ = v___x_32_;
goto _start;
}
else
{
lean_object* v___x_35_; 
lean_dec(v_a_20_);
lean_dec_ref(v_p_18_);
lean_dec(v_a_16_);
lean_dec_ref(v_a_15_);
lean_dec(v_a_14_);
lean_dec_ref(v_a_13_);
lean_dec(v_updateCnstr_4_);
lean_dec_ref(v_getPoly_3_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v_c_5_);
v___x_35_ = v___x_22_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_c_5_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
}
}
else
{
lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_45_; 
lean_dec_ref(v_p_18_);
lean_dec(v_a_16_);
lean_dec_ref(v_a_15_);
lean_dec(v_a_14_);
lean_dec_ref(v_a_13_);
lean_dec(v_c_5_);
lean_dec(v_updateCnstr_4_);
lean_dec_ref(v_getPoly_3_);
v_a_38_ = lean_ctor_get(v___x_19_, 0);
v_isSharedCheck_45_ = !lean_is_exclusive(v___x_19_);
if (v_isSharedCheck_45_ == 0)
{
v___x_40_ = v___x_19_;
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_dec(v___x_19_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_45_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_43_; 
if (v_isShared_41_ == 0)
{
v___x_43_ = v___x_40_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_a_38_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg___boxed(lean_object* v_getPoly_46_, lean_object* v_updateCnstr_47_, lean_object* v_c_48_, lean_object* v_a_49_, lean_object* v_a_50_, lean_object* v_a_51_, lean_object* v_a_52_, lean_object* v_a_53_, lean_object* v_a_54_, lean_object* v_a_55_, lean_object* v_a_56_, lean_object* v_a_57_, lean_object* v_a_58_, lean_object* v_a_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_46_, v_updateCnstr_47_, v_c_48_, v_a_49_, v_a_50_, v_a_51_, v_a_52_, v_a_53_, v_a_54_, v_a_55_, v_a_56_, v_a_57_, v_a_58_, v_a_59_);
lean_dec(v_a_55_);
lean_dec_ref(v_a_54_);
lean_dec(v_a_53_);
lean_dec_ref(v_a_52_);
lean_dec(v_a_51_);
lean_dec(v_a_50_);
lean_dec_ref(v_a_49_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(lean_object* v_00_u03b1_62_, lean_object* v_getPoly_63_, lean_object* v_updateCnstr_64_, lean_object* v_c_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_, lean_object* v_a_71_, lean_object* v_a_72_, lean_object* v_a_73_, lean_object* v_a_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___redArg(v_getPoly_63_, v_updateCnstr_64_, v_c_65_, v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_, v_a_71_, v_a_72_, v_a_73_, v_a_74_, v_a_75_, v_a_76_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed(lean_object* v_00_u03b1_79_, lean_object* v_getPoly_80_, lean_object* v_updateCnstr_81_, lean_object* v_c_82_, lean_object* v_a_83_, lean_object* v_a_84_, lean_object* v_a_85_, lean_object* v_a_86_, lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_, lean_object* v_a_92_, lean_object* v_a_93_, lean_object* v_a_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go(v_00_u03b1_79_, v_getPoly_80_, v_updateCnstr_81_, v_c_82_, v_a_83_, v_a_84_, v_a_85_, v_a_86_, v_a_87_, v_a_88_, v_a_89_, v_a_90_, v_a_91_, v_a_92_, v_a_93_);
lean_dec(v_a_89_);
lean_dec_ref(v_a_88_);
lean_dec(v_a_87_);
lean_dec_ref(v_a_86_);
lean_dec(v_a_85_);
lean_dec(v_a_84_);
lean_dec_ref(v_a_83_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(lean_object* v_c_96_, lean_object* v_getPoly_97_, lean_object* v_updateCnstr_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_, lean_object* v_a_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_133_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_133_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_133_ == 0)
{
v___x_114_ = v___x_111_;
v_isShared_115_ = v_isSharedCheck_133_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_a_112_);
lean_dec(v___x_111_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_133_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v_fieldInst_x3f_116_; 
v_fieldInst_x3f_116_ = lean_ctor_get(v_a_112_, 15);
if (lean_obj_tag(v_fieldInst_x3f_116_) == 0)
{
lean_object* v___x_118_; 
lean_dec(v_a_112_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec(v_a_100_);
lean_dec(v_updateCnstr_98_);
lean_dec_ref(v_getPoly_97_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v_c_96_);
v___x_118_ = v___x_114_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_c_96_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
else
{
lean_object* v_charInst_x3f_120_; 
v_charInst_x3f_120_ = lean_ctor_get(v_a_112_, 16);
lean_inc(v_charInst_x3f_120_);
lean_dec(v_a_112_);
if (lean_obj_tag(v_charInst_x3f_120_) == 1)
{
lean_object* v_val_121_; lean_object* v_snd_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v_val_121_ = lean_ctor_get(v_charInst_x3f_120_, 0);
lean_inc(v_val_121_);
lean_dec_ref(v_charInst_x3f_120_);
v_snd_122_ = lean_ctor_get(v_val_121_, 1);
lean_inc(v_snd_122_);
lean_dec(v_val_121_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_nat_dec_eq(v_snd_122_, v___x_123_);
lean_dec(v_snd_122_);
if (v___x_124_ == 0)
{
lean_object* v___x_126_; 
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec(v_a_100_);
lean_dec(v_updateCnstr_98_);
lean_dec_ref(v_getPoly_97_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v_c_96_);
v___x_126_ = v___x_114_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_c_96_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
else
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_del_object(v___x_114_);
v___x_128_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27_go___boxed), 16, 4);
lean_closure_set(v___x_128_, 0, lean_box(0));
lean_closure_set(v___x_128_, 1, v_getPoly_97_);
lean_closure_set(v___x_128_, 2, v_updateCnstr_98_);
lean_closure_set(v___x_128_, 3, v_c_96_);
v___x_129_ = l_Lean_Meta_Grind_Arith_Linear_withRingM___redArg(v___x_128_, v_a_99_, v_a_100_, v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_, v_a_106_, v_a_107_, v_a_108_, v_a_109_);
return v___x_129_;
}
}
else
{
lean_object* v___x_131_; 
lean_dec(v_charInst_x3f_120_);
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec(v_a_100_);
lean_dec(v_updateCnstr_98_);
lean_dec_ref(v_getPoly_97_);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 0, v_c_96_);
v___x_131_ = v___x_114_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_c_96_);
v___x_131_ = v_reuseFailAlloc_132_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
return v___x_131_;
}
}
}
}
}
else
{
lean_object* v_a_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_141_; 
lean_dec(v_a_109_);
lean_dec_ref(v_a_108_);
lean_dec(v_a_107_);
lean_dec_ref(v_a_106_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
lean_dec(v_a_101_);
lean_dec(v_a_100_);
lean_dec(v_updateCnstr_98_);
lean_dec_ref(v_getPoly_97_);
lean_dec(v_c_96_);
v_a_134_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_141_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_141_ == 0)
{
v___x_136_ = v___x_111_;
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_a_134_);
lean_dec(v___x_111_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_141_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_139_; 
if (v_isShared_137_ == 0)
{
v___x_139_ = v___x_136_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_a_134_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg___boxed(lean_object* v_c_142_, lean_object* v_getPoly_143_, lean_object* v_updateCnstr_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_142_, v_getPoly_143_, v_updateCnstr_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_145_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(lean_object* v_00_u03b1_158_, lean_object* v_c_159_, lean_object* v_getPoly_160_, lean_object* v_updateCnstr_161_, lean_object* v_a_162_, lean_object* v_a_163_, lean_object* v_a_164_, lean_object* v_a_165_, lean_object* v_a_166_, lean_object* v_a_167_, lean_object* v_a_168_, lean_object* v_a_169_, lean_object* v_a_170_, lean_object* v_a_171_, lean_object* v_a_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_159_, v_getPoly_160_, v_updateCnstr_161_, v_a_162_, v_a_163_, v_a_164_, v_a_165_, v_a_166_, v_a_167_, v_a_168_, v_a_169_, v_a_170_, v_a_171_, v_a_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___boxed(lean_object* v_00_u03b1_175_, lean_object* v_c_176_, lean_object* v_getPoly_177_, lean_object* v_updateCnstr_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_, lean_object* v_a_183_, lean_object* v_a_184_, lean_object* v_a_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27(v_00_u03b1_175_, v_c_176_, v_getPoly_177_, v_updateCnstr_178_, v_a_179_, v_a_180_, v_a_181_, v_a_182_, v_a_183_, v_a_184_, v_a_185_, v_a_186_, v_a_187_, v_a_188_, v_a_189_);
lean_dec(v_a_179_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(lean_object* v_x_192_){
_start:
{
lean_object* v_p_193_; 
v_p_193_ = lean_ctor_get(v_x_192_, 0);
lean_inc_ref(v_p_193_);
return v_p_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0___boxed(lean_object* v_x_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__0(v_x_194_);
lean_dec_ref(v_x_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___lam__1(lean_object* v_c_196_, lean_object* v_p_197_, lean_object* v_val_198_, lean_object* v_x_199_, lean_object* v_n_200_){
_start:
{
uint8_t v_strict_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v_strict_201_ = lean_ctor_get_uint8(v_c_196_, sizeof(void*)*2);
v___x_202_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_202_, 0, v_c_196_);
lean_ctor_set(v___x_202_, 1, v_val_198_);
lean_ctor_set(v___x_202_, 2, v_x_199_);
lean_ctor_set(v___x_202_, 3, v_n_200_);
v___x_203_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_203_, 0, v_p_197_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*2, v_strict_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(lean_object* v_c_206_, lean_object* v_a_207_, lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___f_219_; lean_object* v___f_220_; lean_object* v___x_221_; 
v___f_219_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__0));
v___f_220_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___closed__1));
v___x_221_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_206_, v___f_219_, v___f_220_, v_a_207_, v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_, v_a_217_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators___boxed(lean_object* v_c_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Meta_Grind_Arith_Linear_RingIneqCnstr_cleanupDenominators(v_c_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_);
lean_dec(v_a_223_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(lean_object* v_x_236_){
_start:
{
lean_object* v_p_237_; 
v_p_237_ = lean_ctor_get(v_x_236_, 0);
lean_inc_ref(v_p_237_);
return v_p_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0___boxed(lean_object* v_x_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__0(v_x_238_);
lean_dec_ref(v_x_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___lam__1(lean_object* v_c_240_, lean_object* v_p_241_, lean_object* v_val_242_, lean_object* v_x_243_, lean_object* v_n_244_){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_245_, 0, v_c_240_);
lean_ctor_set(v___x_245_, 1, v_val_242_);
lean_ctor_set(v___x_245_, 2, v_x_243_);
lean_ctor_set(v___x_245_, 3, v_n_244_);
v___x_246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_246_, 0, v_p_241_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(lean_object* v_c_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_){
_start:
{
lean_object* v___f_262_; lean_object* v___f_263_; lean_object* v___x_264_; 
v___f_262_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__0));
v___f_263_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___closed__1));
v___x_264_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_249_, v___f_262_, v___f_263_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators___boxed(lean_object* v_c_265_, lean_object* v_a_266_, lean_object* v_a_267_, lean_object* v_a_268_, lean_object* v_a_269_, lean_object* v_a_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Grind_Arith_Linear_RingEqCnstr_cleanupDenominators(v_c_265_, v_a_266_, v_a_267_, v_a_268_, v_a_269_, v_a_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec(v_a_266_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(lean_object* v_x_279_){
_start:
{
lean_object* v_p_280_; 
v_p_280_ = lean_ctor_get(v_x_279_, 0);
lean_inc_ref(v_p_280_);
return v_p_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0___boxed(lean_object* v_x_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__0(v_x_281_);
lean_dec_ref(v_x_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___lam__1(lean_object* v_c_283_, lean_object* v_p_284_, lean_object* v_val_285_, lean_object* v_x_286_, lean_object* v_n_287_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_288_, 0, v_c_283_);
lean_ctor_set(v___x_288_, 1, v_val_285_);
lean_ctor_set(v___x_288_, 2, v_x_286_);
lean_ctor_set(v___x_288_, 3, v_n_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_p_284_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(lean_object* v_c_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_317_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_317_ == 0)
{
v___x_308_ = v___x_305_;
v_isShared_309_ = v_isSharedCheck_317_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_a_306_);
lean_dec(v___x_305_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_317_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v_noNatDivInst_x3f_310_; 
v_noNatDivInst_x3f_310_ = lean_ctor_get(v_a_306_, 11);
lean_inc(v_noNatDivInst_x3f_310_);
lean_dec(v_a_306_);
if (lean_obj_tag(v_noNatDivInst_x3f_310_) == 0)
{
lean_object* v___x_312_; 
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec(v_a_294_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v_c_292_);
v___x_312_ = v___x_308_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_c_292_);
v___x_312_ = v_reuseFailAlloc_313_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
return v___x_312_;
}
}
else
{
lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___x_316_; 
lean_dec_ref(v_noNatDivInst_x3f_310_);
lean_del_object(v___x_308_);
v___f_314_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__0));
v___f_315_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___closed__1));
v___x_316_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Den_0__Lean_Meta_Grind_Arith_Linear_cleanupDenominators_x27___redArg(v_c_292_, v___f_314_, v___f_315_, v_a_293_, v_a_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
return v___x_316_;
}
}
}
else
{
lean_object* v_a_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_325_; 
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
lean_dec_ref(v_a_298_);
lean_dec(v_a_297_);
lean_dec_ref(v_a_296_);
lean_dec(v_a_295_);
lean_dec(v_a_294_);
lean_dec_ref(v_c_292_);
v_a_318_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_325_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_325_ == 0)
{
v___x_320_ = v___x_305_;
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_a_318_);
lean_dec(v___x_305_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_325_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___x_323_; 
if (v_isShared_321_ == 0)
{
v___x_323_ = v___x_320_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_a_318_);
v___x_323_ = v_reuseFailAlloc_324_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
return v___x_323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators___boxed(lean_object* v_c_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_Meta_Grind_Arith_Linear_RingDiseqCnstr_cleanupDenominators(v_c_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
lean_dec(v_a_327_);
return v_res_339_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_SafePoly(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Den(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
