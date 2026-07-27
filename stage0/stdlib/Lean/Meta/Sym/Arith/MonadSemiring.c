// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadSemiring
// Imports: public import Lean.Meta.Sym.Arith.MonadCanon
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommSemiringOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommSemiringOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommSemiringOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadLift___redArg___lam__0(lean_object* v_modifySemiring_1_, lean_object* v_inst_2_, lean_object* v_f_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_modifySemiring_1_, v_f_3_);
v___x_5_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadLift___redArg(lean_object* v_inst_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_getSemiring_8_; lean_object* v_modifySemiring_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_18_; 
v_getSemiring_8_ = lean_ctor_get(v_inst_7_, 0);
v_modifySemiring_9_ = lean_ctor_get(v_inst_7_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_inst_7_);
if (v_isSharedCheck_18_ == 0)
{
v___x_11_ = v_inst_7_;
v_isShared_12_ = v_isSharedCheck_18_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_modifySemiring_9_);
lean_inc(v_getSemiring_8_);
lean_dec(v_inst_7_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_18_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_16_; 
lean_inc(v_inst_6_);
v___f_13_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_13_, 0, v_modifySemiring_9_);
lean_closure_set(v___f_13_, 1, v_inst_6_);
v___x_14_ = lean_apply_2(v_inst_6_, lean_box(0), v_getSemiring_8_);
if (v_isShared_12_ == 0)
{
lean_ctor_set(v___x_11_, 1, v___f_13_);
lean_ctor_set(v___x_11_, 0, v___x_14_);
v___x_16_ = v___x_11_;
goto v_reusejp_15_;
}
else
{
lean_object* v_reuseFailAlloc_17_; 
v_reuseFailAlloc_17_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_17_, 0, v___x_14_);
lean_ctor_set(v_reuseFailAlloc_17_, 1, v___f_13_);
v___x_16_ = v_reuseFailAlloc_17_;
goto v_reusejp_15_;
}
v_reusejp_15_:
{
return v___x_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadLift(lean_object* v_m_19_, lean_object* v_n_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v_getSemiring_23_; lean_object* v_modifySemiring_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_33_; 
v_getSemiring_23_ = lean_ctor_get(v_inst_22_, 0);
v_modifySemiring_24_ = lean_ctor_get(v_inst_22_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_inst_22_);
if (v_isSharedCheck_33_ == 0)
{
v___x_26_ = v_inst_22_;
v_isShared_27_ = v_isSharedCheck_33_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_modifySemiring_24_);
lean_inc(v_getSemiring_23_);
lean_dec(v_inst_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_33_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
lean_inc(v_inst_21_);
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_28_, 0, v_modifySemiring_24_);
lean_closure_set(v___f_28_, 1, v_inst_21_);
v___x_29_ = lean_apply_2(v_inst_21_, lean_box(0), v_getSemiring_23_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 1, v___f_28_);
lean_ctor_set(v___x_26_, 0, v___x_29_);
v___x_31_ = v___x_26_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_29_);
lean_ctor_set(v_reuseFailAlloc_32_, 1, v___f_28_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommSemiringOfMonadLift___redArg___lam__0(lean_object* v_modifyCommSemiring_34_, lean_object* v_inst_35_, lean_object* v_f_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_apply_1(v_modifyCommSemiring_34_, v_f_36_);
v___x_38_ = lean_apply_2(v_inst_35_, lean_box(0), v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommSemiringOfMonadLift___redArg(lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v_getCommSemiring_41_; lean_object* v_modifyCommSemiring_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_51_; 
v_getCommSemiring_41_ = lean_ctor_get(v_inst_40_, 0);
v_modifyCommSemiring_42_ = lean_ctor_get(v_inst_40_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_inst_40_);
if (v_isSharedCheck_51_ == 0)
{
v___x_44_ = v_inst_40_;
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_modifyCommSemiring_42_);
lean_inc(v_getCommSemiring_41_);
lean_dec(v_inst_40_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
lean_inc(v_inst_39_);
v___f_46_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadCommSemiringOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_46_, 0, v_modifyCommSemiring_42_);
lean_closure_set(v___f_46_, 1, v_inst_39_);
v___x_47_ = lean_apply_2(v_inst_39_, lean_box(0), v_getCommSemiring_41_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___f_46_);
lean_ctor_set(v___x_44_, 0, v___x_47_);
v___x_49_ = v___x_44_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___f_46_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommSemiringOfMonadLift(lean_object* v_m_52_, lean_object* v_n_53_, lean_object* v_inst_54_, lean_object* v_inst_55_){
_start:
{
lean_object* v_getCommSemiring_56_; lean_object* v_modifyCommSemiring_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_66_; 
v_getCommSemiring_56_ = lean_ctor_get(v_inst_55_, 0);
v_modifyCommSemiring_57_ = lean_ctor_get(v_inst_55_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_inst_55_);
if (v_isSharedCheck_66_ == 0)
{
v___x_59_ = v_inst_55_;
v_isShared_60_ = v_isSharedCheck_66_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_modifyCommSemiring_57_);
lean_inc(v_getCommSemiring_56_);
lean_dec(v_inst_55_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_66_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
lean_inc(v_inst_54_);
v___f_61_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadCommSemiringOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_61_, 0, v_modifyCommSemiring_57_);
lean_closure_set(v___f_61_, 1, v_inst_54_);
v___x_62_ = lean_apply_2(v_inst_54_, lean_box(0), v_getCommSemiring_56_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___f_61_);
lean_ctor_set(v___x_59_, 0, v___x_62_);
v___x_64_ = v___x_59_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v___f_61_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__0(lean_object* v_f_67_, lean_object* v_s_68_){
_start:
{
lean_object* v_toSemiring_69_; lean_object* v_ringId_70_; lean_object* v_commSemiringInst_71_; lean_object* v_addRightCancelInst_x3f_72_; lean_object* v_toQFn_x3f_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_81_; 
v_toSemiring_69_ = lean_ctor_get(v_s_68_, 0);
v_ringId_70_ = lean_ctor_get(v_s_68_, 1);
v_commSemiringInst_71_ = lean_ctor_get(v_s_68_, 2);
v_addRightCancelInst_x3f_72_ = lean_ctor_get(v_s_68_, 3);
v_toQFn_x3f_73_ = lean_ctor_get(v_s_68_, 4);
v_isSharedCheck_81_ = !lean_is_exclusive(v_s_68_);
if (v_isSharedCheck_81_ == 0)
{
v___x_75_ = v_s_68_;
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_toQFn_x3f_73_);
lean_inc(v_addRightCancelInst_x3f_72_);
lean_inc(v_commSemiringInst_71_);
lean_inc(v_ringId_70_);
lean_inc(v_toSemiring_69_);
lean_dec(v_s_68_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_apply_1(v_f_67_, v_toSemiring_69_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_77_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v_ringId_70_);
lean_ctor_set(v_reuseFailAlloc_80_, 2, v_commSemiringInst_71_);
lean_ctor_set(v_reuseFailAlloc_80_, 3, v_addRightCancelInst_x3f_72_);
lean_ctor_set(v_reuseFailAlloc_80_, 4, v_toQFn_x3f_73_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__1(lean_object* v_modifyCommSemiring_82_, lean_object* v_f_83_){
_start:
{
lean_object* v___f_84_; lean_object* v___x_85_; 
v___f_84_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__0), 2, 1);
lean_closure_set(v___f_84_, 0, v_f_83_);
v___x_85_ = lean_apply_1(v_modifyCommSemiring_82_, v___f_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__2(lean_object* v_toPure_86_, lean_object* v_____do__lift_87_){
_start:
{
lean_object* v_toSemiring_88_; lean_object* v___x_89_; 
v_toSemiring_88_ = lean_ctor_get(v_____do__lift_87_, 0);
lean_inc_ref(v_toSemiring_88_);
lean_dec_ref(v_____do__lift_87_);
v___x_89_ = lean_apply_2(v_toPure_86_, lean_box(0), v_toSemiring_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg(lean_object* v_inst_90_, lean_object* v_inst_91_){
_start:
{
lean_object* v_toApplicative_92_; lean_object* v_toBind_93_; lean_object* v_getCommSemiring_94_; lean_object* v_modifyCommSemiring_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_106_; 
v_toApplicative_92_ = lean_ctor_get(v_inst_90_, 0);
lean_inc_ref(v_toApplicative_92_);
v_toBind_93_ = lean_ctor_get(v_inst_90_, 1);
lean_inc(v_toBind_93_);
lean_dec_ref(v_inst_90_);
v_getCommSemiring_94_ = lean_ctor_get(v_inst_91_, 0);
v_modifyCommSemiring_95_ = lean_ctor_get(v_inst_91_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_inst_91_);
if (v_isSharedCheck_106_ == 0)
{
v___x_97_ = v_inst_91_;
v_isShared_98_ = v_isSharedCheck_106_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_modifyCommSemiring_95_);
lean_inc(v_getCommSemiring_94_);
lean_dec(v_inst_91_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_106_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v_toPure_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v_toPure_99_ = lean_ctor_get(v_toApplicative_92_, 1);
lean_inc(v_toPure_99_);
lean_dec_ref(v_toApplicative_92_);
v___f_100_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__1), 2, 1);
lean_closure_set(v___f_100_, 0, v_modifyCommSemiring_95_);
v___f_101_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__2), 2, 1);
lean_closure_set(v___f_101_, 0, v_toPure_99_);
v___x_102_ = lean_apply_4(v_toBind_93_, lean_box(0), lean_box(0), v_getCommSemiring_94_, v___f_101_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 1, v___f_100_);
lean_ctor_set(v___x_97_, 0, v___x_102_);
v___x_104_ = v___x_97_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___f_100_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring(lean_object* v_m_107_, lean_object* v_inst_108_, lean_object* v_inst_109_){
_start:
{
lean_object* v_toApplicative_110_; lean_object* v_toBind_111_; lean_object* v_getCommSemiring_112_; lean_object* v_modifyCommSemiring_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_124_; 
v_toApplicative_110_ = lean_ctor_get(v_inst_108_, 0);
lean_inc_ref(v_toApplicative_110_);
v_toBind_111_ = lean_ctor_get(v_inst_108_, 1);
lean_inc(v_toBind_111_);
lean_dec_ref(v_inst_108_);
v_getCommSemiring_112_ = lean_ctor_get(v_inst_109_, 0);
v_modifyCommSemiring_113_ = lean_ctor_get(v_inst_109_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v_inst_109_);
if (v_isSharedCheck_124_ == 0)
{
v___x_115_ = v_inst_109_;
v_isShared_116_ = v_isSharedCheck_124_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_modifyCommSemiring_113_);
lean_inc(v_getCommSemiring_112_);
lean_dec(v_inst_109_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_124_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v_toPure_117_; lean_object* v___f_118_; lean_object* v___f_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v_toPure_117_ = lean_ctor_get(v_toApplicative_110_, 1);
lean_inc(v_toPure_117_);
lean_dec_ref(v_toApplicative_110_);
v___f_118_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__1), 2, 1);
lean_closure_set(v___f_118_, 0, v_modifyCommSemiring_113_);
v___f_119_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadSemiringOfMonadOfMonadCommSemiring___redArg___lam__2), 2, 1);
lean_closure_set(v___f_119_, 0, v_toPure_117_);
v___x_120_ = lean_apply_4(v_toBind_111_, lean_box(0), lean_box(0), v_getCommSemiring_112_, v___f_119_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___f_118_);
lean_ctor_set(v___x_115_, 0, v___x_120_);
v___x_122_ = v___x_115_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___f_118_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_MonadSemiring(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_MonadCanon(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_MonadSemiring(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_MonadSemiring(builtin);
}
#ifdef __cplusplus
}
#endif
