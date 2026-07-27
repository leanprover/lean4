// Lean compiler output
// Module: Lean.Meta.Sym.Arith.MonadRing
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0(lean_object* v_modifyRing_1_, lean_object* v_inst_2_, lean_object* v_f_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_modifyRing_1_, v_f_3_);
v___x_5_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg(lean_object* v_inst_6_, lean_object* v_inst_7_){
_start:
{
lean_object* v_getRing_8_; lean_object* v_modifyRing_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_18_; 
v_getRing_8_ = lean_ctor_get(v_inst_7_, 0);
v_modifyRing_9_ = lean_ctor_get(v_inst_7_, 1);
v_isSharedCheck_18_ = !lean_is_exclusive(v_inst_7_);
if (v_isSharedCheck_18_ == 0)
{
v___x_11_ = v_inst_7_;
v_isShared_12_ = v_isSharedCheck_18_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_modifyRing_9_);
lean_inc(v_getRing_8_);
lean_dec(v_inst_7_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_18_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_16_; 
lean_inc(v_inst_6_);
v___f_13_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_13_, 0, v_modifyRing_9_);
lean_closure_set(v___f_13_, 1, v_inst_6_);
v___x_14_ = lean_apply_2(v_inst_6_, lean_box(0), v_getRing_8_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift(lean_object* v_m_19_, lean_object* v_n_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v_getRing_23_; lean_object* v_modifyRing_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_33_; 
v_getRing_23_ = lean_ctor_get(v_inst_22_, 0);
v_modifyRing_24_ = lean_ctor_get(v_inst_22_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_inst_22_);
if (v_isSharedCheck_33_ == 0)
{
v___x_26_ = v_inst_22_;
v_isShared_27_ = v_isSharedCheck_33_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_modifyRing_24_);
lean_inc(v_getRing_23_);
lean_dec(v_inst_22_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_33_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___f_28_; lean_object* v___x_29_; lean_object* v___x_31_; 
lean_inc(v_inst_21_);
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_28_, 0, v_modifyRing_24_);
lean_closure_set(v___f_28_, 1, v_inst_21_);
v___x_29_ = lean_apply_2(v_inst_21_, lean_box(0), v_getRing_23_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg___lam__0(lean_object* v_modifyCommRing_34_, lean_object* v_inst_35_, lean_object* v_f_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_apply_1(v_modifyCommRing_34_, v_f_36_);
v___x_38_ = lean_apply_2(v_inst_35_, lean_box(0), v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg(lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v_getCommRing_41_; lean_object* v_modifyCommRing_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_51_; 
v_getCommRing_41_ = lean_ctor_get(v_inst_40_, 0);
v_modifyCommRing_42_ = lean_ctor_get(v_inst_40_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_inst_40_);
if (v_isSharedCheck_51_ == 0)
{
v___x_44_ = v_inst_40_;
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_modifyCommRing_42_);
lean_inc(v_getCommRing_41_);
lean_dec(v_inst_40_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_51_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___f_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
lean_inc(v_inst_39_);
v___f_46_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_46_, 0, v_modifyCommRing_42_);
lean_closure_set(v___f_46_, 1, v_inst_39_);
v___x_47_ = lean_apply_2(v_inst_39_, lean_box(0), v_getCommRing_41_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift(lean_object* v_m_52_, lean_object* v_n_53_, lean_object* v_inst_54_, lean_object* v_inst_55_){
_start:
{
lean_object* v_getCommRing_56_; lean_object* v_modifyCommRing_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_66_; 
v_getCommRing_56_ = lean_ctor_get(v_inst_55_, 0);
v_modifyCommRing_57_ = lean_ctor_get(v_inst_55_, 1);
v_isSharedCheck_66_ = !lean_is_exclusive(v_inst_55_);
if (v_isSharedCheck_66_ == 0)
{
v___x_59_ = v_inst_55_;
v_isShared_60_ = v_isSharedCheck_66_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_modifyCommRing_57_);
lean_inc(v_getCommRing_56_);
lean_dec(v_inst_55_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_66_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___f_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
lean_inc(v_inst_54_);
v___f_61_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadCommRingOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_61_, 0, v_modifyCommRing_57_);
lean_closure_set(v___f_61_, 1, v_inst_54_);
v___x_62_ = lean_apply_2(v_inst_54_, lean_box(0), v_getCommRing_56_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0(lean_object* v_f_67_, lean_object* v_s_68_){
_start:
{
lean_object* v_toRing_69_; lean_object* v_invFn_x3f_70_; lean_object* v_semiringId_x3f_71_; lean_object* v_commSemiringInst_72_; lean_object* v_commRingInst_73_; lean_object* v_noZeroDivInst_x3f_74_; lean_object* v_fieldInst_x3f_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_83_; 
v_toRing_69_ = lean_ctor_get(v_s_68_, 0);
v_invFn_x3f_70_ = lean_ctor_get(v_s_68_, 1);
v_semiringId_x3f_71_ = lean_ctor_get(v_s_68_, 2);
v_commSemiringInst_72_ = lean_ctor_get(v_s_68_, 3);
v_commRingInst_73_ = lean_ctor_get(v_s_68_, 4);
v_noZeroDivInst_x3f_74_ = lean_ctor_get(v_s_68_, 5);
v_fieldInst_x3f_75_ = lean_ctor_get(v_s_68_, 6);
v_isSharedCheck_83_ = !lean_is_exclusive(v_s_68_);
if (v_isSharedCheck_83_ == 0)
{
v___x_77_ = v_s_68_;
v_isShared_78_ = v_isSharedCheck_83_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_fieldInst_x3f_75_);
lean_inc(v_noZeroDivInst_x3f_74_);
lean_inc(v_commRingInst_73_);
lean_inc(v_commSemiringInst_72_);
lean_inc(v_semiringId_x3f_71_);
lean_inc(v_invFn_x3f_70_);
lean_inc(v_toRing_69_);
lean_dec(v_s_68_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_83_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = lean_apply_1(v_f_67_, v_toRing_69_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_79_);
v___x_81_ = v___x_77_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_79_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_invFn_x3f_70_);
lean_ctor_set(v_reuseFailAlloc_82_, 2, v_semiringId_x3f_71_);
lean_ctor_set(v_reuseFailAlloc_82_, 3, v_commSemiringInst_72_);
lean_ctor_set(v_reuseFailAlloc_82_, 4, v_commRingInst_73_);
lean_ctor_set(v_reuseFailAlloc_82_, 5, v_noZeroDivInst_x3f_74_);
lean_ctor_set(v_reuseFailAlloc_82_, 6, v_fieldInst_x3f_75_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1(lean_object* v_modifyCommRing_84_, lean_object* v_f_85_){
_start:
{
lean_object* v___f_86_; lean_object* v___x_87_; 
v___f_86_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_86_, 0, v_f_85_);
v___x_87_ = lean_apply_1(v_modifyCommRing_84_, v___f_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(lean_object* v_toPure_88_, lean_object* v_____do__lift_89_){
_start:
{
lean_object* v_toRing_90_; lean_object* v___x_91_; 
v_toRing_90_ = lean_ctor_get(v_____do__lift_89_, 0);
lean_inc_ref(v_toRing_90_);
lean_dec_ref(v_____do__lift_89_);
v___x_91_ = lean_apply_2(v_toPure_88_, lean_box(0), v_toRing_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg(lean_object* v_inst_92_, lean_object* v_inst_93_){
_start:
{
lean_object* v_toApplicative_94_; lean_object* v_toBind_95_; lean_object* v_getCommRing_96_; lean_object* v_modifyCommRing_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_108_; 
v_toApplicative_94_ = lean_ctor_get(v_inst_92_, 0);
lean_inc_ref(v_toApplicative_94_);
v_toBind_95_ = lean_ctor_get(v_inst_92_, 1);
lean_inc(v_toBind_95_);
lean_dec_ref(v_inst_92_);
v_getCommRing_96_ = lean_ctor_get(v_inst_93_, 0);
v_modifyCommRing_97_ = lean_ctor_get(v_inst_93_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_inst_93_);
if (v_isSharedCheck_108_ == 0)
{
v___x_99_ = v_inst_93_;
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_modifyCommRing_97_);
lean_inc(v_getCommRing_96_);
lean_dec(v_inst_93_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_108_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v_toPure_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v_toPure_101_ = lean_ctor_get(v_toApplicative_94_, 1);
lean_inc(v_toPure_101_);
lean_dec_ref(v_toApplicative_94_);
v___f_102_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_102_, 0, v_modifyCommRing_97_);
v___f_103_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_103_, 0, v_toPure_101_);
v___x_104_ = lean_apply_4(v_toBind_95_, lean_box(0), lean_box(0), v_getCommRing_96_, v___f_103_);
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v___f_102_);
lean_ctor_set(v___x_99_, 0, v___x_104_);
v___x_106_ = v___x_99_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___f_102_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing(lean_object* v_m_109_, lean_object* v_inst_110_, lean_object* v_inst_111_){
_start:
{
lean_object* v_toApplicative_112_; lean_object* v_toBind_113_; lean_object* v_getCommRing_114_; lean_object* v_modifyCommRing_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_126_; 
v_toApplicative_112_ = lean_ctor_get(v_inst_110_, 0);
lean_inc_ref(v_toApplicative_112_);
v_toBind_113_ = lean_ctor_get(v_inst_110_, 1);
lean_inc(v_toBind_113_);
lean_dec_ref(v_inst_110_);
v_getCommRing_114_ = lean_ctor_get(v_inst_111_, 0);
v_modifyCommRing_115_ = lean_ctor_get(v_inst_111_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_inst_111_);
if (v_isSharedCheck_126_ == 0)
{
v___x_117_ = v_inst_111_;
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_modifyCommRing_115_);
lean_inc(v_getCommRing_114_);
lean_dec(v_inst_111_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_126_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_toPure_119_; lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v_toPure_119_ = lean_ctor_get(v_toApplicative_112_, 1);
lean_inc(v_toPure_119_);
lean_dec_ref(v_toApplicative_112_);
v___f_120_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_120_, 0, v_modifyCommRing_115_);
v___f_121_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Arith_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_121_, 0, v_toPure_119_);
v___x_122_ = lean_apply_4(v_toBind_113_, lean_box(0), lean_box(0), v_getCommRing_114_, v___f_121_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___f_120_);
lean_ctor_set(v___x_117_, 0, v___x_122_);
v___x_124_ = v___x_117_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___f_120_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_MonadRing(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_MonadCanon(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_MonadRing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_MonadRing(builtin);
}
#ifdef __cplusplus
}
#endif
