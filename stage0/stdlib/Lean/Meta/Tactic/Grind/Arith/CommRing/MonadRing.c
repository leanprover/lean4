// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.MonadRing
// Imports: public import Lean.Meta.Sym.Arith.MonadCanon public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0(lean_object* v_modifyRing_1_, lean_object* v_inst_2_, lean_object* v_f_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_4_ = lean_apply_1(v_modifyRing_1_, v_f_3_);
v___x_5_ = lean_apply_2(v_inst_2_, lean_box(0), v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg(lean_object* v_inst_6_, lean_object* v_inst_7_){
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
v___f_13_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0), 3, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift(lean_object* v_m_19_, lean_object* v_n_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
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
v___f_28_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadLift___redArg___lam__0), 3, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0(lean_object* v_modifyCommRing_34_, lean_object* v_inst_35_, lean_object* v_f_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_37_ = lean_apply_1(v_modifyCommRing_34_, v_f_36_);
v___x_38_ = lean_apply_2(v_inst_35_, lean_box(0), v___x_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg(lean_object* v_inst_39_, lean_object* v_inst_40_){
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
v___f_46_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0), 3, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift(lean_object* v_m_52_, lean_object* v_n_53_, lean_object* v_inst_54_, lean_object* v_inst_55_){
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
v___f_61_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadCommRingOfMonadLift___redArg___lam__0), 3, 2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0(lean_object* v_f_67_, lean_object* v_s_68_){
_start:
{
lean_object* v_toRing_69_; lean_object* v_invFn_x3f_70_; lean_object* v_semiringId_x3f_71_; lean_object* v_commSemiringInst_72_; lean_object* v_commRingInst_73_; lean_object* v_noZeroDivInst_x3f_74_; lean_object* v_fieldInst_x3f_75_; lean_object* v_powIdentityInst_x3f_76_; lean_object* v_denoteEntries_77_; lean_object* v_nextId_78_; lean_object* v_steps_79_; lean_object* v_queue_80_; lean_object* v_basis_81_; lean_object* v_diseqs_82_; uint8_t v_recheck_83_; lean_object* v_invSet_84_; lean_object* v_powIdentityVarCount_85_; lean_object* v_numEq0_x3f_86_; uint8_t v_numEq0Updated_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_95_; 
v_toRing_69_ = lean_ctor_get(v_s_68_, 0);
v_invFn_x3f_70_ = lean_ctor_get(v_s_68_, 1);
v_semiringId_x3f_71_ = lean_ctor_get(v_s_68_, 2);
v_commSemiringInst_72_ = lean_ctor_get(v_s_68_, 3);
v_commRingInst_73_ = lean_ctor_get(v_s_68_, 4);
v_noZeroDivInst_x3f_74_ = lean_ctor_get(v_s_68_, 5);
v_fieldInst_x3f_75_ = lean_ctor_get(v_s_68_, 6);
v_powIdentityInst_x3f_76_ = lean_ctor_get(v_s_68_, 7);
v_denoteEntries_77_ = lean_ctor_get(v_s_68_, 8);
v_nextId_78_ = lean_ctor_get(v_s_68_, 9);
v_steps_79_ = lean_ctor_get(v_s_68_, 10);
v_queue_80_ = lean_ctor_get(v_s_68_, 11);
v_basis_81_ = lean_ctor_get(v_s_68_, 12);
v_diseqs_82_ = lean_ctor_get(v_s_68_, 13);
v_recheck_83_ = lean_ctor_get_uint8(v_s_68_, sizeof(void*)*17);
v_invSet_84_ = lean_ctor_get(v_s_68_, 14);
v_powIdentityVarCount_85_ = lean_ctor_get(v_s_68_, 15);
v_numEq0_x3f_86_ = lean_ctor_get(v_s_68_, 16);
v_numEq0Updated_87_ = lean_ctor_get_uint8(v_s_68_, sizeof(void*)*17 + 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v_s_68_);
if (v_isSharedCheck_95_ == 0)
{
v___x_89_ = v_s_68_;
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_numEq0_x3f_86_);
lean_inc(v_powIdentityVarCount_85_);
lean_inc(v_invSet_84_);
lean_inc(v_diseqs_82_);
lean_inc(v_basis_81_);
lean_inc(v_queue_80_);
lean_inc(v_steps_79_);
lean_inc(v_nextId_78_);
lean_inc(v_denoteEntries_77_);
lean_inc(v_powIdentityInst_x3f_76_);
lean_inc(v_fieldInst_x3f_75_);
lean_inc(v_noZeroDivInst_x3f_74_);
lean_inc(v_commRingInst_73_);
lean_inc(v_commSemiringInst_72_);
lean_inc(v_semiringId_x3f_71_);
lean_inc(v_invFn_x3f_70_);
lean_inc(v_toRing_69_);
lean_dec(v_s_68_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_95_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_91_ = lean_apply_1(v_f_67_, v_toRing_69_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_93_ = v___x_89_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 17, 2);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_invFn_x3f_70_);
lean_ctor_set(v_reuseFailAlloc_94_, 2, v_semiringId_x3f_71_);
lean_ctor_set(v_reuseFailAlloc_94_, 3, v_commSemiringInst_72_);
lean_ctor_set(v_reuseFailAlloc_94_, 4, v_commRingInst_73_);
lean_ctor_set(v_reuseFailAlloc_94_, 5, v_noZeroDivInst_x3f_74_);
lean_ctor_set(v_reuseFailAlloc_94_, 6, v_fieldInst_x3f_75_);
lean_ctor_set(v_reuseFailAlloc_94_, 7, v_powIdentityInst_x3f_76_);
lean_ctor_set(v_reuseFailAlloc_94_, 8, v_denoteEntries_77_);
lean_ctor_set(v_reuseFailAlloc_94_, 9, v_nextId_78_);
lean_ctor_set(v_reuseFailAlloc_94_, 10, v_steps_79_);
lean_ctor_set(v_reuseFailAlloc_94_, 11, v_queue_80_);
lean_ctor_set(v_reuseFailAlloc_94_, 12, v_basis_81_);
lean_ctor_set(v_reuseFailAlloc_94_, 13, v_diseqs_82_);
lean_ctor_set(v_reuseFailAlloc_94_, 14, v_invSet_84_);
lean_ctor_set(v_reuseFailAlloc_94_, 15, v_powIdentityVarCount_85_);
lean_ctor_set(v_reuseFailAlloc_94_, 16, v_numEq0_x3f_86_);
lean_ctor_set_uint8(v_reuseFailAlloc_94_, sizeof(void*)*17, v_recheck_83_);
lean_ctor_set_uint8(v_reuseFailAlloc_94_, sizeof(void*)*17 + 1, v_numEq0Updated_87_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1(lean_object* v_modifyCommRing_96_, lean_object* v_f_97_){
_start:
{
lean_object* v___f_98_; lean_object* v___x_99_; 
v___f_98_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__0), 2, 1);
lean_closure_set(v___f_98_, 0, v_f_97_);
v___x_99_ = lean_apply_1(v_modifyCommRing_96_, v___f_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2(lean_object* v_toPure_100_, lean_object* v_____do__lift_101_){
_start:
{
lean_object* v_toRing_102_; lean_object* v___x_103_; 
v_toRing_102_ = lean_ctor_get(v_____do__lift_101_, 0);
lean_inc_ref(v_toRing_102_);
lean_dec_ref(v_____do__lift_101_);
v___x_103_ = lean_apply_2(v_toPure_100_, lean_box(0), v_toRing_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg(lean_object* v_inst_104_, lean_object* v_inst_105_){
_start:
{
lean_object* v_toApplicative_106_; lean_object* v_toBind_107_; lean_object* v_getCommRing_108_; lean_object* v_modifyCommRing_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_120_; 
v_toApplicative_106_ = lean_ctor_get(v_inst_104_, 0);
lean_inc_ref(v_toApplicative_106_);
v_toBind_107_ = lean_ctor_get(v_inst_104_, 1);
lean_inc(v_toBind_107_);
lean_dec_ref(v_inst_104_);
v_getCommRing_108_ = lean_ctor_get(v_inst_105_, 0);
v_modifyCommRing_109_ = lean_ctor_get(v_inst_105_, 1);
v_isSharedCheck_120_ = !lean_is_exclusive(v_inst_105_);
if (v_isSharedCheck_120_ == 0)
{
v___x_111_ = v_inst_105_;
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_modifyCommRing_109_);
lean_inc(v_getCommRing_108_);
lean_dec(v_inst_105_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_120_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_toPure_113_; lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___x_118_; 
v_toPure_113_ = lean_ctor_get(v_toApplicative_106_, 1);
lean_inc(v_toPure_113_);
lean_dec_ref(v_toApplicative_106_);
v___f_114_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_114_, 0, v_modifyCommRing_109_);
v___f_115_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_115_, 0, v_toPure_113_);
v___x_116_ = lean_apply_4(v_toBind_107_, lean_box(0), lean_box(0), v_getCommRing_108_, v___f_115_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 1, v___f_114_);
lean_ctor_set(v___x_111_, 0, v___x_116_);
v___x_118_ = v___x_111_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___f_114_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing(lean_object* v_m_121_, lean_object* v_inst_122_, lean_object* v_inst_123_){
_start:
{
lean_object* v_toApplicative_124_; lean_object* v_toBind_125_; lean_object* v_getCommRing_126_; lean_object* v_modifyCommRing_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_138_; 
v_toApplicative_124_ = lean_ctor_get(v_inst_122_, 0);
lean_inc_ref(v_toApplicative_124_);
v_toBind_125_ = lean_ctor_get(v_inst_122_, 1);
lean_inc(v_toBind_125_);
lean_dec_ref(v_inst_122_);
v_getCommRing_126_ = lean_ctor_get(v_inst_123_, 0);
v_modifyCommRing_127_ = lean_ctor_get(v_inst_123_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_inst_123_);
if (v_isSharedCheck_138_ == 0)
{
v___x_129_ = v_inst_123_;
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_modifyCommRing_127_);
lean_inc(v_getCommRing_126_);
lean_dec(v_inst_123_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_138_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v_toPure_131_; lean_object* v___f_132_; lean_object* v___f_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v_toPure_131_ = lean_ctor_get(v_toApplicative_124_, 1);
lean_inc(v_toPure_131_);
lean_dec_ref(v_toApplicative_124_);
v___f_132_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__1), 2, 1);
lean_closure_set(v___f_132_, 0, v_modifyCommRing_127_);
v___f_133_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingOfMonadOfMonadCommRing___redArg___lam__2), 2, 1);
lean_closure_set(v___f_133_, 0, v_toPure_131_);
v___x_134_ = lean_apply_4(v_toBind_125_, lean_box(0), lean_box(0), v_getCommRing_126_, v___f_133_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___f_132_);
lean_ctor_set(v___x_129_, 0, v___x_134_);
v___x_136_ = v___x_129_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___f_132_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Arith_MonadCanon(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Arith_MonadCanon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_MonadRing(builtin);
}
#ifdef __cplusplus
}
#endif
