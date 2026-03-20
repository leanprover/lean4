// Lean compiler output
// Module: Std.Sat.AIG.CachedGates
// Imports: public import Std.Sat.AIG.CachedLemmas
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
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___redArg(lean_object* v_aig_1_, lean_object* v_gate_2_){
_start:
{
uint8_t v_invert_3_; 
v_invert_3_ = lean_ctor_get_uint8(v_gate_2_, sizeof(void*)*1);
if (v_invert_3_ == 0)
{
lean_object* v_gate_4_; lean_object* v___x_6_; uint8_t v_isShared_7_; uint8_t v_isSharedCheck_13_; 
v_gate_4_ = lean_ctor_get(v_gate_2_, 0);
v_isSharedCheck_13_ = !lean_is_exclusive(v_gate_2_);
if (v_isSharedCheck_13_ == 0)
{
v___x_6_ = v_gate_2_;
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
else
{
lean_inc(v_gate_4_);
lean_dec(v_gate_2_);
v___x_6_ = lean_box(0);
v_isShared_7_ = v_isSharedCheck_13_;
goto v_resetjp_5_;
}
v_resetjp_5_:
{
uint8_t v___x_8_; lean_object* v___x_10_; 
v___x_8_ = 1;
if (v_isShared_7_ == 0)
{
v___x_10_ = v___x_6_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_12_; 
v_reuseFailAlloc_12_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_12_, 0, v_gate_4_);
v___x_10_ = v_reuseFailAlloc_12_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
lean_object* v___x_11_; 
lean_ctor_set_uint8(v___x_10_, sizeof(void*)*1, v___x_8_);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v_aig_1_);
lean_ctor_set(v___x_11_, 1, v___x_10_);
return v___x_11_;
}
}
}
else
{
lean_object* v_gate_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_23_; 
v_gate_14_ = lean_ctor_get(v_gate_2_, 0);
v_isSharedCheck_23_ = !lean_is_exclusive(v_gate_2_);
if (v_isSharedCheck_23_ == 0)
{
v___x_16_ = v_gate_2_;
v_isShared_17_ = v_isSharedCheck_23_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_gate_14_);
lean_dec(v_gate_2_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_23_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
uint8_t v___x_18_; lean_object* v___x_20_; 
v___x_18_ = 0;
if (v_isShared_17_ == 0)
{
v___x_20_ = v___x_16_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_gate_14_);
v___x_20_ = v_reuseFailAlloc_22_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_21_; 
lean_ctor_set_uint8(v___x_20_, sizeof(void*)*1, v___x_18_);
v___x_21_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_21_, 0, v_aig_1_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
return v___x_21_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached(lean_object* v_00_u03b1_24_, lean_object* v_inst_25_, lean_object* v_inst_26_, lean_object* v_aig_27_, lean_object* v_gate_28_){
_start:
{
uint8_t v_invert_29_; 
v_invert_29_ = lean_ctor_get_uint8(v_gate_28_, sizeof(void*)*1);
if (v_invert_29_ == 0)
{
lean_object* v_gate_30_; lean_object* v___x_32_; uint8_t v_isShared_33_; uint8_t v_isSharedCheck_39_; 
v_gate_30_ = lean_ctor_get(v_gate_28_, 0);
v_isSharedCheck_39_ = !lean_is_exclusive(v_gate_28_);
if (v_isSharedCheck_39_ == 0)
{
v___x_32_ = v_gate_28_;
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
else
{
lean_inc(v_gate_30_);
lean_dec(v_gate_28_);
v___x_32_ = lean_box(0);
v_isShared_33_ = v_isSharedCheck_39_;
goto v_resetjp_31_;
}
v_resetjp_31_:
{
uint8_t v___x_34_; lean_object* v___x_36_; 
v___x_34_ = 1;
if (v_isShared_33_ == 0)
{
v___x_36_ = v___x_32_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_38_; 
v_reuseFailAlloc_38_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_38_, 0, v_gate_30_);
v___x_36_ = v_reuseFailAlloc_38_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
lean_object* v___x_37_; 
lean_ctor_set_uint8(v___x_36_, sizeof(void*)*1, v___x_34_);
v___x_37_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_37_, 0, v_aig_27_);
lean_ctor_set(v___x_37_, 1, v___x_36_);
return v___x_37_;
}
}
}
else
{
lean_object* v_gate_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_49_; 
v_gate_40_ = lean_ctor_get(v_gate_28_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v_gate_28_);
if (v_isSharedCheck_49_ == 0)
{
v___x_42_ = v_gate_28_;
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_gate_40_);
lean_dec(v_gate_28_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_49_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
uint8_t v___x_44_; lean_object* v___x_46_; 
v___x_44_ = 0;
if (v_isShared_43_ == 0)
{
v___x_46_ = v___x_42_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_gate_40_);
v___x_46_ = v_reuseFailAlloc_48_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
lean_object* v___x_47_; 
lean_ctor_set_uint8(v___x_46_, sizeof(void*)*1, v___x_44_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_aig_27_);
lean_ctor_set(v___x_47_, 1, v___x_46_);
return v___x_47_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkNotCached___boxed(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_aig_53_, lean_object* v_gate_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_Sat_AIG_mkNotCached(v_00_u03b1_50_, v_inst_51_, v_inst_52_, v_aig_53_, v_gate_54_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_51_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached___redArg(lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_aig_58_, lean_object* v_input_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_56_, v_inst_57_, v_aig_58_, v_input_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkAndCached(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_aig_64_, lean_object* v_input_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_62_, v_inst_63_, v_aig_64_, v_input_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object* v_inst_67_, lean_object* v_inst_68_, lean_object* v_aig_69_, lean_object* v_input_70_){
_start:
{
lean_object* v___y_72_; lean_object* v_lhs_112_; lean_object* v_rhs_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_163_; 
v_lhs_112_ = lean_ctor_get(v_input_70_, 0);
v_rhs_113_ = lean_ctor_get(v_input_70_, 1);
v_isSharedCheck_163_ = !lean_is_exclusive(v_input_70_);
if (v_isSharedCheck_163_ == 0)
{
v___x_115_ = v_input_70_;
v_isShared_116_ = v_isSharedCheck_163_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_rhs_113_);
lean_inc(v_lhs_112_);
lean_dec(v_input_70_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_163_;
goto v_resetjp_114_;
}
v___jp_71_:
{
lean_object* v_res_73_; lean_object* v_ref_74_; uint8_t v_invert_75_; 
v_res_73_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_67_, v_inst_68_, v_aig_69_, v___y_72_);
v_ref_74_ = lean_ctor_get(v_res_73_, 1);
lean_inc_ref(v_ref_74_);
v_invert_75_ = lean_ctor_get_uint8(v_ref_74_, sizeof(void*)*1);
if (v_invert_75_ == 0)
{
lean_object* v_aig_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_92_; 
v_aig_76_ = lean_ctor_get(v_res_73_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v_res_73_);
if (v_isSharedCheck_92_ == 0)
{
lean_object* v_unused_93_; 
v_unused_93_ = lean_ctor_get(v_res_73_, 1);
lean_dec(v_unused_93_);
v___x_78_ = v_res_73_;
v_isShared_79_ = v_isSharedCheck_92_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_aig_76_);
lean_dec(v_res_73_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_92_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v_gate_80_; lean_object* v___x_82_; uint8_t v_isShared_83_; uint8_t v_isSharedCheck_91_; 
v_gate_80_ = lean_ctor_get(v_ref_74_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v_ref_74_);
if (v_isSharedCheck_91_ == 0)
{
v___x_82_ = v_ref_74_;
v_isShared_83_ = v_isSharedCheck_91_;
goto v_resetjp_81_;
}
else
{
lean_inc(v_gate_80_);
lean_dec(v_ref_74_);
v___x_82_ = lean_box(0);
v_isShared_83_ = v_isSharedCheck_91_;
goto v_resetjp_81_;
}
v_resetjp_81_:
{
uint8_t v___x_84_; lean_object* v___x_86_; 
v___x_84_ = 1;
if (v_isShared_83_ == 0)
{
v___x_86_ = v___x_82_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_gate_80_);
v___x_86_ = v_reuseFailAlloc_90_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_88_; 
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_84_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_86_);
v___x_88_ = v___x_78_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_aig_76_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
else
{
lean_object* v_aig_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_110_; 
v_aig_94_ = lean_ctor_get(v_res_73_, 0);
v_isSharedCheck_110_ = !lean_is_exclusive(v_res_73_);
if (v_isSharedCheck_110_ == 0)
{
lean_object* v_unused_111_; 
v_unused_111_ = lean_ctor_get(v_res_73_, 1);
lean_dec(v_unused_111_);
v___x_96_ = v_res_73_;
v_isShared_97_ = v_isSharedCheck_110_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_aig_94_);
lean_dec(v_res_73_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_110_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v_gate_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_109_; 
v_gate_98_ = lean_ctor_get(v_ref_74_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v_ref_74_);
if (v_isSharedCheck_109_ == 0)
{
v___x_100_ = v_ref_74_;
v_isShared_101_ = v_isSharedCheck_109_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_gate_98_);
lean_dec(v_ref_74_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_109_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
uint8_t v___x_102_; lean_object* v___x_104_; 
v___x_102_ = 0;
if (v_isShared_101_ == 0)
{
v___x_104_ = v___x_100_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_gate_98_);
v___x_104_ = v_reuseFailAlloc_108_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_106_; 
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*1, v___x_102_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 1, v___x_104_);
v___x_106_ = v___x_96_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_aig_94_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_104_);
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
}
}
v_resetjp_114_:
{
lean_object* v___y_118_; uint8_t v_invert_144_; 
v_invert_144_ = lean_ctor_get_uint8(v_lhs_112_, sizeof(void*)*1);
if (v_invert_144_ == 0)
{
lean_object* v_gate_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_153_; 
v_gate_145_ = lean_ctor_get(v_lhs_112_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v_lhs_112_);
if (v_isSharedCheck_153_ == 0)
{
v___x_147_ = v_lhs_112_;
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_gate_145_);
lean_dec(v_lhs_112_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_153_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
uint8_t v___x_149_; lean_object* v___x_151_; 
v___x_149_ = 1;
if (v_isShared_148_ == 0)
{
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_gate_145_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_ctor_set_uint8(v___x_151_, sizeof(void*)*1, v___x_149_);
v___y_118_ = v___x_151_;
goto v___jp_117_;
}
}
}
else
{
lean_object* v_gate_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_162_; 
v_gate_154_ = lean_ctor_get(v_lhs_112_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v_lhs_112_);
if (v_isSharedCheck_162_ == 0)
{
v___x_156_ = v_lhs_112_;
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_gate_154_);
lean_dec(v_lhs_112_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_162_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
uint8_t v___x_158_; lean_object* v___x_160_; 
v___x_158_ = 0;
if (v_isShared_157_ == 0)
{
v___x_160_ = v___x_156_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_gate_154_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
lean_ctor_set_uint8(v___x_160_, sizeof(void*)*1, v___x_158_);
v___y_118_ = v___x_160_;
goto v___jp_117_;
}
}
}
v___jp_117_:
{
uint8_t v_invert_119_; 
v_invert_119_ = lean_ctor_get_uint8(v_rhs_113_, sizeof(void*)*1);
if (v_invert_119_ == 0)
{
lean_object* v_gate_120_; lean_object* v___x_122_; uint8_t v_isShared_123_; uint8_t v_isSharedCheck_131_; 
v_gate_120_ = lean_ctor_get(v_rhs_113_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v_rhs_113_);
if (v_isSharedCheck_131_ == 0)
{
v___x_122_ = v_rhs_113_;
v_isShared_123_ = v_isSharedCheck_131_;
goto v_resetjp_121_;
}
else
{
lean_inc(v_gate_120_);
lean_dec(v_rhs_113_);
v___x_122_ = lean_box(0);
v_isShared_123_ = v_isSharedCheck_131_;
goto v_resetjp_121_;
}
v_resetjp_121_:
{
uint8_t v___x_124_; lean_object* v___x_126_; 
v___x_124_ = 1;
if (v_isShared_123_ == 0)
{
v___x_126_ = v___x_122_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_gate_120_);
v___x_126_ = v_reuseFailAlloc_130_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
lean_object* v___x_128_; 
lean_ctor_set_uint8(v___x_126_, sizeof(void*)*1, v___x_124_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_126_);
lean_ctor_set(v___x_115_, 0, v___y_118_);
v___x_128_ = v___x_115_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v___y_118_);
lean_ctor_set(v_reuseFailAlloc_129_, 1, v___x_126_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
v___y_72_ = v___x_128_;
goto v___jp_71_;
}
}
}
}
else
{
lean_object* v_gate_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_143_; 
v_gate_132_ = lean_ctor_get(v_rhs_113_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v_rhs_113_);
if (v_isSharedCheck_143_ == 0)
{
v___x_134_ = v_rhs_113_;
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_gate_132_);
lean_dec(v_rhs_113_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_143_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
uint8_t v___x_136_; lean_object* v___x_138_; 
v___x_136_ = 0;
if (v_isShared_135_ == 0)
{
v___x_138_ = v___x_134_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_gate_132_);
v___x_138_ = v_reuseFailAlloc_142_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_140_; 
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_136_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_138_);
lean_ctor_set(v___x_115_, 0, v___y_118_);
v___x_140_ = v___x_115_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___y_118_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_138_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
v___y_72_ = v___x_140_;
goto v___jp_71_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached(lean_object* v_00_u03b1_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_aig_167_, lean_object* v_input_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Std_Sat_AIG_mkOrCached___redArg(v_inst_165_, v_inst_166_, v_aig_167_, v_input_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object* v_inst_170_, lean_object* v_inst_171_, lean_object* v_aig_172_, lean_object* v_input_173_){
_start:
{
lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_183_; lean_object* v_res_203_; lean_object* v_aig_204_; lean_object* v_ref_205_; lean_object* v___y_207_; lean_object* v_lhs_232_; lean_object* v_rhs_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_273_; 
lean_inc_ref(v_input_173_);
lean_inc_ref(v_inst_171_);
lean_inc_ref(v_inst_170_);
v_res_203_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_170_, v_inst_171_, v_aig_172_, v_input_173_);
v_aig_204_ = lean_ctor_get(v_res_203_, 0);
lean_inc_ref(v_aig_204_);
v_ref_205_ = lean_ctor_get(v_res_203_, 1);
lean_inc_ref(v_ref_205_);
lean_dec_ref(v_res_203_);
v_lhs_232_ = lean_ctor_get(v_input_173_, 0);
v_rhs_233_ = lean_ctor_get(v_input_173_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_input_173_);
if (v_isSharedCheck_273_ == 0)
{
v___x_235_ = v_input_173_;
v_isShared_236_ = v_isSharedCheck_273_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_rhs_233_);
lean_inc(v_lhs_232_);
lean_dec(v_input_173_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_273_;
goto v_resetjp_234_;
}
v___jp_174_:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_178_, 0, v___y_176_);
lean_ctor_set(v___x_178_, 1, v___y_177_);
v___x_179_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_170_, v_inst_171_, v___y_175_, v___x_178_);
return v___x_179_;
}
v___jp_180_:
{
uint8_t v_invert_184_; 
v_invert_184_ = lean_ctor_get_uint8(v___y_181_, sizeof(void*)*1);
if (v_invert_184_ == 0)
{
lean_object* v_gate_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_193_; 
v_gate_185_ = lean_ctor_get(v___y_181_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___y_181_);
if (v_isSharedCheck_193_ == 0)
{
v___x_187_ = v___y_181_;
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_gate_185_);
lean_dec(v___y_181_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_193_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
uint8_t v___x_189_; lean_object* v___x_191_; 
v___x_189_ = 1;
if (v_isShared_188_ == 0)
{
v___x_191_ = v___x_187_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_gate_185_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_ctor_set_uint8(v___x_191_, sizeof(void*)*1, v___x_189_);
v___y_175_ = v___y_182_;
v___y_176_ = v___y_183_;
v___y_177_ = v___x_191_;
goto v___jp_174_;
}
}
}
else
{
lean_object* v_gate_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_202_; 
v_gate_194_ = lean_ctor_get(v___y_181_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___y_181_);
if (v_isSharedCheck_202_ == 0)
{
v___x_196_ = v___y_181_;
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_gate_194_);
lean_dec(v___y_181_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
uint8_t v___x_198_; lean_object* v___x_200_; 
v___x_198_ = 0;
if (v_isShared_197_ == 0)
{
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_gate_194_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_ctor_set_uint8(v___x_200_, sizeof(void*)*1, v___x_198_);
v___y_175_ = v___y_182_;
v___y_176_ = v___y_183_;
v___y_177_ = v___x_200_;
goto v___jp_174_;
}
}
}
}
v___jp_206_:
{
lean_object* v_res_208_; uint8_t v_invert_209_; 
lean_inc_ref(v_inst_171_);
lean_inc_ref(v_inst_170_);
v_res_208_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_170_, v_inst_171_, v_aig_204_, v___y_207_);
v_invert_209_ = lean_ctor_get_uint8(v_ref_205_, sizeof(void*)*1);
if (v_invert_209_ == 0)
{
lean_object* v_aig_210_; lean_object* v_ref_211_; lean_object* v_gate_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_220_; 
v_aig_210_ = lean_ctor_get(v_res_208_, 0);
lean_inc_ref(v_aig_210_);
v_ref_211_ = lean_ctor_get(v_res_208_, 1);
lean_inc_ref(v_ref_211_);
lean_dec_ref(v_res_208_);
v_gate_212_ = lean_ctor_get(v_ref_205_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v_ref_205_);
if (v_isSharedCheck_220_ == 0)
{
v___x_214_ = v_ref_205_;
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_gate_212_);
lean_dec(v_ref_205_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_220_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
uint8_t v___x_216_; lean_object* v___x_218_; 
v___x_216_ = 1;
if (v_isShared_215_ == 0)
{
v___x_218_ = v___x_214_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_gate_212_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
lean_ctor_set_uint8(v___x_218_, sizeof(void*)*1, v___x_216_);
v___y_181_ = v_ref_211_;
v___y_182_ = v_aig_210_;
v___y_183_ = v___x_218_;
goto v___jp_180_;
}
}
}
else
{
lean_object* v_aig_221_; lean_object* v_ref_222_; lean_object* v_gate_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_231_; 
v_aig_221_ = lean_ctor_get(v_res_208_, 0);
lean_inc_ref(v_aig_221_);
v_ref_222_ = lean_ctor_get(v_res_208_, 1);
lean_inc_ref(v_ref_222_);
lean_dec_ref(v_res_208_);
v_gate_223_ = lean_ctor_get(v_ref_205_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v_ref_205_);
if (v_isSharedCheck_231_ == 0)
{
v___x_225_ = v_ref_205_;
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_gate_223_);
lean_dec(v_ref_205_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint8_t v___x_227_; lean_object* v___x_229_; 
v___x_227_ = 0;
if (v_isShared_226_ == 0)
{
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_gate_223_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*1, v___x_227_);
v___y_181_ = v_ref_222_;
v___y_182_ = v_aig_221_;
v___y_183_ = v___x_229_;
goto v___jp_180_;
}
}
}
}
v_resetjp_234_:
{
lean_object* v_gate_237_; uint8_t v_invert_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_272_; 
v_gate_237_ = lean_ctor_get(v_lhs_232_, 0);
v_invert_238_ = lean_ctor_get_uint8(v_lhs_232_, sizeof(void*)*1);
v_isSharedCheck_272_ = !lean_is_exclusive(v_lhs_232_);
if (v_isSharedCheck_272_ == 0)
{
v___x_240_ = v_lhs_232_;
v_isShared_241_ = v_isSharedCheck_272_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_gate_237_);
lean_dec(v_lhs_232_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_272_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v_gate_242_; uint8_t v_invert_243_; lean_object* v___x_245_; uint8_t v_isShared_246_; uint8_t v_isSharedCheck_271_; 
v_gate_242_ = lean_ctor_get(v_rhs_233_, 0);
v_invert_243_ = lean_ctor_get_uint8(v_rhs_233_, sizeof(void*)*1);
v_isSharedCheck_271_ = !lean_is_exclusive(v_rhs_233_);
if (v_isSharedCheck_271_ == 0)
{
v___x_245_ = v_rhs_233_;
v_isShared_246_ = v_isSharedCheck_271_;
goto v_resetjp_244_;
}
else
{
lean_inc(v_gate_242_);
lean_dec(v_rhs_233_);
v___x_245_ = lean_box(0);
v_isShared_246_ = v_isSharedCheck_271_;
goto v_resetjp_244_;
}
v_resetjp_244_:
{
lean_object* v___y_248_; 
if (v_invert_238_ == 0)
{
uint8_t v___x_263_; lean_object* v___x_265_; 
v___x_263_ = 1;
if (v_isShared_241_ == 0)
{
v___x_265_ = v___x_240_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_gate_237_);
v___x_265_ = v_reuseFailAlloc_266_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_263_);
v___y_248_ = v___x_265_;
goto v___jp_247_;
}
}
else
{
uint8_t v___x_267_; lean_object* v___x_269_; 
v___x_267_ = 0;
if (v_isShared_241_ == 0)
{
v___x_269_ = v___x_240_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_gate_237_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_ctor_set_uint8(v___x_269_, sizeof(void*)*1, v___x_267_);
v___y_248_ = v___x_269_;
goto v___jp_247_;
}
}
v___jp_247_:
{
if (v_invert_243_ == 0)
{
uint8_t v___x_249_; lean_object* v___x_251_; 
v___x_249_ = 1;
if (v_isShared_246_ == 0)
{
v___x_251_ = v___x_245_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_gate_242_);
v___x_251_ = v_reuseFailAlloc_255_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_253_; 
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*1, v___x_249_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_251_);
lean_ctor_set(v___x_235_, 0, v___y_248_);
v___x_253_ = v___x_235_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___y_248_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
v___y_207_ = v___x_253_;
goto v___jp_206_;
}
}
}
else
{
uint8_t v___x_256_; lean_object* v___x_258_; 
v___x_256_ = 0;
if (v_isShared_246_ == 0)
{
v___x_258_ = v___x_245_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_gate_242_);
v___x_258_ = v_reuseFailAlloc_262_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_260_; 
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_256_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_258_);
lean_ctor_set(v___x_235_, 0, v___y_248_);
v___x_260_ = v___x_235_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___y_248_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
v___y_207_ = v___x_260_;
goto v___jp_206_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object* v_00_u03b1_274_, lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_aig_277_, lean_object* v_input_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_275_, v_inst_276_, v_aig_277_, v_input_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___redArg(lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_aig_282_, lean_object* v_input_283_){
_start:
{
lean_object* v___y_285_; lean_object* v___y_286_; lean_object* v___y_287_; lean_object* v___y_291_; lean_object* v___y_292_; lean_object* v___y_293_; lean_object* v___y_314_; lean_object* v___y_315_; lean_object* v___y_316_; uint8_t v___y_317_; lean_object* v___y_318_; lean_object* v_lhs_345_; lean_object* v_rhs_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_390_; 
v_lhs_345_ = lean_ctor_get(v_input_283_, 0);
v_rhs_346_ = lean_ctor_get(v_input_283_, 1);
v_isSharedCheck_390_ = !lean_is_exclusive(v_input_283_);
if (v_isSharedCheck_390_ == 0)
{
v___x_348_ = v_input_283_;
v_isShared_349_ = v_isSharedCheck_390_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_rhs_346_);
lean_inc(v_lhs_345_);
lean_dec(v_input_283_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_390_;
goto v_resetjp_347_;
}
v___jp_284_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_288_, 0, v___y_286_);
lean_ctor_set(v___x_288_, 1, v___y_287_);
v___x_289_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_280_, v_inst_281_, v___y_285_, v___x_288_);
return v___x_289_;
}
v___jp_290_:
{
uint8_t v_invert_294_; 
v_invert_294_ = lean_ctor_get_uint8(v___y_291_, sizeof(void*)*1);
if (v_invert_294_ == 0)
{
lean_object* v_gate_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v_gate_295_ = lean_ctor_get(v___y_291_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___y_291_);
if (v_isSharedCheck_303_ == 0)
{
v___x_297_ = v___y_291_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_gate_295_);
lean_dec(v___y_291_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
uint8_t v___x_299_; lean_object* v___x_301_; 
v___x_299_ = 1;
if (v_isShared_298_ == 0)
{
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v_gate_295_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*1, v___x_299_);
v___y_285_ = v___y_292_;
v___y_286_ = v___y_293_;
v___y_287_ = v___x_301_;
goto v___jp_284_;
}
}
}
else
{
lean_object* v_gate_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_312_; 
v_gate_304_ = lean_ctor_get(v___y_291_, 0);
v_isSharedCheck_312_ = !lean_is_exclusive(v___y_291_);
if (v_isSharedCheck_312_ == 0)
{
v___x_306_ = v___y_291_;
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_gate_304_);
lean_dec(v___y_291_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_312_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
uint8_t v___x_308_; lean_object* v___x_310_; 
v___x_308_ = 0;
if (v_isShared_307_ == 0)
{
v___x_310_ = v___x_306_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v_gate_304_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*1, v___x_308_);
v___y_285_ = v___y_292_;
v___y_286_ = v___y_293_;
v___y_287_ = v___x_310_;
goto v___jp_284_;
}
}
}
}
v___jp_313_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_res_321_; uint8_t v_invert_322_; 
v___x_319_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_319_, 0, v___y_314_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*1, v___y_317_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___y_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
lean_inc_ref(v_inst_281_);
lean_inc_ref(v_inst_280_);
v_res_321_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_280_, v_inst_281_, v___y_315_, v___x_320_);
v_invert_322_ = lean_ctor_get_uint8(v___y_316_, sizeof(void*)*1);
if (v_invert_322_ == 0)
{
lean_object* v_aig_323_; lean_object* v_ref_324_; lean_object* v_gate_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_333_; 
v_aig_323_ = lean_ctor_get(v_res_321_, 0);
lean_inc_ref(v_aig_323_);
v_ref_324_ = lean_ctor_get(v_res_321_, 1);
lean_inc_ref(v_ref_324_);
lean_dec_ref(v_res_321_);
v_gate_325_ = lean_ctor_get(v___y_316_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___y_316_);
if (v_isSharedCheck_333_ == 0)
{
v___x_327_ = v___y_316_;
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_gate_325_);
lean_dec(v___y_316_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_333_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
uint8_t v___x_329_; lean_object* v___x_331_; 
v___x_329_ = 1;
if (v_isShared_328_ == 0)
{
v___x_331_ = v___x_327_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_gate_325_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_ctor_set_uint8(v___x_331_, sizeof(void*)*1, v___x_329_);
v___y_291_ = v_ref_324_;
v___y_292_ = v_aig_323_;
v___y_293_ = v___x_331_;
goto v___jp_290_;
}
}
}
else
{
lean_object* v_aig_334_; lean_object* v_ref_335_; lean_object* v_gate_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_344_; 
v_aig_334_ = lean_ctor_get(v_res_321_, 0);
lean_inc_ref(v_aig_334_);
v_ref_335_ = lean_ctor_get(v_res_321_, 1);
lean_inc_ref(v_ref_335_);
lean_dec_ref(v_res_321_);
v_gate_336_ = lean_ctor_get(v___y_316_, 0);
v_isSharedCheck_344_ = !lean_is_exclusive(v___y_316_);
if (v_isSharedCheck_344_ == 0)
{
v___x_338_ = v___y_316_;
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_gate_336_);
lean_dec(v___y_316_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
uint8_t v___x_340_; lean_object* v___x_342_; 
v___x_340_ = 0;
if (v_isShared_339_ == 0)
{
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_gate_336_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_ctor_set_uint8(v___x_342_, sizeof(void*)*1, v___x_340_);
v___y_291_ = v_ref_335_;
v___y_292_ = v_aig_334_;
v___y_293_ = v___x_342_;
goto v___jp_290_;
}
}
}
}
v_resetjp_347_:
{
lean_object* v_gate_350_; uint8_t v_invert_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_389_; 
v_gate_350_ = lean_ctor_get(v_lhs_345_, 0);
v_invert_351_ = lean_ctor_get_uint8(v_lhs_345_, sizeof(void*)*1);
v_isSharedCheck_389_ = !lean_is_exclusive(v_lhs_345_);
if (v_isSharedCheck_389_ == 0)
{
v___x_353_ = v_lhs_345_;
v_isShared_354_ = v_isSharedCheck_389_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_gate_350_);
lean_dec(v_lhs_345_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_389_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_gate_355_; uint8_t v_invert_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_388_; 
v_gate_355_ = lean_ctor_get(v_rhs_346_, 0);
v_invert_356_ = lean_ctor_get_uint8(v_rhs_346_, sizeof(void*)*1);
v_isSharedCheck_388_ = !lean_is_exclusive(v_rhs_346_);
if (v_isSharedCheck_388_ == 0)
{
v___x_358_ = v_rhs_346_;
v_isShared_359_ = v_isSharedCheck_388_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_gate_355_);
lean_dec(v_rhs_346_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_388_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___y_361_; lean_object* v___x_376_; 
lean_inc(v_gate_350_);
if (v_isShared_354_ == 0)
{
v___x_376_ = v___x_353_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_gate_350_);
lean_ctor_set_uint8(v_reuseFailAlloc_387_, sizeof(void*)*1, v_invert_351_);
v___x_376_ = v_reuseFailAlloc_387_;
goto v_reusejp_375_;
}
v___jp_360_:
{
lean_object* v_res_362_; 
lean_inc_ref(v_inst_281_);
lean_inc_ref(v_inst_280_);
v_res_362_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_280_, v_inst_281_, v_aig_282_, v___y_361_);
if (v_invert_351_ == 0)
{
lean_object* v_aig_363_; lean_object* v_ref_364_; uint8_t v___x_365_; lean_object* v___x_367_; 
v_aig_363_ = lean_ctor_get(v_res_362_, 0);
lean_inc_ref(v_aig_363_);
v_ref_364_ = lean_ctor_get(v_res_362_, 1);
lean_inc_ref(v_ref_364_);
lean_dec_ref(v_res_362_);
v___x_365_ = 1;
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v_gate_350_);
v___x_367_ = v___x_358_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_gate_350_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
lean_ctor_set_uint8(v___x_367_, sizeof(void*)*1, v___x_365_);
v___y_314_ = v_gate_355_;
v___y_315_ = v_aig_363_;
v___y_316_ = v_ref_364_;
v___y_317_ = v_invert_356_;
v___y_318_ = v___x_367_;
goto v___jp_313_;
}
}
else
{
lean_object* v_aig_369_; lean_object* v_ref_370_; uint8_t v___x_371_; lean_object* v___x_373_; 
v_aig_369_ = lean_ctor_get(v_res_362_, 0);
lean_inc_ref(v_aig_369_);
v_ref_370_ = lean_ctor_get(v_res_362_, 1);
lean_inc_ref(v_ref_370_);
lean_dec_ref(v_res_362_);
v___x_371_ = 0;
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v_gate_350_);
v___x_373_ = v___x_358_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_gate_350_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_ctor_set_uint8(v___x_373_, sizeof(void*)*1, v___x_371_);
v___y_314_ = v_gate_355_;
v___y_315_ = v_aig_369_;
v___y_316_ = v_ref_370_;
v___y_317_ = v_invert_356_;
v___y_318_ = v___x_373_;
goto v___jp_313_;
}
}
}
v_reusejp_375_:
{
if (v_invert_356_ == 0)
{
uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_377_ = 1;
lean_inc(v_gate_355_);
v___x_378_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_378_, 0, v_gate_355_);
lean_ctor_set_uint8(v___x_378_, sizeof(void*)*1, v___x_377_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_378_);
lean_ctor_set(v___x_348_, 0, v___x_376_);
v___x_380_ = v___x_348_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
v___y_361_ = v___x_380_;
goto v___jp_360_;
}
}
else
{
uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_382_ = 0;
lean_inc(v_gate_355_);
v___x_383_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_383_, 0, v_gate_355_);
lean_ctor_set_uint8(v___x_383_, sizeof(void*)*1, v___x_382_);
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_383_);
lean_ctor_set(v___x_348_, 0, v___x_376_);
v___x_385_ = v___x_348_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_376_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
v___y_361_ = v___x_385_;
goto v___jp_360_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object* v_00_u03b1_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_aig_394_, lean_object* v_input_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Std_Sat_AIG_mkBEqCached___redArg(v_inst_392_, v_inst_393_, v_aig_394_, v_input_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___redArg(lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_aig_399_, lean_object* v_input_400_){
_start:
{
lean_object* v___y_402_; lean_object* v_lhs_442_; lean_object* v_rhs_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_476_; 
v_lhs_442_ = lean_ctor_get(v_input_400_, 0);
v_rhs_443_ = lean_ctor_get(v_input_400_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_input_400_);
if (v_isSharedCheck_476_ == 0)
{
v___x_445_ = v_input_400_;
v_isShared_446_ = v_isSharedCheck_476_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_rhs_443_);
lean_inc(v_lhs_442_);
lean_dec(v_input_400_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_476_;
goto v_resetjp_444_;
}
v___jp_401_:
{
lean_object* v_res_403_; lean_object* v_ref_404_; uint8_t v_invert_405_; 
v_res_403_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_397_, v_inst_398_, v_aig_399_, v___y_402_);
v_ref_404_ = lean_ctor_get(v_res_403_, 1);
lean_inc_ref(v_ref_404_);
v_invert_405_ = lean_ctor_get_uint8(v_ref_404_, sizeof(void*)*1);
if (v_invert_405_ == 0)
{
lean_object* v_aig_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_422_; 
v_aig_406_ = lean_ctor_get(v_res_403_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_res_403_);
if (v_isSharedCheck_422_ == 0)
{
lean_object* v_unused_423_; 
v_unused_423_ = lean_ctor_get(v_res_403_, 1);
lean_dec(v_unused_423_);
v___x_408_ = v_res_403_;
v_isShared_409_ = v_isSharedCheck_422_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_aig_406_);
lean_dec(v_res_403_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_422_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_gate_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_421_; 
v_gate_410_ = lean_ctor_get(v_ref_404_, 0);
v_isSharedCheck_421_ = !lean_is_exclusive(v_ref_404_);
if (v_isSharedCheck_421_ == 0)
{
v___x_412_ = v_ref_404_;
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_gate_410_);
lean_dec(v_ref_404_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_421_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
uint8_t v___x_414_; lean_object* v___x_416_; 
v___x_414_ = 1;
if (v_isShared_413_ == 0)
{
v___x_416_ = v___x_412_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_gate_410_);
v___x_416_ = v_reuseFailAlloc_420_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_418_; 
lean_ctor_set_uint8(v___x_416_, sizeof(void*)*1, v___x_414_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_416_);
v___x_418_ = v___x_408_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_aig_406_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
else
{
lean_object* v_aig_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_440_; 
v_aig_424_ = lean_ctor_get(v_res_403_, 0);
v_isSharedCheck_440_ = !lean_is_exclusive(v_res_403_);
if (v_isSharedCheck_440_ == 0)
{
lean_object* v_unused_441_; 
v_unused_441_ = lean_ctor_get(v_res_403_, 1);
lean_dec(v_unused_441_);
v___x_426_ = v_res_403_;
v_isShared_427_ = v_isSharedCheck_440_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_aig_424_);
lean_dec(v_res_403_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_440_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_gate_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_439_; 
v_gate_428_ = lean_ctor_get(v_ref_404_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v_ref_404_);
if (v_isSharedCheck_439_ == 0)
{
v___x_430_ = v_ref_404_;
v_isShared_431_ = v_isSharedCheck_439_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_gate_428_);
lean_dec(v_ref_404_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_439_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
uint8_t v___x_432_; lean_object* v___x_434_; 
v___x_432_ = 0;
if (v_isShared_431_ == 0)
{
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_gate_428_);
v___x_434_ = v_reuseFailAlloc_438_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
lean_ctor_set_uint8(v___x_434_, sizeof(void*)*1, v___x_432_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_434_);
v___x_436_ = v___x_426_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_aig_424_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v___x_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
}
}
v_resetjp_444_:
{
lean_object* v_gate_447_; uint8_t v_invert_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_475_; 
v_gate_447_ = lean_ctor_get(v_lhs_442_, 0);
v_invert_448_ = lean_ctor_get_uint8(v_lhs_442_, sizeof(void*)*1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_lhs_442_);
if (v_isSharedCheck_475_ == 0)
{
v___x_450_ = v_lhs_442_;
v_isShared_451_ = v_isSharedCheck_475_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_gate_447_);
lean_dec(v_lhs_442_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_475_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_gate_452_; uint8_t v_invert_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_474_; 
v_gate_452_ = lean_ctor_get(v_rhs_443_, 0);
v_invert_453_ = lean_ctor_get_uint8(v_rhs_443_, sizeof(void*)*1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_rhs_443_);
if (v_isSharedCheck_474_ == 0)
{
v___x_455_ = v_rhs_443_;
v_isShared_456_ = v_isSharedCheck_474_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_gate_452_);
lean_dec(v_rhs_443_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_474_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 0, v_gate_447_);
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_gate_447_);
v___x_458_ = v_reuseFailAlloc_473_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_ctor_set_uint8(v___x_458_, sizeof(void*)*1, v_invert_448_);
if (v_invert_453_ == 0)
{
uint8_t v___x_459_; lean_object* v___x_461_; 
v___x_459_ = 1;
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v_gate_452_);
v___x_461_ = v___x_450_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_gate_452_);
v___x_461_ = v_reuseFailAlloc_465_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
lean_object* v___x_463_; 
lean_ctor_set_uint8(v___x_461_, sizeof(void*)*1, v___x_459_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_461_);
lean_ctor_set(v___x_445_, 0, v___x_458_);
v___x_463_ = v___x_445_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_464_; 
v_reuseFailAlloc_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_464_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_464_, 1, v___x_461_);
v___x_463_ = v_reuseFailAlloc_464_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
v___y_402_ = v___x_463_;
goto v___jp_401_;
}
}
}
else
{
uint8_t v___x_466_; lean_object* v___x_468_; 
v___x_466_ = 0;
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v_gate_452_);
v___x_468_ = v___x_450_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_gate_452_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*1, v___x_466_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v___x_468_);
lean_ctor_set(v___x_445_, 0, v___x_458_);
v___x_470_ = v___x_445_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
v___y_402_ = v___x_470_;
goto v___jp_401_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object* v_00_u03b1_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_aig_480_, lean_object* v_input_481_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Std_Sat_AIG_mkImpCached___redArg(v_inst_478_, v_inst_479_, v_aig_480_, v_input_481_);
return v___x_482_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_CachedGates(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Sat_AIG_CachedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Sat_AIG_CachedGates(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_AIG_CachedGates(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CachedLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_CachedGates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Sat_AIG_CachedGates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Sat_AIG_CachedGates(builtin);
}
#ifdef __cplusplus
}
#endif
