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
lean_object* v___y_72_; lean_object* v_lhs_112_; lean_object* v_rhs_113_; lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_157_; 
v_lhs_112_ = lean_ctor_get(v_input_70_, 0);
v_rhs_113_ = lean_ctor_get(v_input_70_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_input_70_);
if (v_isSharedCheck_157_ == 0)
{
v___x_115_ = v_input_70_;
v_isShared_116_ = v_isSharedCheck_157_;
goto v_resetjp_114_;
}
else
{
lean_inc(v_rhs_113_);
lean_inc(v_lhs_112_);
lean_dec(v_input_70_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_157_;
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
lean_object* v_gate_117_; uint8_t v_invert_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_156_; 
v_gate_117_ = lean_ctor_get(v_lhs_112_, 0);
v_invert_118_ = lean_ctor_get_uint8(v_lhs_112_, sizeof(void*)*1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_lhs_112_);
if (v_isSharedCheck_156_ == 0)
{
v___x_120_ = v_lhs_112_;
v_isShared_121_ = v_isSharedCheck_156_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_gate_117_);
lean_dec(v_lhs_112_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_156_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
uint8_t v___x_122_; lean_object* v___y_124_; 
v___x_122_ = 1;
if (v_invert_118_ == 0)
{
lean_object* v___x_150_; 
if (v_isShared_121_ == 0)
{
v___x_150_ = v___x_120_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_gate_117_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*1, v___x_122_);
v___y_124_ = v___x_150_;
goto v___jp_123_;
}
}
else
{
uint8_t v___x_152_; lean_object* v___x_154_; 
v___x_152_ = 0;
if (v_isShared_121_ == 0)
{
v___x_154_ = v___x_120_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_gate_117_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_152_);
v___y_124_ = v___x_154_;
goto v___jp_123_;
}
}
v___jp_123_:
{
uint8_t v_invert_125_; 
v_invert_125_ = lean_ctor_get_uint8(v_rhs_113_, sizeof(void*)*1);
if (v_invert_125_ == 0)
{
lean_object* v_gate_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_136_; 
v_gate_126_ = lean_ctor_get(v_rhs_113_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_rhs_113_);
if (v_isSharedCheck_136_ == 0)
{
v___x_128_ = v_rhs_113_;
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_gate_126_);
lean_dec(v_rhs_113_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_gate_126_);
v___x_131_ = v_reuseFailAlloc_135_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_133_; 
lean_ctor_set_uint8(v___x_131_, sizeof(void*)*1, v___x_122_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_131_);
lean_ctor_set(v___x_115_, 0, v___y_124_);
v___x_133_ = v___x_115_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v___y_124_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_134_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
v___y_72_ = v___x_133_;
goto v___jp_71_;
}
}
}
}
else
{
lean_object* v_gate_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_148_; 
v_gate_137_ = lean_ctor_get(v_rhs_113_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v_rhs_113_);
if (v_isSharedCheck_148_ == 0)
{
v___x_139_ = v_rhs_113_;
v_isShared_140_ = v_isSharedCheck_148_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_gate_137_);
lean_dec(v_rhs_113_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_148_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
uint8_t v___x_141_; lean_object* v___x_143_; 
v___x_141_ = 0;
if (v_isShared_140_ == 0)
{
v___x_143_ = v___x_139_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_gate_137_);
v___x_143_ = v_reuseFailAlloc_147_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_145_; 
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*1, v___x_141_);
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 1, v___x_143_);
lean_ctor_set(v___x_115_, 0, v___y_124_);
v___x_145_ = v___x_115_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___y_124_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_143_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
v___y_72_ = v___x_145_;
goto v___jp_71_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkOrCached(lean_object* v_00_u03b1_158_, lean_object* v_inst_159_, lean_object* v_inst_160_, lean_object* v_aig_161_, lean_object* v_input_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_Sat_AIG_mkOrCached___redArg(v_inst_159_, v_inst_160_, v_aig_161_, v_input_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_aig_166_, lean_object* v_input_167_){
_start:
{
lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; lean_object* v___y_175_; lean_object* v___y_176_; lean_object* v___y_177_; lean_object* v_res_197_; lean_object* v_aig_198_; lean_object* v_ref_199_; lean_object* v___y_201_; lean_object* v_lhs_226_; lean_object* v_rhs_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_266_; 
lean_inc_ref(v_input_167_);
lean_inc_ref(v_inst_165_);
lean_inc_ref(v_inst_164_);
v_res_197_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_164_, v_inst_165_, v_aig_166_, v_input_167_);
v_aig_198_ = lean_ctor_get(v_res_197_, 0);
lean_inc_ref(v_aig_198_);
v_ref_199_ = lean_ctor_get(v_res_197_, 1);
lean_inc_ref(v_ref_199_);
lean_dec_ref(v_res_197_);
v_lhs_226_ = lean_ctor_get(v_input_167_, 0);
v_rhs_227_ = lean_ctor_get(v_input_167_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_input_167_);
if (v_isSharedCheck_266_ == 0)
{
v___x_229_ = v_input_167_;
v_isShared_230_ = v_isSharedCheck_266_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_rhs_227_);
lean_inc(v_lhs_226_);
lean_dec(v_input_167_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_266_;
goto v_resetjp_228_;
}
v___jp_168_:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v___y_169_);
lean_ctor_set(v___x_172_, 1, v___y_171_);
v___x_173_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_164_, v_inst_165_, v___y_170_, v___x_172_);
return v___x_173_;
}
v___jp_174_:
{
uint8_t v_invert_178_; 
v_invert_178_ = lean_ctor_get_uint8(v___y_176_, sizeof(void*)*1);
if (v_invert_178_ == 0)
{
lean_object* v_gate_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_187_; 
v_gate_179_ = lean_ctor_get(v___y_176_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___y_176_);
if (v_isSharedCheck_187_ == 0)
{
v___x_181_ = v___y_176_;
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_gate_179_);
lean_dec(v___y_176_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_187_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
uint8_t v___x_183_; lean_object* v___x_185_; 
v___x_183_ = 1;
if (v_isShared_182_ == 0)
{
v___x_185_ = v___x_181_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_gate_179_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
lean_ctor_set_uint8(v___x_185_, sizeof(void*)*1, v___x_183_);
v___y_169_ = v___y_177_;
v___y_170_ = v___y_175_;
v___y_171_ = v___x_185_;
goto v___jp_168_;
}
}
}
else
{
lean_object* v_gate_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_196_; 
v_gate_188_ = lean_ctor_get(v___y_176_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___y_176_);
if (v_isSharedCheck_196_ == 0)
{
v___x_190_ = v___y_176_;
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_gate_188_);
lean_dec(v___y_176_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_196_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
uint8_t v___x_192_; lean_object* v___x_194_; 
v___x_192_ = 0;
if (v_isShared_191_ == 0)
{
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_gate_188_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*1, v___x_192_);
v___y_169_ = v___y_177_;
v___y_170_ = v___y_175_;
v___y_171_ = v___x_194_;
goto v___jp_168_;
}
}
}
}
v___jp_200_:
{
lean_object* v_res_202_; uint8_t v_invert_203_; 
lean_inc_ref(v_inst_165_);
lean_inc_ref(v_inst_164_);
v_res_202_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_164_, v_inst_165_, v_aig_198_, v___y_201_);
v_invert_203_ = lean_ctor_get_uint8(v_ref_199_, sizeof(void*)*1);
if (v_invert_203_ == 0)
{
lean_object* v_aig_204_; lean_object* v_ref_205_; lean_object* v_gate_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_214_; 
v_aig_204_ = lean_ctor_get(v_res_202_, 0);
lean_inc_ref(v_aig_204_);
v_ref_205_ = lean_ctor_get(v_res_202_, 1);
lean_inc_ref(v_ref_205_);
lean_dec_ref(v_res_202_);
v_gate_206_ = lean_ctor_get(v_ref_199_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v_ref_199_);
if (v_isSharedCheck_214_ == 0)
{
v___x_208_ = v_ref_199_;
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_gate_206_);
lean_dec(v_ref_199_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_214_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
uint8_t v___x_210_; lean_object* v___x_212_; 
v___x_210_ = 1;
if (v_isShared_209_ == 0)
{
v___x_212_ = v___x_208_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_gate_206_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
lean_ctor_set_uint8(v___x_212_, sizeof(void*)*1, v___x_210_);
v___y_175_ = v_aig_204_;
v___y_176_ = v_ref_205_;
v___y_177_ = v___x_212_;
goto v___jp_174_;
}
}
}
else
{
lean_object* v_aig_215_; lean_object* v_ref_216_; lean_object* v_gate_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_225_; 
v_aig_215_ = lean_ctor_get(v_res_202_, 0);
lean_inc_ref(v_aig_215_);
v_ref_216_ = lean_ctor_get(v_res_202_, 1);
lean_inc_ref(v_ref_216_);
lean_dec_ref(v_res_202_);
v_gate_217_ = lean_ctor_get(v_ref_199_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_ref_199_);
if (v_isSharedCheck_225_ == 0)
{
v___x_219_ = v_ref_199_;
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_gate_217_);
lean_dec(v_ref_199_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_225_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
uint8_t v___x_221_; lean_object* v___x_223_; 
v___x_221_ = 0;
if (v_isShared_220_ == 0)
{
v___x_223_ = v___x_219_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_gate_217_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
lean_ctor_set_uint8(v___x_223_, sizeof(void*)*1, v___x_221_);
v___y_175_ = v_aig_215_;
v___y_176_ = v_ref_216_;
v___y_177_ = v___x_223_;
goto v___jp_174_;
}
}
}
}
v_resetjp_228_:
{
lean_object* v_gate_231_; uint8_t v_invert_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_265_; 
v_gate_231_ = lean_ctor_get(v_lhs_226_, 0);
v_invert_232_ = lean_ctor_get_uint8(v_lhs_226_, sizeof(void*)*1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_lhs_226_);
if (v_isSharedCheck_265_ == 0)
{
v___x_234_ = v_lhs_226_;
v_isShared_235_ = v_isSharedCheck_265_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_gate_231_);
lean_dec(v_lhs_226_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_265_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v_gate_236_; uint8_t v_invert_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_264_; 
v_gate_236_ = lean_ctor_get(v_rhs_227_, 0);
v_invert_237_ = lean_ctor_get_uint8(v_rhs_227_, sizeof(void*)*1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_rhs_227_);
if (v_isSharedCheck_264_ == 0)
{
v___x_239_ = v_rhs_227_;
v_isShared_240_ = v_isSharedCheck_264_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_gate_236_);
lean_dec(v_rhs_227_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_264_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
uint8_t v___x_241_; lean_object* v___y_243_; 
v___x_241_ = 1;
if (v_invert_232_ == 0)
{
lean_object* v___x_258_; 
if (v_isShared_235_ == 0)
{
v___x_258_ = v___x_234_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_gate_231_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_241_);
v___y_243_ = v___x_258_;
goto v___jp_242_;
}
}
else
{
uint8_t v___x_260_; lean_object* v___x_262_; 
v___x_260_ = 0;
if (v_isShared_235_ == 0)
{
v___x_262_ = v___x_234_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_gate_231_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_ctor_set_uint8(v___x_262_, sizeof(void*)*1, v___x_260_);
v___y_243_ = v___x_262_;
goto v___jp_242_;
}
}
v___jp_242_:
{
if (v_invert_237_ == 0)
{
lean_object* v___x_245_; 
if (v_isShared_240_ == 0)
{
v___x_245_ = v___x_239_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v_gate_236_);
v___x_245_ = v_reuseFailAlloc_249_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_247_; 
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_241_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_245_);
lean_ctor_set(v___x_229_, 0, v___y_243_);
v___x_247_ = v___x_229_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___y_243_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
v___y_201_ = v___x_247_;
goto v___jp_200_;
}
}
}
else
{
uint8_t v___x_250_; lean_object* v___x_252_; 
v___x_250_ = 0;
if (v_isShared_240_ == 0)
{
v___x_252_ = v___x_239_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_gate_236_);
v___x_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
lean_ctor_set_uint8(v___x_252_, sizeof(void*)*1, v___x_250_);
if (v_isShared_230_ == 0)
{
lean_ctor_set(v___x_229_, 1, v___x_252_);
lean_ctor_set(v___x_229_, 0, v___y_243_);
v___x_254_ = v___x_229_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___y_243_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
v___y_201_ = v___x_254_;
goto v___jp_200_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkXorCached(lean_object* v_00_u03b1_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_aig_270_, lean_object* v_input_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_Sat_AIG_mkXorCached___redArg(v_inst_268_, v_inst_269_, v_aig_270_, v_input_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached___redArg(lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_aig_275_, lean_object* v_input_276_){
_start:
{
lean_object* v___y_278_; lean_object* v___y_279_; lean_object* v___y_280_; lean_object* v_lhs_283_; lean_object* v_rhs_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_397_; 
v_lhs_283_ = lean_ctor_get(v_input_276_, 0);
v_rhs_284_ = lean_ctor_get(v_input_276_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_input_276_);
if (v_isSharedCheck_397_ == 0)
{
v___x_286_ = v_input_276_;
v_isShared_287_ = v_isSharedCheck_397_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_rhs_284_);
lean_inc(v_lhs_283_);
lean_dec(v_input_276_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_397_;
goto v_resetjp_285_;
}
v___jp_277_:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v___y_279_);
lean_ctor_set(v___x_281_, 1, v___y_280_);
v___x_282_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_273_, v_inst_274_, v___y_278_, v___x_281_);
return v___x_282_;
}
v_resetjp_285_:
{
lean_object* v_gate_288_; uint8_t v_invert_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_396_; 
v_gate_288_ = lean_ctor_get(v_lhs_283_, 0);
v_invert_289_ = lean_ctor_get_uint8(v_lhs_283_, sizeof(void*)*1);
v_isSharedCheck_396_ = !lean_is_exclusive(v_lhs_283_);
if (v_isSharedCheck_396_ == 0)
{
v___x_291_ = v_lhs_283_;
v_isShared_292_ = v_isSharedCheck_396_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_gate_288_);
lean_dec(v_lhs_283_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_396_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
uint8_t v___x_293_; uint8_t v___x_294_; lean_object* v___y_296_; lean_object* v___y_297_; lean_object* v___y_298_; lean_object* v___y_317_; lean_object* v___y_318_; lean_object* v___y_319_; uint8_t v___y_343_; lean_object* v___y_344_; lean_object* v___y_345_; lean_object* v___y_346_; lean_object* v___y_347_; lean_object* v___y_361_; lean_object* v___y_386_; 
v___x_293_ = 0;
v___x_294_ = 1;
if (v_invert_289_ == 0)
{
lean_object* v___x_394_; 
lean_inc(v_gate_288_);
v___x_394_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_394_, 0, v_gate_288_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*1, v___x_293_);
v___y_386_ = v___x_394_;
goto v___jp_385_;
}
else
{
lean_object* v___x_395_; 
lean_inc(v_gate_288_);
v___x_395_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_395_, 0, v_gate_288_);
lean_ctor_set_uint8(v___x_395_, sizeof(void*)*1, v___x_294_);
v___y_386_ = v___x_395_;
goto v___jp_385_;
}
v___jp_295_:
{
uint8_t v_invert_299_; 
v_invert_299_ = lean_ctor_get_uint8(v___y_297_, sizeof(void*)*1);
if (v_invert_299_ == 0)
{
lean_object* v_gate_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_gate_300_ = lean_ctor_get(v___y_297_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___y_297_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___y_297_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_gate_300_);
lean_dec(v___y_297_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_gate_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
lean_ctor_set_uint8(v___x_305_, sizeof(void*)*1, v___x_294_);
v___y_278_ = v___y_296_;
v___y_279_ = v___y_298_;
v___y_280_ = v___x_305_;
goto v___jp_277_;
}
}
}
else
{
lean_object* v_gate_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_gate_308_ = lean_ctor_get(v___y_297_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v___y_297_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v___y_297_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_gate_308_);
lean_dec(v___y_297_);
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
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_gate_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_ctor_set_uint8(v___x_313_, sizeof(void*)*1, v___x_293_);
v___y_278_ = v___y_296_;
v___y_279_ = v___y_298_;
v___y_280_ = v___x_313_;
goto v___jp_277_;
}
}
}
}
v___jp_316_:
{
lean_object* v_res_320_; uint8_t v_invert_321_; 
lean_inc_ref(v_inst_274_);
lean_inc_ref(v_inst_273_);
v_res_320_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_273_, v_inst_274_, v___y_318_, v___y_319_);
v_invert_321_ = lean_ctor_get_uint8(v___y_317_, sizeof(void*)*1);
if (v_invert_321_ == 0)
{
lean_object* v_aig_322_; lean_object* v_ref_323_; lean_object* v_gate_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_331_; 
v_aig_322_ = lean_ctor_get(v_res_320_, 0);
lean_inc_ref(v_aig_322_);
v_ref_323_ = lean_ctor_get(v_res_320_, 1);
lean_inc_ref(v_ref_323_);
lean_dec_ref(v_res_320_);
v_gate_324_ = lean_ctor_get(v___y_317_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___y_317_);
if (v_isSharedCheck_331_ == 0)
{
v___x_326_ = v___y_317_;
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_gate_324_);
lean_dec(v___y_317_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_331_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_329_; 
if (v_isShared_327_ == 0)
{
v___x_329_ = v___x_326_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_gate_324_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_ctor_set_uint8(v___x_329_, sizeof(void*)*1, v___x_294_);
v___y_296_ = v_aig_322_;
v___y_297_ = v_ref_323_;
v___y_298_ = v___x_329_;
goto v___jp_295_;
}
}
}
else
{
lean_object* v_aig_332_; lean_object* v_ref_333_; lean_object* v_gate_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_341_; 
v_aig_332_ = lean_ctor_get(v_res_320_, 0);
lean_inc_ref(v_aig_332_);
v_ref_333_ = lean_ctor_get(v_res_320_, 1);
lean_inc_ref(v_ref_333_);
lean_dec_ref(v_res_320_);
v_gate_334_ = lean_ctor_get(v___y_317_, 0);
v_isSharedCheck_341_ = !lean_is_exclusive(v___y_317_);
if (v_isSharedCheck_341_ == 0)
{
v___x_336_ = v___y_317_;
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_gate_334_);
lean_dec(v___y_317_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_341_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v___x_339_; 
if (v_isShared_337_ == 0)
{
v___x_339_ = v___x_336_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_gate_334_);
v___x_339_ = v_reuseFailAlloc_340_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*1, v___x_293_);
v___y_296_ = v_aig_332_;
v___y_297_ = v_ref_333_;
v___y_298_ = v___x_339_;
goto v___jp_295_;
}
}
}
}
v___jp_342_:
{
if (v___y_343_ == 0)
{
lean_object* v___x_349_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___y_345_);
v___x_349_ = v___x_291_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v___y_345_);
v___x_349_ = v_reuseFailAlloc_353_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_351_; 
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*1, v___x_293_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v___x_349_);
lean_ctor_set(v___x_286_, 0, v___y_347_);
v___x_351_ = v___x_286_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___y_347_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_349_);
v___x_351_ = v_reuseFailAlloc_352_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
v___y_317_ = v___y_344_;
v___y_318_ = v___y_346_;
v___y_319_ = v___x_351_;
goto v___jp_316_;
}
}
}
else
{
lean_object* v___x_355_; 
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 0, v___y_345_);
v___x_355_ = v___x_291_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___y_345_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
lean_ctor_set_uint8(v___x_355_, sizeof(void*)*1, v___x_294_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 1, v___x_355_);
lean_ctor_set(v___x_286_, 0, v___y_347_);
v___x_357_ = v___x_286_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___y_347_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
v___y_317_ = v___y_344_;
v___y_318_ = v___y_346_;
v___y_319_ = v___x_357_;
goto v___jp_316_;
}
}
}
}
v___jp_360_:
{
lean_object* v_res_362_; 
lean_inc_ref(v_inst_274_);
lean_inc_ref(v_inst_273_);
v_res_362_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_273_, v_inst_274_, v_aig_275_, v___y_361_);
if (v_invert_289_ == 0)
{
lean_object* v_aig_363_; lean_object* v_ref_364_; lean_object* v_gate_365_; uint8_t v_invert_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_373_; 
v_aig_363_ = lean_ctor_get(v_res_362_, 0);
lean_inc_ref(v_aig_363_);
v_ref_364_ = lean_ctor_get(v_res_362_, 1);
lean_inc_ref(v_ref_364_);
lean_dec_ref(v_res_362_);
v_gate_365_ = lean_ctor_get(v_rhs_284_, 0);
v_invert_366_ = lean_ctor_get_uint8(v_rhs_284_, sizeof(void*)*1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_rhs_284_);
if (v_isSharedCheck_373_ == 0)
{
v___x_368_ = v_rhs_284_;
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_gate_365_);
lean_dec(v_rhs_284_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_373_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_371_; 
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v_gate_288_);
v___x_371_ = v___x_368_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_gate_288_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_294_);
v___y_343_ = v_invert_366_;
v___y_344_ = v_ref_364_;
v___y_345_ = v_gate_365_;
v___y_346_ = v_aig_363_;
v___y_347_ = v___x_371_;
goto v___jp_342_;
}
}
}
else
{
lean_object* v_aig_374_; lean_object* v_ref_375_; lean_object* v_gate_376_; uint8_t v_invert_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
v_aig_374_ = lean_ctor_get(v_res_362_, 0);
lean_inc_ref(v_aig_374_);
v_ref_375_ = lean_ctor_get(v_res_362_, 1);
lean_inc_ref(v_ref_375_);
lean_dec_ref(v_res_362_);
v_gate_376_ = lean_ctor_get(v_rhs_284_, 0);
v_invert_377_ = lean_ctor_get_uint8(v_rhs_284_, sizeof(void*)*1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_rhs_284_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v_rhs_284_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_gate_376_);
lean_dec(v_rhs_284_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_gate_288_);
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_gate_288_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
lean_ctor_set_uint8(v___x_382_, sizeof(void*)*1, v___x_293_);
v___y_343_ = v_invert_377_;
v___y_344_ = v_ref_375_;
v___y_345_ = v_gate_376_;
v___y_346_ = v_aig_374_;
v___y_347_ = v___x_382_;
goto v___jp_342_;
}
}
}
}
v___jp_385_:
{
uint8_t v_invert_387_; 
v_invert_387_ = lean_ctor_get_uint8(v_rhs_284_, sizeof(void*)*1);
if (v_invert_387_ == 0)
{
lean_object* v_gate_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_gate_388_ = lean_ctor_get(v_rhs_284_, 0);
lean_inc(v_gate_388_);
v___x_389_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_389_, 0, v_gate_388_);
lean_ctor_set_uint8(v___x_389_, sizeof(void*)*1, v___x_294_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___y_386_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___y_361_ = v___x_390_;
goto v___jp_360_;
}
else
{
lean_object* v_gate_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_gate_391_ = lean_ctor_get(v_rhs_284_, 0);
lean_inc(v_gate_391_);
v___x_392_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_392_, 0, v_gate_391_);
lean_ctor_set_uint8(v___x_392_, sizeof(void*)*1, v___x_293_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___y_386_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___y_361_ = v___x_393_;
goto v___jp_360_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkBEqCached(lean_object* v_00_u03b1_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_aig_401_, lean_object* v_input_402_){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Std_Sat_AIG_mkBEqCached___redArg(v_inst_399_, v_inst_400_, v_aig_401_, v_input_402_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached___redArg(lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_aig_406_, lean_object* v_input_407_){
_start:
{
lean_object* v___y_409_; lean_object* v_lhs_449_; lean_object* v_rhs_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_493_; 
v_lhs_449_ = lean_ctor_get(v_input_407_, 0);
v_rhs_450_ = lean_ctor_get(v_input_407_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_input_407_);
if (v_isSharedCheck_493_ == 0)
{
v___x_452_ = v_input_407_;
v_isShared_453_ = v_isSharedCheck_493_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_rhs_450_);
lean_inc(v_lhs_449_);
lean_dec(v_input_407_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_493_;
goto v_resetjp_451_;
}
v___jp_408_:
{
lean_object* v_res_410_; lean_object* v_ref_411_; uint8_t v_invert_412_; 
v_res_410_ = l_Std_Sat_AIG_mkGateCached___redArg(v_inst_404_, v_inst_405_, v_aig_406_, v___y_409_);
v_ref_411_ = lean_ctor_get(v_res_410_, 1);
lean_inc_ref(v_ref_411_);
v_invert_412_ = lean_ctor_get_uint8(v_ref_411_, sizeof(void*)*1);
if (v_invert_412_ == 0)
{
lean_object* v_aig_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_429_; 
v_aig_413_ = lean_ctor_get(v_res_410_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v_res_410_);
if (v_isSharedCheck_429_ == 0)
{
lean_object* v_unused_430_; 
v_unused_430_ = lean_ctor_get(v_res_410_, 1);
lean_dec(v_unused_430_);
v___x_415_ = v_res_410_;
v_isShared_416_ = v_isSharedCheck_429_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_aig_413_);
lean_dec(v_res_410_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_429_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v_gate_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_428_; 
v_gate_417_ = lean_ctor_get(v_ref_411_, 0);
v_isSharedCheck_428_ = !lean_is_exclusive(v_ref_411_);
if (v_isSharedCheck_428_ == 0)
{
v___x_419_ = v_ref_411_;
v_isShared_420_ = v_isSharedCheck_428_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_gate_417_);
lean_dec(v_ref_411_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_428_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
uint8_t v___x_421_; lean_object* v___x_423_; 
v___x_421_ = 1;
if (v_isShared_420_ == 0)
{
v___x_423_ = v___x_419_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_gate_417_);
v___x_423_ = v_reuseFailAlloc_427_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_425_; 
lean_ctor_set_uint8(v___x_423_, sizeof(void*)*1, v___x_421_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 1, v___x_423_);
v___x_425_ = v___x_415_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_aig_413_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v___x_423_);
v___x_425_ = v_reuseFailAlloc_426_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
return v___x_425_;
}
}
}
}
}
else
{
lean_object* v_aig_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_447_; 
v_aig_431_ = lean_ctor_get(v_res_410_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_res_410_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v_res_410_, 1);
lean_dec(v_unused_448_);
v___x_433_ = v_res_410_;
v_isShared_434_ = v_isSharedCheck_447_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_aig_431_);
lean_dec(v_res_410_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_447_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_gate_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_446_; 
v_gate_435_ = lean_ctor_get(v_ref_411_, 0);
v_isSharedCheck_446_ = !lean_is_exclusive(v_ref_411_);
if (v_isSharedCheck_446_ == 0)
{
v___x_437_ = v_ref_411_;
v_isShared_438_ = v_isSharedCheck_446_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_gate_435_);
lean_dec(v_ref_411_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_446_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
uint8_t v___x_439_; lean_object* v___x_441_; 
v___x_439_ = 0;
if (v_isShared_438_ == 0)
{
v___x_441_ = v___x_437_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_gate_435_);
v___x_441_ = v_reuseFailAlloc_445_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
lean_object* v___x_443_; 
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*1, v___x_439_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_441_);
v___x_443_ = v___x_433_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_aig_431_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
}
}
v_resetjp_451_:
{
lean_object* v_gate_454_; uint8_t v_invert_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_492_; 
v_gate_454_ = lean_ctor_get(v_lhs_449_, 0);
v_invert_455_ = lean_ctor_get_uint8(v_lhs_449_, sizeof(void*)*1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_lhs_449_);
if (v_isSharedCheck_492_ == 0)
{
v___x_457_ = v_lhs_449_;
v_isShared_458_ = v_isSharedCheck_492_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_gate_454_);
lean_dec(v_lhs_449_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_492_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
uint8_t v___x_459_; lean_object* v___y_461_; 
v___x_459_ = 1;
if (v_invert_455_ == 0)
{
lean_object* v___x_487_; 
if (v_isShared_458_ == 0)
{
v___x_487_ = v___x_457_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_gate_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_488_, sizeof(void*)*1, v_invert_455_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
v___y_461_ = v___x_487_;
goto v___jp_460_;
}
}
else
{
lean_object* v___x_490_; 
if (v_isShared_458_ == 0)
{
v___x_490_ = v___x_457_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_gate_454_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
lean_ctor_set_uint8(v___x_490_, sizeof(void*)*1, v___x_459_);
v___y_461_ = v___x_490_;
goto v___jp_460_;
}
}
v___jp_460_:
{
uint8_t v_invert_462_; 
v_invert_462_ = lean_ctor_get_uint8(v_rhs_450_, sizeof(void*)*1);
if (v_invert_462_ == 0)
{
lean_object* v_gate_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_473_; 
v_gate_463_ = lean_ctor_get(v_rhs_450_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v_rhs_450_);
if (v_isSharedCheck_473_ == 0)
{
v___x_465_ = v_rhs_450_;
v_isShared_466_ = v_isSharedCheck_473_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_gate_463_);
lean_dec(v_rhs_450_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_473_;
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
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_gate_463_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
lean_ctor_set_uint8(v___x_468_, sizeof(void*)*1, v___x_459_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_468_);
lean_ctor_set(v___x_452_, 0, v___y_461_);
v___x_470_ = v___x_452_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___y_461_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
v___y_409_ = v___x_470_;
goto v___jp_408_;
}
}
}
}
else
{
lean_object* v_gate_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_485_; 
v_gate_474_ = lean_ctor_get(v_rhs_450_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_rhs_450_);
if (v_isSharedCheck_485_ == 0)
{
v___x_476_ = v_rhs_450_;
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_gate_474_);
lean_dec(v_rhs_450_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_485_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
uint8_t v___x_478_; lean_object* v___x_480_; 
v___x_478_ = 0;
if (v_isShared_477_ == 0)
{
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_gate_474_);
v___x_480_ = v_reuseFailAlloc_484_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_482_; 
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*1, v___x_478_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_480_);
lean_ctor_set(v___x_452_, 0, v___y_461_);
v___x_482_ = v___x_452_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v___y_461_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
v___y_409_ = v___x_482_;
goto v___jp_408_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_AIG_mkImpCached(lean_object* v_00_u03b1_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_aig_497_, lean_object* v_input_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_Sat_AIG_mkImpCached___redArg(v_inst_495_, v_inst_496_, v_aig_497_, v_input_498_);
return v___x_499_;
}
}
lean_object* runtime_initialize_Std_Sat_AIG_CachedLemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Sat_AIG_CachedGates(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
